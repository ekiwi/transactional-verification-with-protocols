#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, time, threading, queue
from collections import defaultdict
from typing import Set, Optional
from itertools import chain

from pysmt.shortcuts import Not, Type, Symbol, FunctionType, BOOL, Function, Ite, BV, substitute, Implies, Equals, TRUE
from pysmt.smtlib.script import smtcmd, SmtLibCommand

from .utils import SmtExpr, disjunction, conjunction
from .module import Module
from .spec import VerificationProblem, Transaction
from .spec_check import check_verification_problem
from .proto import to_verification_graph
from .verifier import get_inactive_reset, make_symbols

class InteractiveVerifier:
	def __init__(self, mod: Module, prob: VerificationProblem):
		check_verification_problem(prob, mod)
		self.prob = prob
		self.mod = mod
		self.verbose = True

	def verify_inductive_base_case(self):
		""" prove that the invariances hold after reset """
		print("WARN: TODO: prove inductive base case!")

	def verify_transaction(self, tran: Transaction):
		print(f"Verifying {self.mod.name}.{tran.name}")
		graph = to_verification_graph(tran.proto, tran, self.mod)
		# instance -> transaction name -> graph
		sub_graphs = {nn: {tran.name: to_verification_graph(tran.proto, tran, self.mod.submodules[nn])
						   for tran in spec.transactions}
					  for nn, spec in self.prob.submodules.items()}
		check = InteractiveCheck(self.mod)
		inactive_reset = get_inactive_reset(self.mod)

		# declare architectural state
		state_syms = make_symbols(self.prob.spec.state, self.mod.name + ".")
		for sym in state_syms.values(): check.constant(sym)

		# encode initial state
		for inv in self.prob.invariances:
			check.assume_at(0, inv)
		print("TODO: enable mappings")
		#for mapping in self.prob.mappings:
		#	check.assume_at(0, Implies(mapping.guard, Equals(mapping.arch, mapping.impl)))

		# remember top states
		top_states = [(TRUE(), graph.start)]
		sub_states = {nn: [(TRUE(), graph.start) for graph in tns.values()] for nn, tns in sub_graphs.items()}

		cycle = 0
		while len(top_states) > 0:
			### apply input assumptions

			# assume not in reset
			if inactive_reset is not None:
				check.assume_at(cycle, inactive_reset)
			for guard, state in top_states:
				# the inputs for any of the available edges could be applied
				I = [conjunction(*edge.guards, *edge.constraints.input) for edge in state.edges]
				check.assume_at(cycle, Implies(guard, disjunction(*I)))

			### Find feasible submodule edges
			feasible = {}
			for nn, states in sub_states.items():
				print(f"Trying to find edges for {nn} in cycle {cycle}")
				feasible[nn] = []
				for subguard, substate in states:
					for subedge in substate.edges:
						subI = conjunction(*subedge.guards, *subedge.constraints.input)
						if check.is_feasible_at(cycle, Implies(subguard, subI)):
							print(f"feasible:   {subI}")
							feasible[nn].append((subguard, subedge))
						else:
							print(f"infeasible: {subI}")

			### Find all feasible combinations of submodule edges





			cycle += 1
			check.unroll(1)
			# TODO: remove break
			print("DEBUG: break")
			break




	def proof_all(self):
		self.verify_inductive_base_case()
		for tran in self.prob.spec.transactions:
			self.verify_transaction(tran)


		# topgraph = to_veri_spec(self.mod, self.prob.spec)
		# subgraphs = {nn: to_veri_spec(self.mod.submodules[nn], spec) for nn, spec in self.prob.submodules.items()}
		# with BoundedCheck(f"module {self.mod.name} correctly implements its spec", self, cycles=topgraph.max_k) as check:
		# 	# test state encoding
		# 	#check.state(Symbol("test_state", BVType()), Symbol("test_state", BVType()), BV(0,32))
		#
		# 	encode_toplevel_module(graph=topgraph, check=check, spec=self.prob.spec, mod=self.mod,
		# 	                       invariances=self.prob.invariances, mappings=self.prob.mappings)
		# 	for instance, spec in self.prob.submodules.items():
		# 		encode_submodule(instance=instance, graph=subgraphs[instance], check=check, spec=spec, mod=self.mod.submodules[instance])



class InteractiveCheck:
	def __init__(self, mod: Module):
		self._mod = mod
		self._sym_names: Set[str] = set(self._mod.signals.keys())
		self._s = InteractiveSolver('yices2', debug=True)
		self._state_t = Type(mod.name + "_s")
		self._tran = Symbol(mod.name + "_t", FunctionType(BOOL, [self._state_t, self._state_t]))
		self._states = [Symbol("s0", self._state_t)]
		self._signals = []
		self._mappings = []
		self._load_symbols()
		self._load_model()


	def _load_model(self):
		self._s.push()
		self._s._send_cmd(*self._mod.smt2_src.split("\n"))
		self._s.fun(self._states[0])
		self._create_mapping()

	def _load_symbols(self):
		# create a list of signals in the module (this includes I/O and state)
		signal_symbols = [Symbol(name, tpe) for name, tpe in
						  chain(self._mod.inputs.items(), self._mod.outputs.items(), self._mod.state.items())]
		for submodule in self._mod.submodules.values():
			signal_symbols += [Symbol(submodule.io_prefix + name, tpe) for name, tpe in
							   chain(submodule.inputs.items(), submodule.outputs.items())]
		self._signals = signal_symbols

	def _create_mapping(self):
		assert len(self._states) == len(self._mappings) + 1
		def map_sym(symbol: Symbol, state_sym):
			tpe = symbol.symbol_type()
			is_bool_ = tpe.is_bv_type() and tpe.width == 1
			ft = FunctionType(BOOL if is_bool_ else tpe, [self._state_t])
			if tpe.is_array_type():	fn = self._mod.name + "_m " + symbol.symbol_name()
			else:                   fn = self._mod.name + "_n " + symbol.symbol_name()
			if is_bool_: return Ite(Function(Symbol(fn, ft), [state_sym]), BV(1,1), BV(0,1))
			else:        return Function(Symbol(fn, ft), [state_sym])

		# map module i/o and state to cycle dependent function
		# TODO: compute mappings lazily as not all of them will be used
		self._mappings.append({sym: map_sym(sym, self._states[-1]) for sym in self._signals})

	@property
	def cycles(self): return len(self._states) - 1

	def _in_cycle(self, ii: int, ee: SmtExpr):
		return substitute(ee, self._mappings[ii])

	def unroll(self, cycles: int):
		assert cycles > 0
		for ii in range(cycles):
			st = Symbol(f"s{len(self._states)}", self._state_t)
			self._states.append(st)
			self._s.fun(st)
			self._s.add(Function(self._tran, [self._states[-2], self._states[-1]]))
			self._create_mapping()

	def assume_at(self, cycle: int, expr: SmtExpr):
		assert self.cycles >= cycle >= 0, f"{self.cycles} >= {cycle} >= 0"
		self._s.add(self._in_cycle(cycle, expr))

	def is_feasible_at(self, cycle: int, expr: SmtExpr):
		assert self.cycles >= cycle >= 0, f"{self.cycles} >= {cycle} >= 0"
		is_sat, _ = self._s.check_sat([self._in_cycle(cycle, expr)])
		return is_sat

	def constant(self, sym: Symbol):
		self._s.fun(sym)




########################################################################################################################

KnownSolvers = {
	'yices2': { 'bin': 'yices-smt2',
	            'args': [], 'interactive_args': ['--incremental'] }, # TODO: enable '--incremental'
	'z3': { 'bin': 'z3', 'args': ['-in'], 'interactive_args': [] },
}

class Smt2Error(Exception):
	pass

class SolverBase:
	def __init__(self, name, debug):
		assert name in KnownSolvers, "Unknown solver!"
		self.name = name
		self.bin = os.path.expanduser(KnownSolvers[name]['bin'])
		self.args = KnownSolvers[name]['args']
		self.runtime = 0.0
		self.check_sat_calls = 0
		self.debug_print = print if debug else lambda x: None
		self.debug = debug

	def get_new_instance(self):
		raise Exception("Needs to be implemented in derrived class!")

class InteractiveSolver(SolverBase):
	def __init__(self, name, debug=False):
		super().__init__(name, debug)
		self.args += KnownSolvers[name]['interactive_args']
		self.is_running = False
		self.proc = None
		self._solver_output = None
		self.stack_size = 0
		# TODO: do we realy want to do this in the constructor?
		self.start()

	def start(self):
		if self.is_running: return
		self.proc = subprocess.Popen([self.bin] + self.args,
		                             stdin=subprocess.PIPE,
		                             stdout=subprocess.PIPE)
		self._solver_output = Smt2SolverOutputThread.create(self.proc.stdout)
		if self.proc.poll() is None:
			self.is_running = True
		else:
			raise Exception("Failed to start solver!")
		self._send_cmd("(set-logic QF_AUFBV)")

	def push(self):
		self._send_cmd("(push 1)")
		self.stack_size += 1

	def pop(self):
		assert self.stack_size > 0
		self._send_cmd("(pop 1)")
		self.stack_size -= 1

	def fun(self, function: Symbol):
		self._send_cmd(SmtLibCommand(smtcmd.DECLARE_FUN, [function]).serialize_to_string(daggify=False))

	def add(self, *assertions):
		for a in assertions:
			self._send_cmd(SmtLibCommand(smtcmd.ASSERT, [a]).serialize_to_string(daggify=False))

	def check_sat(self, assertions: Optional[list]=None, get_model=False):
		self.check_sat_calls += 1
		self._solver_output.clear()
		start = time.monotonic()
		self.push()
		if assertions is not None:
			self.add(*assertions)
		self._send_cmd("(check-sat)")
		rr = self._solver_output.read_line_blocking()
		self.debug_print(rr)
		self.runtime += time.monotonic() - start
		is_sat = (rr == 'sat')
		assert not (is_sat and get_model), "TODO: implement get-model"
		self.pop()
		return is_sat, []

	def stop(self):
		if not self.is_running: return
		# TODO: clean up this function, make more reliable...
		self._send_cmd("(exit)")
		time.sleep(0.00001)
		self.proc.terminate()
		time.sleep(0.0001)
		if self.proc.poll() is not None:
			self.proc.kill()
		self.is_running = False
		self.proc = None
		self._solver_output = None

	def __len__(self):
		return self.stack_size

	def _send_cmd(self, *cmds):
		assert self.is_running
		cmd_str = "\n".join(cmds) + "\n"
		self.debug_print(cmd_str)
		self.proc.stdin.write(cmd_str.encode('ASCII'))
		self.proc.stdin.flush()

class Smt2SolverOutputThread(threading.Thread):
	""" reads lines from a input stream and puts them into a threadsafe queue """
	@staticmethod
	def create(input_stream):
		t = Smt2SolverOutputThread(input_stream)
		t.start()
		return t
	def __init__(self, input_stream, debug=False):
		super().__init__()
		self.daemon = True
		self.inp = input_stream
		self.fifo = queue.Queue()
		if debug:
			self.debug_print = print
		else:
			self.debug_print = lambda x: None
	def run(self):
		try:
			self._read_line_loop()
		except Smt2Error as error:
			self.fifo.put(error)
		self.debug_print("ReadLineThread: done reading lines, closing the stream...")
		self.inp.close()
	def _read_line_loop(self):
		for line in iter(self.inp.readline, b''):
			self.debug_print("ReadLineThread: read line `{}`".format(line[:-1]))
			self._process_line(line[:-1].decode('ASCII'))
	def _process_line(self, line):
		if line.startswith("(error"):
			raise Smt2Error(line)
		self.fifo.put(line, block=False)
	def __len__(self):
		return self.fifo.qsize()
	def read_line_blocking(self, timeout=None):
		line = self.fifo.get(block=True, timeout=timeout)
		if isinstance(line, Exception): raise line
		return line
	def get_lines(self):
		lines = []
		read_done = False
		while not read_done:
			try:
				line = self.fifo.get(block=False)
				if isinstance(line, Exception): raise line
				lines.append(line)
			except queue.Empty:
				read_done = True
		return lines
	def clear(self):
		try:
			while True: self.fifo.get(block=False)
		except queue.Empty:
			return