#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List, Tuple, Dict, Optional
from functools import reduce
from itertools import zip_longest
from pysmt.shortcuts import *
from pysmt.smtlib.script import SmtLibScript, smtcmd

# local hack (TODO: remove)
yosys_path = os.path.expanduser(os.path.join('~', 'd', 'yosys'))
os.environ['PATH'] = yosys_path + ":" + os.environ['PATH']


# yosys interface functions
def require_yosys() -> str:
	r = subprocess.run(['yosys', '-V'], stdout=subprocess.PIPE)
	assert r.returncode == 0, f"Failed to find yosys! {r}"
	version = re.match(r'Yosys (\d+\.\d+\+\d+)', r.stdout.decode('utf-8')).group(1)
	return version

def verilog_to_smt2(filename: str, arrays: bool = True) -> str:
	assert os.path.isfile(filename)
	with tempfile.TemporaryDirectory() as dd:
		outfile = os.path.join(dd, "module.smt2")
		mem = "memory -nomap -nordff" if arrays else "memory"
		cmds = [f"read_verilog {filename}", "proc", "opt", mem, f"write_smt2 {outfile}"]
		subprocess.run(['yosys', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		with open(outfile) as ff:
			smt2_src = ff.read()
	return smt2_src


def parse_yosys_smt2(smt2_src: str) -> dict:
	res = {
		'inputs': re.compile(r'; yosys-smt2-input ([^\s]+) ([\d+])'),
		'outputs': re.compile(r'; yosys-smt2-output ([^\s]+) ([\d+])'),
		'registers': re.compile(r'; yosys-smt2-register ([^\s]+) ([\d+])'),
		'memories': re.compile(r'; yosys-smt2-memory ([^\s]+) ([\d+]) ([\d+]) ([\d+]) ([\d+]) (async|sync)'),
		'modules': re.compile(r'; yosys-smt2-module ([^\s]+)')
	}
	results = defaultdict(list)
	for line in smt2_src.splitlines():
		for name, regex in res.items():
			m = regex.match(line)
			if m is not None:
				results[name].append(m.groups())
	results = dict(results)
	assert len(results['modules']) == 1, "Currently this software only works for single modules!"
	results['name'] = results['modules'][0][0]
	results.pop('modules')
	for key in ['inputs', 'outputs', 'registers']:
		results[key] = { ii[0]: BVSignal.from_yosys(*ii) for ii in results[key]}
	results['memories'] = { ii[0]: ArraySignal.from_yosys(*ii) for ii in results['memories']}
	results['state'] = {**results['memories'], **results['registers']}
	results.pop('memories')
	results.pop('registers')
	return results

sat = "sat"
unsat = "unsat"

class Solver:
	def __init__(self, header, logic='QF_AUFBV', bin='yices-smt2'):
		self.header = header
		self.logic = logic
		self.bin = bin
		subprocess.run(['which', bin], check=True, stdout=subprocess.PIPE)
		self.assertions = []
		self.funs = []

	def reset(self):
		self.assertions = []
		self.funs = []

	def add(self, *assertions):
		self.assertions += assertions

	def fun(self, function):
		self.funs.append(function)

	def _write_scrip(self, filename, script, get_model=False):
		with open(filename, 'w') as ff:
			print("(set-logic QF_AUFBV)", file=ff)
			print("; smt script generated using yosys + a custom python script", file=ff)
			print(file=ff)
			print("; yosys generated:", file=ff)
			print(self.header, file=ff)
			print("; custom cmds", file=ff)
			script.serialize(outstream=ff, daggify=False)
			print("(check-sat)", file=ff)
			if get_model:
				print("(get-model)", file=ff)

	def solve(self, filename=None, get_model=True):
		script = SmtLibScript()
		for f in self.funs:
			script.add(smtcmd.DECLARE_FUN, [f])
		for a in self.assertions:
			script.add(smtcmd.ASSERT, [a])

		if filename is None:
			(_, filename) = tempfile.mkstemp()

		self._write_scrip(filename=filename, script=script, get_model=False)
		r = subprocess.run([self.bin, filename], stdout=subprocess.PIPE, check=True).stdout.decode('utf-8').strip()
		if r == unsat:
			return unsat, None
		assert r == sat, r


		if not get_model:
			return sat, None
		# get model
		self._write_scrip(filename=filename, script=script, get_model=True)
		r = subprocess.run([self.bin, filename], stdout=subprocess.PIPE, check=True).stdout.decode('utf-8')
		return sat, r

class Module:
	def __init__(self, name: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"]):
		self._name = name
		self._inputs = inputs
		self._outputs = outputs
		self._state = state
		self.state_t = Type(name + "_s")
		self._transition_fun = Symbol(name + "_t", FunctionType(BOOL, [self.state_t, self.state_t]))

	@property
	def name(self): return self._name

	def __str__(self):
		dd = [self._name, '-' * len(self._name), ""]
		def render_fields(fields)-> List[str]:
			return [str(ff) for ff in fields.values()]
		dd += ["Inputs:"] + render_fields(self._inputs) + [""]
		dd += ["Outputs:"] + render_fields(self._outputs) + [""]
		dd += ["State:"] + render_fields(self._state) + [""]
		return '\n'.join(dd)
	def __repr__(self): return str(self)

	def declare_states(self, solver: Solver, names: List[str]) -> list:
		states = [State(name, self) for name in names]
		for state in states:
			solver.fun(state.sym)
		return states

	def transition(self, solver: Solver, states: List["State"]):
		assert all(state._mod == self for state in states)
		if len(states) < 2: return
		for ii in range((len(states) - 1)):
			solver.add(Function(self._transition_fun, [states[ii].sym, states[ii+1].sym]))

	def _get_signal(self, name: str) -> Optional["Signal"]:
		for dd in [self._inputs, self._outputs, self._state]:
			if name in dd:
				return dd[name]
		return None

	def get(self, name: str, state: "State"):
		signal = self._get_signal(name=name)
		assert signal is not None, f"Unknown io/state element {name}"
		ft = FunctionType(signal.tpe, [self.state_t])
		if isinstance(signal, ArraySignal):
			fn = self.name + "_m " + signal.name
		else:
			fn = self.name + "_n " + signal.name
		return Function(Symbol(fn, ft), [state.sym])

class Signal:
	def __init__(self, name: str):
		self.name = name
		self.tpe = None

	def __str__(self):
		return f"{self.name} : ?"

class BVSignal(Signal):
	@staticmethod
	def from_yosys(name: str, bits: str):
		bits = int(bits)
		if bits == 1:
			return BoolSignal(name=name)
		assert bits > 1
		return BVSignal(name=name, bits=bits)

	def __init__(self, name: str, bits: int):
		super().__init__(name=name)
		self.bits = bits
		self.tpe = BVType(bits)

	def __str__(self):
		return f"{self.name} : bv<{self.bits}>"

class BoolSignal(Signal):
	def __init__(self, name: str):
		super().__init__(name=name)
		self.tpe = BOOL
		self.bits = 1
	def __str__(self):
		return f"{self.name} : bool"

# https://www.reddit.com/r/yosys/comments/39t2fl/new_support_for_memories_in_write_smt2_via_arrays/
class ArraySignal(Signal):
	def __init__(self, name: str, address_bits: int, data_bits: int):
		super().__init__(name=name)
		self.name = name
		self.address_bits = address_bits
		self.data_bits = data_bits
		self.tpe = ArrayType(BVType(self.address_bits), BVType(self.data_bits))
	@staticmethod
	def from_memory(name: str, address_bits: int, data_bits: int, read_ports: int, write_ports: int, async_read: bool):
		assert not async_read, "asynchronous memories are not supported!"
		return ArraySignal(name=name, address_bits=address_bits, data_bits=data_bits)
	@staticmethod
	def from_yosys(name: str, address_bits: str, data_bits: str, read_ports: str, write_ports: str, async_read: str):
		return ArraySignal.from_memory(name=name, address_bits=int(address_bits), data_bits=int(data_bits),
									   read_ports=int(read_ports), write_ports=int(write_ports),
									   async_read=(async_read == "async"))
	def __str__(self):
		return f"{self.name} : bv<{self.address_bits}> -> bv<{self.data_bits}>"


class State:
	def __init__(self, name: str, module: Module):
		self.name = name
		self.sym = Symbol(name, module.state_t)
		self._mod = module

	def __str__(self):
		return f"(declare-fun |{self.name}| () {self._mod.state_t})"

	def __getitem__(self, name) -> str:
		return self._mod.get(name, self)


def merge_dicts(a: dict, b: dict) -> dict:
	keys = a.keys() | b.keys()
	if len(keys) < len(a) + len(b):
		for k in keys:
			assert not (k in a and k in b), f"Key {k} is used in a and b!"
	return {**a, **b}

class Protocol:
	def __init__(self, mappings):
		self.mappings = mappings

	def __len__(self):
		return len(self.mappings)

	def __or__(self, other):
		assert isinstance(other, Protocol)
		m = [merge_dicts(*c) for c in zip_longest(self.mappings, other.mappings, fillvalue=dict())]
		return Protocol(mappings=m)

	def __add__(self, other):
		assert isinstance(other, Protocol)
		m = self.mappings + other.mappings
		return Protocol(mappings=m)

def BitSerial(signal: str, sym) -> Protocol:
	return Protocol([{signal: BVExtract(sym, ii, ii)} for ii in range(sym.bv_width())])

def Repeat(signal: str, sym, cycles) -> Protocol:
	return Protocol([{signal: sym}] * cycles)

def Map(signal:str, sym) -> Protocol:
	return Protocol([{signal: sym}])

class Transaction:
	def __init__(self, name: str, args: List[Signal], ret_args: List[Signal], proto: Protocol, semantics):
		self.name = name
		self.args = args
		self.ret_args = ret_args
		self.proto = proto
		self.semantics = semantics



class Spec:
	def __init__(self, arch_state, mapping, transactions, idle, invariances):
		self.arch_state = arch_state
		self.transactions = transactions
		self.idle = idle
		self.invariances = invariances
		self.mapping = mapping

class RegfileSpec(Spec):
	def __init__(self):
		x = ArraySignal('x', 5, 32)

		def mapping(state: State, x):
			asserts = []
			memory = state['memory']
			for ii in range(32):
				reg = Select(x, BV(ii, 5))
				for jj in range(16):
					a = Select(memory, BV(ii*16 + jj, 9))
					b = BVExtract(reg, start=jj*2, end=jj*2+1)
					asserts.append(Equals(a, b))
			return asserts

		# build transaction
		rs1_addr = Symbol('rs1_addr', BVType(5))
		rs2_addr = Symbol('rs2_addr', BVType(5))
		rd_enable = Symbol('rd_enable')
		rd_addr = Symbol('rd_addr', BVType(5))
		rd_data = Symbol('rd_data', BVType(32))
		args = [rs1_addr, rs2_addr, rd_enable, rd_addr, rd_data]
		rs1_data = Symbol('rs1_data', BVType(32))
		rs2_data = Symbol('rs2_data', BVType(32))
		ret = [rs1_data, rs2_data]

		protocol = (Map('i_go', Bool(True)) +
			       (BitSerial('i_rd', rd_data) | BitSerial('o_rs1', rs1_data)     | BitSerial('o_rs2', rs2_data) |
		            Repeat('i_go', Bool(False), 32)      | Repeat('i_rd_en', rd_enable, 32) | Repeat('i_rd_addr', rd_addr, 32) |
		            Repeat('i_rs1_addr', rs1_addr, 32) | Repeat('i_rs2_addr', rs2_addr, 32)))


		def semantics(rs1_addr, rs2_addr, rd_enable, rd_addr, rd_data, x):
			rs1_data = Select(x, rs1_addr)
			rs2_data = Select(x, rs2_addr)
			x_n = Ite(rd_enable, Store(x, rd_addr, rd_data), x)
			return { 'rs1_data': rs1_data, 'rs2_data': rs2_data, 'x': x_n}

		transactions = [Transaction(name="rw", args=args, ret_args=ret, semantics=semantics, proto=protocol)]

		idle = lambda state: And(Not(state['i_go']), Not(state['i_rd_en']))

		# TODO: infer
		inv = [lambda state: Equals(state['wcnt'], BV(0, 5))]
		super().__init__(arch_state={'x': x}, mapping=mapping, transactions=transactions, idle=idle, invariances=inv)




def proof_no_mem_change(regfile: Module, solver: Solver):
	states = regfile.declare_states(solver, ['s1', 's2'])
	regfile.transition(solver, states)

	start, end = states[0], states[-1]

	# setup assumptions
	# assuming that i_rd_en is false
	solver.add(Not(start['i_rd_en']))

	# assert that memory does not change
	solver.add(Not(Equals(start['memory'], end['memory'])))


def is_bool(expr):
	return expr.is_bool_constant() or expr.is_bool_op() or (expr.is_symbol() and expr.symbol_type().is_bool_type())

class ProofEngine:
	def __init__(self, mod: Module, spec: Spec, solver: Solver, reset_signal: str, outdir=None):
		self.mod = mod
		self.spec = spec
		self.solver = solver
		self.reset_signal = reset_signal # TODO: move this info to Module class
		self.verbose = True
		self.outdir = outdir
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)
		self.proof_count = 0

	def unroll(self, cycles):
		states = self.mod.declare_states(self.solver, [f's{ii}' for ii in range(cycles+1)])
		self.mod.transition(self.solver, states)
		return states

	def reset(self, cycles=1):
		states = self.unroll(cycles)
		# assert reset signal for N cycles
		for s in states[:-1]:
			self.solver.add(s[self.reset_signal])
		return states

	def idle(self):
		s0, s1 = self.unroll(1)
		self.solver.add(self.spec.idle(s0))
		return s0, s1

	def transaction(self, trans: Transaction, assume_invariances=False):
		# unroll for complete transaction
		states = self.unroll(len(trans.proto))
		start, end = states[0], states[-1]

		# assume invariances hold at the beginning of the transaction
		if assume_invariances:
			for inv in self.spec.invariances:
				self.solver.add(inv(start))

		# declare transaction args
		for arg in trans.args + trans.ret_args:
			self.solver.fun(arg)

		# apply cycle behavior
		for m, state in zip(trans.proto.mappings, states):
			for signal_name, expr in m.items():
				signal = state[signal_name]
				if is_bool(expr):
					self.solver.add(Iff(signal, expr))
				else:
					if expr.bv_width() == 1:
						expr = Equals(expr, BV(1, 1))
						self.solver.add(Iff(signal, expr))
					else:
						self.solver.add(Equals(signal, expr))

		# return first and last state
		return start, end

	def proof_invariances(self):
		# TODO: take invariance dependence into account
		for inv in self.spec.invariances:
			self.proof_invariance(inv)

	def proof_invariance(self, invariance):
		# TODO: take strengthening invariances into account
		with Proof("invariance holds after reset", self):
			final = self.reset(cycles=1)[-1]
			# invariance should hold after reset
			self.solver.add(Not(invariance(final)))

		with Proof("invariance is inductive over idle period", self):
			s0, s1 = self.idle()
			self.solver.add(invariance(s0))
			# invariance should hold after idle step
			self.solver.add(Not(invariance(s1)))


		for trans in self.spec.transactions:
			with Proof(f"invariance is inductive over {trans.name} transaction", self):
				start, end = self.transaction(trans=trans, assume_invariances=False)
				# assume this particular invariance
				self.solver.add(invariance(start))
				# invariance should hold after transaction
				self.solver.add(Not(invariance(start)))

class Proof:
	def __init__(self, name: str, engine: ProofEngine):
		self.engine = engine
		self.name = name
		self.ii = self.engine.proof_count
		self.engine.proof_count += 1
	def __enter__(self):
		self.engine.solver.reset()
	def __exit__(self, exc_type, exc_val, exc_tb):
		if exc_type is not None: return
		if self.engine.outdir is not None:
			filename = os.path.join(self.engine.outdir, f"{self.ii}.{self.name}.smt2")
		else:
			filename = None
		res, model = self.engine.solver.solve(filename =filename)
		assert res == unsat, f"❌ Failed to proof: {self.name}\nCEX:\n{model}"
		if self.engine.verbose:
			print(f"✔️ {self.name}")

regfile_v = os.path.join('serv', 'rtl', 'serv_regfile.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	smt2_src = verilog_to_smt2(regfile_v)
	smt2_names = parse_yosys_smt2(smt2_src)
	regfile = Module(**smt2_names)

	"""
	print(regfile)
	solver = Solver(smt2_src)
	proof_no_mem_change(regfile, solver)
	print(solver.solve())
	"""


	spec = RegfileSpec()
	solver = Solver(smt2_src)
	engine = ProofEngine(mod=regfile,spec=spec, solver=solver, reset_signal='i_rst', outdir=".")
	engine.proof_invariances()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
