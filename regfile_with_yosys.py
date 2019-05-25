#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List, Tuple, Dict, Optional
from functools import reduce
from itertools import zip_longest, chain
from pysmt.shortcuts import *
from pysmt.smtlib.script import SmtLibScript, smtcmd
import operator
import tabulate

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
	assert len(results['modules']) == 1, "Currently this software only works for single modules!"
	results['name'] = results['modules'][0][0]
	for key in ['inputs', 'outputs', 'registers']:
		results[key] = { ii[0]: BVSignal.from_yosys(*ii) for ii in results[key]}
	results['memories'] = { ii[0]: ArraySignal.from_yosys(*ii) for ii in results['memories']}
	results['state'] = {**results['memories'], **results['registers']}
	results = dict(results)
	results.pop('modules')
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

	def _write_scrip(self, filename, script):
		with open(filename, 'w') as ff:
			print("(set-logic QF_AUFBV)", file=ff)
			print("; smt script generated using yosys + a custom python script", file=ff)
			print(file=ff)
			print("; yosys generated:", file=ff)
			print(self.header, file=ff)
			print("; custom cmds", file=ff)
			script.serialize(outstream=ff, daggify=False)

	def solve(self, filename=None, get_model=True, get_values=None):
		script = SmtLibScript()
		for f in self.funs:
			script.add(smtcmd.DECLARE_FUN, [f])
		for a in self.assertions:
			script.add(smtcmd.ASSERT, [a])
		script.add(smtcmd.CHECK_SAT, [])

		if filename is None:
			(_, filename) = tempfile.mkstemp()

		self._write_scrip(filename=filename, script=script)
		r = subprocess.run([self.bin, filename], stdout=subprocess.PIPE, check=True).stdout.decode('utf-8').strip()
		if r == unsat:
			return unsat, None
		assert r == sat, r


		if not get_model:
			return sat, None
		# get model
		if get_values is None:
			script.add(smtcmd.GET_MODEL, [])
		else:
			for vv in get_values:
				script.add(smtcmd.GET_VALUE, [vv])
		self._write_scrip(filename=filename, script=script)
		r = subprocess.run([self.bin, filename], stdout=subprocess.PIPE, check=True).stdout.decode('utf-8')
		return sat, r

class Module:
	@staticmethod
	def load(verilog_file: str, reset:Optional[str] = None):
		assert os.path.isfile(verilog_file)
		smt2_src = verilog_to_smt2(verilog_file)
		smt2_names = parse_yosys_smt2(smt2_src)
		return Module(**smt2_names, smt2_src=smt2_src, reset=reset)

	def __init__(self, name: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"], smt2_src: str, reset: Optional[str] = None):
		self._name = name
		self._inputs = inputs
		self._outputs = outputs
		self._state = state
		self.state_t = Type(name + "_s")
		self._transition_fun = Symbol(name + "_t", FunctionType(BOOL, [self.state_t, self.state_t]))
		self.smt2_src = smt2_src
		self.reset = reset

	@property
	def name(self): return self._name

	def is_input(self, name: str):
		return name in self._inputs
	def is_output(self, name: str):
		return name in self._outputs
	def is_state(self, name: str):
		return name in self._state
	@property
	def inputs(self):
		return self._inputs.values()
	@property
	def outputs(self):
		return self._outputs.values()
	@property
	def state(self):
		return self._state.values()
	@property
	def non_mem_state(self):
		return [s for s in self.state if not isinstance(s, ArraySignal)]

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
	def __init__(self, mappings: list):
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

	def __mul__(self, other):
		assert isinstance(other, int)
		assert other < 1000
		m = self.mappings * other
		return Protocol(mappings=m)

	def __rshift__(self, other):
		assert isinstance(other, int)
		m = [dict() for _ in range(other)] + self.mappings
		return Protocol(mappings=m)

	def __lshift__(self, other):
		assert isinstance(other, int)
		m = self.mappings + [dict() for _ in range(other)]
		return Protocol(mappings=m)

def BitSerial(signal: str, sym) -> Protocol:
	return Protocol([{signal: BVExtract(sym, ii, ii)} for ii in range(sym.bv_width())])

def Repeat(signal: str, sym, cycles) -> Protocol:
	return Protocol([{signal: sym}] * cycles)

def Map(signal:str, sym) -> Protocol:
	return Protocol([{signal: sym}])

class Transaction:
	def __init__(self, name: str, args: list, ret_args: list, proto: Protocol, semantics):
		self.name = name
		self.args = args
		self.ret_args = ret_args
		self.proto = proto
		self.semantics = semantics



def default(expr, default):
	return expr if expr is not None else default

class Spec:
	def __init__(self, arch_state=None, mapping=None, transactions=None, idle=None, invariances=None):
		self.arch_state = default(arch_state, {})
		self.transactions = default(transactions, [])
		self.idle = default(idle, lambda state: Bool(True))
		self.invariances = default(invariances, [])
		self.mapping = default(mapping, lambda state: [Bool(True)])


def proof_no_mem_change(regfile: Module, solver: Solver):
	states = regfile.declare_states(solver, ['s1', 's2'])
	regfile.transition(solver, states)

	start, end = states[0], states[-1]

	# setup assumptions
	# assuming that i_rd_en is false
	solver.add(Not(start['i_rd_en']))

	# assert that memory does not change
	solver.add(Not(Equals(start['memory'], end['memory'])))


def get_type(expr):
	if expr.is_symbol(): return expr.symbol_type()
	if expr.is_function_application():
		return expr.function_name().symbol_type().return_type
	if expr.is_select():
		return expr.arg(0).get_type().elem_type
	assert False, f"should not get here! {expr}"

def is_bool(expr):
	if expr.is_bool_constant() or expr.is_bool_op(): return True
	if expr.is_bv_op(): return False
	if expr.is_symbol(): return expr.symbol_type().is_bool_type()
	if expr.is_function_application():
		return expr.function_name().symbol_type().return_type.is_bool_type()
	if expr.is_select():
		return expr.arg(0).get_type().elem_type.is_bool_type()
	if expr.is_ite():
		return is_bool(expr.arg(1))
	if expr.is_store() or expr.is_array_value():
		return False
	assert False, f"should not get here! {expr}"

def to_bool(expr):
	assert not is_bool(expr)
	assert expr.bv_width() == 1
	return  Equals(expr, BV(1, 1))

def equal(e0, e1):
	if not is_bool(e0) and not is_bool(e1): return Equals(e0, e1)
	if not is_bool(e0): e0 = to_bool(e0)
	if not is_bool(e1): e1 = to_bool(e1)
	return Iff(e0, e1)

def conjunction(*args):
	assert len(args) > 0
	if len(args) == 1: return args[0]
	else: return reduce(And, args)

class ProofEngine:
	def __init__(self, mod: Module, spec: Spec, solver: Solver, outdir=None):
		self.mod = mod
		self.spec = spec
		self.solver = solver
		self.verbose = True
		self.outdir = outdir
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)
		self.proof_count = 0
		self.states = []
		self.active_proof = None
		self.signals = list(self.mod.inputs) + list(self.mod.outputs) + list(self.mod.non_mem_state)
		self.last_proof_accepted = False
		self.active_trans : Optional[Transaction] = None

	def _read_all_signals(self, states) -> list:
		expressions = []
		for state in states:
			for sig in self.signals:
				expressions.append(state[sig.name])
		return expressions

	def _read_all_trans(self, trans: Transaction) -> list:
		return [sig for sig in chain(trans.args, trans.ret_args)]

	def unroll(self, cycles):
		states = self.mod.declare_states(self.solver, [f's{ii}' for ii in range(cycles+1)])
		self.states += states
		self.mod.transition(self.solver, states)
		return states

	def reset(self, cycles=1):
		assert self.mod.reset is not None, f"Module {self.mod.name} does not have a reset signal declared!"
		states = self.unroll(cycles)
		# assert reset signal for N cycles
		for s in states[:-1]:
			self.solver.add(s[self.mod.reset])
		return states

	def idle(self):
		s0, s1 = self.unroll(1)
		self.solver.add(self.spec.idle(s0))
		if self.mod.reset is not None:
			self.solver.add(Not(s0[self.mod.reset]))
		return s0, s1

	def transaction(self, trans: Transaction, assume_invariances=False, skip_reads=False, cycles=None):
		cycle_count = min(default(cycles, len(trans.proto)), len(trans.proto))
		assert cycle_count >= 1, f"{cycles}"

		# unroll for complete transaction
		states = self.unroll(cycle_count)
		start, end = states[0], states[-1]
		if cycle_count < len(trans.proto):
			end = None

		# assume invariances hold at the beginning of the transaction
		if assume_invariances:
			for inv in self.spec.invariances:
				self.solver.add(inv(start))

		# assume reset is inactive during the transaction
		if self.mod.reset is not None:
			for state in states:
				self.solver.add(Not(state[self.mod.reset]))

		# declare transaction args
		for arg in trans.args:
			self.solver.fun(arg)

		# apply cycle behavior
		cycles = []
		for m, state in zip(trans.proto.mappings, states):
			reads = {}
			for signal_name, expr in m.items():
				assert not self.mod.is_state(signal_name), f"protocols may only read/write from io: {signal_name}"
				signal = state[signal_name]

				if self.mod.is_output(signal_name):
					if not skip_reads:
						# if the signal is an output, we need to read it
						read_sym = Symbol(f"{signal_name}_cyc{len(cycles)}_read", get_type(signal))
						self.solver.fun(read_sym)
						self.solver.add(equal(signal, read_sym))
						reads[signal_name] = read_sym
				else:
					# if the signal is an input, we just apply the constraint for this cycle
					assert self.mod.is_input(signal_name)
					self.solver.add(equal(signal, expr))
			# remember all read symbols
			cycles.append(reads)

		# return first and last state
		return start, end, cycles

	def proof_all(self):
		self.proof_invariances()
		self.proof_transactions()
		if len(self.spec.arch_state) > 0:
			print("WARN: we still need to prove that the architectural states stay the same across IDLE transactions!")

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
				start, end, _ = self.transaction(trans=trans, assume_invariances=False, skip_reads=True)
				# assume this particular invariance
				self.solver.add(invariance(start))
				# invariance should hold after transaction
				self.solver.add(Not(invariance(start)))

	def proof_transactions(self):
		for trans in self.spec.transactions:
			self.proof_transaction(trans)

	def map_arch_state(self, suffix: str, state: State):
		arch_state = {name: Symbol(name + suffix, tpe) for name, tpe in self.spec.arch_state.items()}
		for sym in arch_state.values():
			self.solver.fun(sym)
		self.solver.add(conjunction(*self.spec.mapping(state=state, **arch_state)))
		return arch_state

	def proof_transaction(self, trans: Transaction):
		assert self.active_trans is None
		self.active_trans = trans
		cycles = len(trans.proto)

		# 1.) attempt a full proof
		with Proof(f"transaction {trans.name} is correct", self, check=False):
			vc = self.setup_transaction_proof(trans)
			self.solver.add(Not(conjunction(*vc)))
		if self.last_proof_accepted:
			self.active_trans = None
			return True

		# 2.) incremental proof
		check_vcs = 0
		for cc in range(1, cycles+1):
			vcs = self.setup_transaction_proof(trans, cycles=cc)
			max_vc = len(vcs)
			for ii in range(max_vc - check_vcs):
				with Proof(f"{trans.name}: {vcs[check_vcs]} ({cc} cycles)", self):
					vc = self.setup_transaction_proof(trans, cycles=cc)[:check_vcs+1]
					proven = vc[:-1]
					if len(proven) > 0:
						self.solver.add(conjunction(*proven))
					self.solver.add(Not(vc[-1]))
				check_vcs += 1
		assert False, f"should not get here! check_vcs={check_vcs}"

	def setup_transaction_proof(self, trans: Transaction, cycles=None):
		start, end, reads = self.transaction(trans=trans, assume_invariances=True, cycles=cycles)
		complete = end is not None

		# declare return args
		arch_outs = {name: Symbol(name + "_n", tpe) for name, tpe in self.spec.arch_state.items()}
		for sym in trans.ret_args + list(arch_outs.values()):
			self.solver.fun(sym)

		# semantics
		start_arch = self.map_arch_state("", start)
		sem_out = trans.semantics(**{arg.symbol_name(): arg for arg in trans.args}, **start_arch)

		# map outputs
		end_arch = self.map_arch_state("_read", end) if complete else {}
		for name, expr in merge_dicts({arg.symbol_name(): arg for arg in trans.ret_args}, end_arch).items():
			self.solver.add(equal(expr, sem_out[name]))

		# verify reads
		vc = []
		for ii, m in enumerate(trans.proto.mappings):
			if ii >= len(reads): break
			for signal_name, expr in m.items():
				if not self.mod.is_output(signal_name): continue
				read = reads[ii][signal_name]
				vc.append(equal(read, expr))
		# verify arch state if we are dealing with a complete transaction
		if complete:
			for name in self.spec.arch_state.keys():
				vc.append(Equals(arch_outs[name], end_arch[name]))
		return vc

	def start_proof(self, proof):
		ii = self.proof_count
		self.proof_count += 1
		assert self.active_proof is None
		self.active_proof = proof
		self.solver.reset()
		self.states = []
		return ii

	def parse_cex(self, cex: str, states: List[State]):
		state_to_id = {st.name: ii for ii, st in enumerate(states)}
		signals = [dict() for _ in range(len(states))]
		trans = {}

		prefix = rf'\(\(\(\|{self.mod.name}_n ([a-zA-Z_0-9]+)\|\s+([a-zA-Z_0-9]+)\)\s+'
		suffix = r'\)\)'
		bv_bool = '(#b[01]+|false|true)'
		re_signal = re.compile(prefix + bv_bool + suffix)
		re_trans = re.compile(f'\(\(([a-zA-Z_0-9]+)\s+' + bv_bool + suffix)

		def parse_value(vv):
			if vv == 'true': return "1"
			if vv == 'false': return "0"
			assert len(vv) > 2
			return vv[2:]

		for line in cex.splitlines():
			if line.strip() == 'sat': continue
			m = re_signal.match(line)
			if m is not None:
				signal, state, value = m.groups()
				signals[state_to_id[state]][signal] = parse_value(value)
			else:
				m = re_trans.match(line)
				assert m is not None, f"Failed to parse line: {line}"
				name, value = m.groups()
				trans[name] = parse_value(value)
		return signals, trans

	def cex_to_table(self, cex: List[dict]) -> List[List[str]]:
		table = []
		signal_names = [s.name for s in self.signals]
		table.append([""] + [str(ii) for ii in range(len(cex))])
		for sig in signal_names:
			table.append([sig] + [cc.get(sig, "?") for cc in cex])
		return table

	def cex_to_csv(self, cex: List[dict], out):
		for line in self.cex_to_table(cex):
			print(",".join(line), file=out)

	def render_transact_cex(self, values: dict):
		if self.active_trans is None: return ""
		render_val = lambda a: f"{a.symbol_name()} = {values[a.symbol_name()]}"
		args = ', '.join(render_val(a) for a in self.active_trans.args)
		out = f"\n\n{self.active_trans.name}({args}) =\n"
		out += '\n'.join("\t" + render_val(a) for a in self.active_trans.ret_args)
		return out

	def run_proof(self, proof):
		assert self.active_proof == proof
		if self.outdir is not None:
			filename = os.path.join(self.outdir, f"{proof.ii}.{proof.name}.smt2")
		else:
			filename = None
		if len(self.states) > 0:
			read = self._read_all_signals(self.states)
			if self.active_trans is not None:
				read += self._read_all_trans(self.active_trans)
		else:
			read = None
		res, model = self.solver.solve(filename=filename, get_model=True, get_values=read)
		if res == sat and read is not None:
			signals, trans = self.parse_cex(model, self.states)
			with open('cex.csv', 'w') as ff:
				self.cex_to_csv(signals, out=ff)
			print("Wrote counter example to cex.csv")
			table = self.cex_to_table(signals)
			model = tabulate.tabulate(tabular_data=table[1:], headers=table[0])
			model += self.render_transact_cex(trans)
		if proof.check:
			assert res == unsat, f"❌ Failed to proof: {proof.name}\nCEX:\n{model}"
		if self.verbose:
			if res == unsat:
				print(f"✔️ {proof.name}")
			else:
				print(f"❌ {proof.name}")
		self.active_proof = None
		self.last_proof_accepted = res == unsat


class Proof:
	def __init__(self, name: str, engine: ProofEngine, check = True):
		self.engine = engine
		self.name = name
		self.check = check
		self.ii = None
	def __enter__(self):
		self.ii = self.engine.start_proof(self)
		return self
	def __exit__(self, exc_type, exc_val, exc_tb):
		if exc_type is not None: return
		self.engine.run_proof(self)

########################################################################################################################
# Regfile Specific Code
########################################################################################################################

class RegfileSpec(Spec):
	def __init__(self):
		x = ArrayType(BVType(5), BVType(32)) #ArraySignal('x', 5, 32)

		def mapping(state: State, x):
			asserts = []
			memory = state['memory']
			for ii in range(32):
				reg = Select(x, BV(ii, 5))
				iis = [Select(memory, BV(ii*16 + jj, 9)) for jj in reversed(range(16))]
				asserts.append(Equals(reg, reduce(BVConcat, iis)))
				# for jj in range(16):
				# 	a = Select(memory, BV(ii*16 + jj, 9))
				# 	b = BVExtract(reg, start=jj*2, end=jj*2+1)
				# 	asserts.append(Equals(a, b))
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

		protocol = (
			(Map('i_go', Bool(True)) + Map('i_go', Bool(False)) * 34) |
			(Repeat('i_rs1_addr', rs1_addr, 32) >> 1) |
			(Repeat('i_rs2_addr', rs2_addr, 32) >> 1) |
			(Repeat('i_rd_addr', rd_addr, 32) >> 3)   |
			(Map('i_rd_en', Bool(False)) * 3 + Repeat('i_rd_en', rd_enable, 32))   |
			(BitSerial('o_rs1', rs1_data) >> 3)       |
			(BitSerial('o_rs2', rs2_data) >> 3)       |
			(BitSerial('i_rd', rd_data) >> 3)
		)
		assert len(protocol) == 35

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

class AdderSpec(Spec):
	def __init__(self, bits):
		a = Symbol('a', BVType(bits))
		b = Symbol('b', BVType(bits))
		c = Symbol('c', BVType(bits))
		carry = Symbol('carry', BVType(1))
		protocol = Map('clr', Bool(True)) + (BitSerial('a', a) | BitSerial('b', b) | BitSerial('q', c) |
											 Repeat('clr', Bool(False), bits))
		protocol.mappings[-1]['o_v'] = carry

		def semantics(a, b):
			c = BVAdd(a, b)
			carry = BVExtract(BVAdd(BVZExt(a, 1), BVZExt(b, 1)), bits, bits)
			return {'c': c, 'carry': carry}

		transactions = [Transaction(name=f"add{bits}", args=[a,b], ret_args=[c,carry], semantics=semantics, proto=protocol)]

		super().__init__(transactions=transactions)



regfile_v = os.path.join('serv', 'rtl', 'serv_regfile.v')
add_v = os.path.join('serv', 'rtl', 'ser_add.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	regfile = Module.load(regfile_v, reset='i_rst')
	adder = Module.load(add_v, reset='rst')

	"""
	print(regfile)
	solver = Solver(smt2_src)
	proof_no_mem_change(regfile, solver)
	print(solver.solve())
	"""

	mods = [(adder, lambda: AdderSpec(32)), (regfile, RegfileSpec)]

	for mod, spec_fun in mods[1:]:
		reset_env()
		spec = spec_fun()
		print(f"Trying to proof {mod.name}")
		print(mod)
		solver = Solver(mod.smt2_src)
		engine = ProofEngine(mod=mod,spec=spec, solver=solver, outdir=".")
		#engine.proof_invariances()
		engine.proof_all()
		print()
		print()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
