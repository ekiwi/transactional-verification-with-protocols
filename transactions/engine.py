#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os, re
from typing import List, Tuple, Dict, Optional
from itertools import zip_longest, chain
from pysmt.shortcuts import *
import tabulate

from .module import Module, State
from .utils import *
from .solver import sat, unsat

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

def BitSerial(signal: str, sym, max_bits: Optional[int] = None) -> Protocol:
	max_bits = default(max_bits, sym.bv_width())
	bits = min(max_bits, sym.bv_width())
	return Protocol([{signal: BVExtract(sym, ii, ii)} for ii in range(bits)])

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

class Spec:
	def __init__(self, arch_state=None, mapping=None, transactions=None, idle=None, invariances=None, case_split=None):
		self.arch_state = default(arch_state, {})
		self.transactions = default(transactions, [])
		self.idle = default(idle, lambda state: Bool(True))
		self.invariances = default(invariances, [])
		self.mapping = default(mapping, lambda state: [Bool(True)])
		self.case_split = default(case_split, list())


def proof_no_mem_change(regfile: Module, solver: Solver):
	states = regfile.declare_states(solver, ['s1', 's2'])
	regfile.transition(solver, states)

	start, end = states[0], states[-1]

	# setup assumptions
	# assuming that i_rd_en is false
	solver.add(Not(start['i_rd_en']))

	# assert that memory does not change
	solver.add(Not(Equals(start['memory'], end['memory'])))


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
		# initial state:
		self.mod.initial(self.solver, states[0])
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

	def proof_transaction(self, trans: Transaction, always_incremental = False):
		assert self.active_trans is None
		self.active_trans = trans
		cycles = len(trans.proto)

		if not always_incremental:
			# 1.) attempt a full proof
			with Proof(f"transaction {trans.name} is correct", self, check=False, case_split=self.spec.case_split, print_time=True):
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
				with Proof(f"{trans.name}: {vcs[check_vcs]} ({cc} cycles)", self, case_split=self.spec.case_split, print_time=True):
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
		for name, expr in merge_dicts({arg.symbol_name(): arg for arg in trans.ret_args}, arch_outs).items():
			self.solver.add(equal(expr, sem_out[name]))

		# final arch state
		end_arch = self.map_arch_state("_read", end) if complete else {}

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

		prefix = rf'\(\(\(\|{self.mod.name}_n ([a-zA-Z_0-9\.]+)\|\s+([a-zA-Z_0-9\.]+)\)\s+'
		suffix = r'\)\)'
		bv_bool = '(#b[01]+|false|true)'
		re_signal = re.compile(prefix + bv_bool + suffix)
		re_trans = re.compile(f'\(\(([a-zA-Z_0-9\.]+)\s+' + bv_bool + suffix)

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
		res, model = self.solver.solve(filename=filename, get_model=True, get_values=read, case_split=proof.case_split, print_time=proof.print_time)
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
	def __init__(self, name: str, engine: ProofEngine, check = True, case_split=None, print_time=False):
		self.engine = engine
		self.name = name
		self.check = check
		self.case_split = case_split
		self.print_time = print_time
		self.ii = None
	def __enter__(self):
		self.ii = self.engine.start_proof(self)
		return self
	def __exit__(self, exc_type, exc_val, exc_tb):
		if exc_type is not None: return
		self.engine.run_proof(self)

