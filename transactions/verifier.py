#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import itertools
from pysmt.shortcuts import *
from .module import Module, LowActiveReset, HighActiveReset
from .utils import *
from .spec import *
from .spec_check import check_verification_problem, merge_indices
from .bounded import BoundedCheck
from typing import Iterable, Tuple, Union
from itertools import chain
from collections import defaultdict

def transaction_len(tran: Transaction):
	return len(tran.proto.transitions)

class Verifier:
	def __init__(self, mod: Module, prob: VerificationProblem, engine):
		check_verification_problem(prob, mod)
		self.prob = prob
		self.mod = mod
		self.engine = engine
		self.verbose = True

	def reset_active(self):
		if self.mod.reset is not None:
			rst = Symbol(self.mod.reset.name, BVType(1))
			if isinstance(self.mod.reset, HighActiveReset):
				return Equals(rst, BV(1,1))
			else:
				assert isinstance(self.mod.reset, LowActiveReset)
				return Equals(rst, BV(0,1))

	@staticmethod
	def declare_constants(check: BoundedCheck, symbols: Dict[str, Symbol]):
		for sym in symbols.values(): check.constant(sym)

	@staticmethod
	def make_symbols(symbols: Dict[str, SmtSort], prefix: str = "", suffix: str = "") -> Dict[str, Symbol]:
		return {name: Symbol(prefix + name + suffix, tpe) for name, tpe in symbols.items()}

	@staticmethod
	def map_symbols(symbols: Dict[str, Symbol]) -> Dict[Symbol, Symbol]:
		return {Symbol(name, sym.symbol_type()): sym for name, sym in symbols.items()}

	def do_transaction(self, tran: Transaction, check: BoundedCheck, trace: Dict[str, List[Transaction]], no_asserts=False):
		""" (symbolically) execute a transaction of the module being verified  """
		assert check.cycles == transaction_len(tran), f"need to fully unroll transaction! {check.cycles} vs {transaction_len(tran)}"

		# assume invariances hold at the beginning of the transaction
		for inv in self.prob.invariances:
			check.assume_at(0, inv)

		# assume reset is inactive during the transaction
		check.assume_always(Not(self.reset_active()))

		# declare transaction args
		self.declare_constants(check, self.make_symbols(tran.args))

		# apply cycle behavior
		for ii, tt in enumerate(tran.proto.transitions):
			# apply inputs
			for signal_name, expr in tt.inputs.items():
				check.assume_at(ii, Equals(Symbol(signal_name, self.mod.inputs[signal_name]), expr))
			# check outputs
			if not no_asserts:
				for signal_name, expr in tt.outputs.items():
					check.assert_at(ii, Equals(Symbol(signal_name, self.mod.outputs[signal_name]), expr))

		# apply cycle behavior of submodules
		sub_arch_state_n = {}
		for instance, subspec in self.prob.submodules.items():
			subtrace = trace[instance]
			submodule = self.mod.submodules[instance]

			# declare architectural state at the beginning and at the end of the toplevel transaction
			arch_state_begin = self.make_symbols(subspec.state, instance + ".")
			self.declare_constants(check, arch_state_begin)
			arch_state_end = self.make_symbols(subspec.state, instance + ".", "_n")
			self.declare_constants(check, arch_state_end)
			sub_arch_state_n = {**sub_arch_state_n, **{instance + "." + name: sym for name, sym in arch_state_end.items()}}

			# start with start state
			current_state = arch_state_begin

			offsets = [0] + list(itertools.accumulate(transaction_len(tt) for tt in subtrace))
			for ii, (start_cycle, subtran) in enumerate(zip(offsets, subtrace)):
				# execute subtransaction
				prefix = f"{instance}.{subtran.name}.{start_cycle}."
				self.model_submodule_transaction(subtran, check, submodule, subspec.state, start_cycle, prefix)

				# connect input state
				for name, sym in current_state.items():
					check.assume_always(Equals(Symbol(prefix+name, sym.symbol_type()), sym))
				# remember output state
				current_state = self.make_symbols(subspec.state, prefix, "_n")

			# connect output state
			for name, sym in arch_state_end.items():
				check.assume_always(Equals(sym, current_state[name]))

		return sub_arch_state_n

	def apply_semantics(self, tran: Transaction, check: BoundedCheck, state: Dict[str, Symbol], prefix: str = ""):
		# the semantics operate on previous arch state and input args
		if len(prefix) > 0:
			args = self.make_symbols(tran.args, prefix)
			state_syms = self.make_symbols(state, prefix)
			mapping = self.map_symbols(merge_indices(args, state_syms))
		else:
			mapping = {}
		# semantics as next state function for spec state and outputs
		for ret_name, ret_tpe in tran.ret_args.items():
			expr = tran.semantics[ret_name]
			check.function(Symbol(prefix + ret_name, ret_tpe), substitute(expr, mapping))
		for state_name, state_tpe in state.items():
			# keep state the same if no update specified
			prev_state = Symbol(state_name, state_tpe)
			next_state = tran.semantics.get(state_name, prev_state)
			check.function(Symbol(prefix + state_name + "_n", state_tpe), substitute(next_state, mapping))

	def model_submodule_transaction(self, tran: Transaction, check: BoundedCheck, submodule: RtlModule, state: Dict[str, SmtSort], start_cycle: int, prefix: str):
		# declare arguments for this particular transaction
		args = self.make_symbols(tran.args, prefix)
		self.declare_constants(check, args)

		# declare architectural state input
		self.declare_constants(check, self.make_symbols(state, prefix))

		# calculate semantics of this transaction
		self.apply_semantics(tran, check, state, prefix)

		# we need to rename references to the transaction arguments in the protocol mapping
		ret_args = self.make_symbols(tran.ret_args, prefix)
		mappings = self.map_symbols(merge_indices(args, ret_args))

		for ii, tt in enumerate(tran.proto.transitions):
			# connect inputs
			for signal_name, expr in tt.inputs.items():
				sig = Symbol(submodule.io_prefix + signal_name, submodule.inputs[signal_name])
				check.assume_at(start_cycle + ii, Equals(sig, substitute(expr, mappings)))
			# connect outputs
			for signal_name, expr in tt.outputs.items():
				sig = Symbol(submodule.io_prefix + signal_name, submodule.outputs[signal_name])
				check.assume_at(start_cycle + ii, Equals(sig, substitute(expr, mappings)))

		return start_cycle + transaction_len(tran)


	def verify_inductive_base_case(self):
		""" prove that the invariances hold after reset """
		with BoundedCheck(f"invariances on state in {self.prob.implementation} hold after reset ", self, cycles=1) as check:
			# we assume that the reset comes after uploading the bit stream which initializes the registers + memory
			check.initialize_state()
			check.assume_at(0, self.reset_active())
			# all invariances should hold after reset
			for ii in self.prob.invariances:
				check.assert_at(1, ii)

	def find_transaction_trace(self, tran: Transaction) -> Dict[str, List[Transaction]]:
		if len(self.prob.submodules) == 0: return {}
		# TODO: actually discover traces
		assert set(self.prob.submodules.keys()) == {'regfile', 'alu'}, f"{list(self.prob.submodules.keys())}"
		rr = {tt.name: tt for tt in self.prob.submodules['regfile'].transactions}
		aa = {tt.name: tt for tt in self.prob.submodules['alu'].transactions}
		if tran.name == 'Idle':
			return {'regfile': [rr['Idle']], 'alu': [aa['Idle']]}
		elif tran.name == 'Add':
			return {
				'regfile': [rr[n] for n in ['RW', 'Idle']],
				'alu': [aa[n] for n in ['Idle', 'Idle', 'Add', 'Idle']]
			}
		else:
			assert False, f"Unknown transaction {tran.name}"

	def verify_transaction_trace_format(self, tran: Transaction, trace: Dict[str, List[Transaction]]):
		# check that for each blackboxed submodule we have a trace of the correct length
		for name, spec in self.prob.submodules.items():
			assert name in trace, f"Missing transaction trace for {tran.name} for submodule {name}"
			trace_len = sum(transaction_len(tt) for tt in trace[name])
			assert trace_len == transaction_len(tran), f"Transaction trace for {tran.name} for submodule {name} is {trace_len} cycles long, needs to be {transaction_len(tran)}"
			for subtran in trace[name]:
				assert subtran in spec.transactions, f"Subtransaction {subtran.name} is not part of the spec for {name}"

	def generate_input_conditions(self, tran: Transaction, offset: int = 0):
		var_finder = FindVariableIntervals()
		var2inputs = defaultdict(list)
		for ii, tt in enumerate(tran.proto.transitions):
			for signal_name, expr in tt.inputs.items():
				findings = var_finder.walk(expr)
				for (signal_msb, signal_lsb, (var_msb, var_lsb, var)) in findings:
					if var.is_symbol():
						var2inputs[var].append((ii+offset, (signal_name, signal_msb, signal_lsb), (var_msb, var_lsb)))

		print(var2inputs)


	def verify_transaction_trace(self, tran: Transaction, traces: Dict[str, List[Transaction]]):
		""" ensures that the transaction trace selected is the only feasible one """
		if len(self.prob.submodules) == 0:
			assert len(traces) == 0, f"Did not expect a trace: {traces}"
			return
		self.verify_transaction_trace_format(tran, traces)
		print("WARN: transaction traces are currently NOT verified! FIXME!")
		# TODO: check that module reset is never active!

		for instance, trace in  traces.items():
			offsets = [0] + list(itertools.accumulate(transaction_len(tt) for tt in trace))
			for ii, (start_cycle, tran) in enumerate(zip(offsets, trace)):
				self.generate_input_conditions(tran, offset=start_cycle)


	def verify_transaction_output(self, tran: Transaction, trace: Dict[str, List[Transaction]]):
		""" checks that the transaction output is correct """
		cycles = transaction_len(tran)
		with BoundedCheck(f"transaction {tran.name} is correct", self, cycles=cycles) as check:
			# instantiate unrolled transaction
			subarch_n = self.do_transaction(tran=tran,trace=trace, check=check)

			# declare architectural state input
			for state_name, state_tpe in self.prob.spec.state.items():
				check.constant(Symbol(state_name, state_tpe))

			# connect initial circuit and arch state
			for mapping in self.prob.mappings:
				check.assume_at(0, Equals(mapping.arch, mapping.impl))

			# semantics as next state function for spec state and outputs
			self.apply_semantics(tran, check, self.prob.spec.state)

			# verify arch states after transaction
			arch_next = {Symbol(name, tpe): Symbol(name + "_n", tpe) for name, tpe in self.prob.spec.state.items()}
			subarch_next = {Symbol(name, sym.symbol_type()): sym for name, sym in subarch_n.items()}
			for mapping in self.prob.mappings:
				arch = substitute(mapping.arch, arch_next)
				impl = substitute(mapping.impl, subarch_next)
				check.assert_at(cycles, Equals(arch, impl))

	def verify_inductive_step(self, tran: Transaction, trace: Dict[str, List[Transaction]]):
		""" checks that the the invariants are inductive over transaction tran """
		cycles = transaction_len(tran)
		with BoundedCheck(f"invariances are inductive over {tran.name} transaction", self, cycles=cycles) as check:
			self.do_transaction(tran=tran, check=check, trace=trace, no_asserts=True)
			# all invariances should hold after the transaction
			for ii in self.prob.invariances:
				check.assert_at(cycles, ii)

	def proof_all(self):
		self.verify_inductive_base_case()
		for tran in self.prob.spec.transactions:
			trace = self.find_transaction_trace(tran)
			self.verify_transaction_trace(tran, trace)
			self.verify_transaction_output(tran, trace)
			self.verify_inductive_step(tran, trace)

from pysmt.walkers import DagWalker

class FindVariableIntervals(DagWalker):
	def __init__(self, env=None):
		super().__init__(env)
	def bits(self, formula): return formula.get_type().width
	def walk(self, formula, **kwargs):
		res = super().walk(formula, **kwargs)
		assert not isinstance(res, list), "TODO: deal with concats"
		return [(self.bits(formula)-1, 0, res)]
	def walk_bv_concat(self, formula, args, **kwargs):
		return ((args[0] if isinstance(args[0], list) else [args[0]]) +
		        (args[1] if isinstance(args[1], list) else [args[1]]))
	def walk_bv_extract(self, formula, args, **kwargs):
		lo = formula.bv_extract_start()
		hi = formula.bv_extract_end()
		assert len(args) == 1
		old_hi, old_lo, name = args[0]
		a = (hi + old_lo, lo + old_lo, name)
		assert a[0] - a[1] == self.bits(formula) - 1
		return a
	def walk_array_select(self, formula, args, **kwargs):
		raise NotImplementedError("TODO: support array select")
	def walk_bv_constant(self, formula, **kwargs): return (self.bits(formula)-1, 0, formula)
	def walk_symbol(self, formula, **kwargs): return (self.bits(formula)-1, 0, formula)