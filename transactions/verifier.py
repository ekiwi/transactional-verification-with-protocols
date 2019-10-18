#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import itertools
from pysmt.shortcuts import *
from .module import Module
from .utils import *
from .spec import Transaction, Spec
from .bounded import BoundedCheck

class Verifier:
	def __init__(self, mod: Module, spec: Spec, engine):
		self.mod = mod
		self.spec = spec
		self.engine = engine
		self.verbose = True

	def do_transaction(self, tran: Transaction, check: BoundedCheck, transaction_traces, assume_invariances=False, no_asserts=False):
		assert check.cycles == len(tran.proto), f"need to fully unroll transaction! {check.cycles} vs {len(tran.proto)}"

		# assume invariances hold at the beginning of the transaction
		if assume_invariances:
			for inv in self.spec.invariances:
				check.assume_at(0, inv(self.mod))

		# assume reset is inactive during the transaction
		if self.mod.reset is not None:
			check.assume_always(Not(self.mod[self.mod.reset]))

		# declare transaction args
		for arg in tran.args:
			check.constant(arg)

		# apply cycle behavior
		for ii, m in enumerate(tran.proto.mappings):
			for signal_name, expr in m.items():
				assert not self.mod.is_state(signal_name), f"protocols may only read/write from io: {signal_name}"

				if self.mod.is_output(signal_name):
					if not no_asserts:
						check.assert_at(ii, equal(self.mod[signal_name], expr))
				else:
					# if the signal is an input, we just apply the constraint for this cycle
					assert self.mod.is_input(signal_name)
					check.assume_at(ii, equal(self.mod[signal_name], expr))

		# apply cycle behavior of submodules
		sub_arch_state, sub_arch_state_n = {}, {}
		for name, mod in self.mod.submodules.items():
			trace = transaction_traces[tran.name][name]['trace']
			subspec = transaction_traces[tran.name][name]['spec']
			cycles = [0] + list(itertools.accumulate(len(tt.proto) for tt in trace))
			def make_state(pre, post=""): return { n: Symbol(pre + n + post, tpe) for n, tpe in subspec.arch_state.items() }
			arch_state_begin = make_state(f"__{name}_")
			arch_state_end = make_state(f"__{name}_", "_n")
			# start with start state + declare it as unconstrained symbolic input
			current_state = arch_state_begin
			for sym in current_state.values(): check.constant(sym)
			for ii, (start_cycle, subtran) in enumerate(zip(cycles, trace)):
				is_last = ii == len(trace) - 1
				prefix = f"__{name}_{ii}_{subtran.name}_"
				next_state = make_state(prefix) if not is_last else arch_state_end
				self.model_submodule_transaction(subtran, check, mod, start_cycle, prefix, current_state, next_state)
				current_state = next_state
			assert current_state == arch_state_end
			sub_arch_state[name] = arch_state_begin
			sub_arch_state_n[name] = arch_state_end

		return  sub_arch_state, sub_arch_state_n


	def model_submodule_transaction(self, tran: Transaction, check: BoundedCheck, submodule: Module, start_cycle: int, prefix: str, arch_in, arch_out):
		# declare arguments for this particular transaction
		args = { sym.symbol_name(): Symbol(prefix + sym.symbol_name(), sym.symbol_type()) for sym in tran.args }
		for sym in args.values(): check.constant(sym)

		# calculate semanitcs of this transaction
		sem_out = tran.semantics(**args, **arch_in)

		# declare return arguments as functions
		ret_args = { sym.symbol_name(): Symbol(prefix + sym.symbol_name(), sym.symbol_type()) for sym in tran.ret_args }
		for name, sym in ret_args.items():
			check.function(sym, sem_out[name])

		# declare next arch state as functions
		for name, sym in arch_out.items():
			check.function(sym, sem_out[name])

		# we need to rename references to the transaction arguments in the protocol mapping
		mappings = { sym: Symbol(prefix + sym.symbol_name(), sym.symbol_type()) for sym in itertools.chain(tran.args, tran.ret_args) }

		for ii, m in enumerate(tran.proto.mappings):
			for signal_name, expr in m.items():
				renamed_expr = substitute(expr, mappings)
				if submodule.is_output(signal_name):
					# we need to apply the output of the blackboxed submodule to the input of the module we are verifying
					check.assume_at(ii + start_cycle, equal(submodule[signal_name], renamed_expr))
				else:
					assert submodule.is_input(signal_name)
					# we just connect the inputs because we assume that they are correct
					check.assume_at(ii + start_cycle, equal(submodule[signal_name], renamed_expr))
		return start_cycle + len(tran.proto)

	def proof_transaction(self, tran: Transaction, transaction_traces):
		cycles = len(tran.proto)
		with BoundedCheck(f"transaction {tran.name} is correct", self, cycles=cycles) as check:
			# instantiate unrolled transaction
			sub_arch_state_index, sub_arch_state_n_index = self.do_transaction(
				tran=tran, transaction_traces=transaction_traces, assume_invariances=True, check=check)

			# native arch state tied to a physical state in the module
			arch_state = {name: Symbol(name, tpe) for name, tpe in self.spec.arch_state.items() if not isinstance(tpe, str)}
			arch_state_n = {name: Symbol(name + "_n", tpe) for name, tpe in self.spec.arch_state.items() if not isinstance(tpe, str)}
			# TODO: we could assign an initial value to the arch state that is derived from the initial circuit state
			for sym in arch_state.values():
				check.constant(sym)
			# submodule arch state
			def astate(tpe, index):
				instance, st = tpe.split(".")
				return index[instance][st]
			sub_arch_state   = {name: astate(tpe, sub_arch_state_index)   for name, tpe in self.spec.arch_state.items() if isinstance(tpe, str)}
			sub_arch_state_n = {name: astate(tpe, sub_arch_state_n_index) for name, tpe in self.spec.arch_state.items() if isinstance(tpe, str)}

			# connect initial circuit and arch state
			mapping_assumptions = self.spec.mapping(self.mod, **arch_state)
			for a in mapping_assumptions:
				check.assume_at(0, a)

			# semantics as pure function calculated during initialization
			def rename(symbols):
				return {sym.symbol_name(): sym for sym in symbols}
			args = rename(tran.args)
			# arg constants were already declared during unrolling
			sem_out = tran.semantics(**args, **arch_state, **sub_arch_state)
			ret_args = rename(tran.ret_args)
			for name, sym in itertools.chain(ret_args.items(), arch_state_n.items()):
				check.function(sym, sem_out[name])

			# verify arch states after transaction
			mapping_assertions = self.spec.mapping(self.mod, **arch_state_n)
			for a in mapping_assertions:
				check.assert_at(cycles, a)
			# verify submodule arch state equivalence
			for name, sym in sub_arch_state_n.items():
				check.assert_at(cycles, equal(sem_out[name], sym))

	def proof_transactions(self, transaction_traces):
		for trans in self.spec.transactions:
			self.proof_transaction(trans, transaction_traces)

	def proof_invariances(self, transaction_traces):
		invariances = [ii(self.mod) for ii in self.spec.invariances]

		for ii in invariances:
			with BoundedCheck(f"invariance holds after reset ({ii})", self, cycles=1) as check:
				# we assume that the reset comes after uploading the bit stream which initializes the registers + memory
				check.initialize_state()
				check.assume_at(0, self.mod[self.mod.reset])
				# invariance should hold after reset
				check.assert_at(1, ii)

		for tran in self.spec.transactions:
			cycles = len(tran.proto)
			with BoundedCheck(f"invariances are inductive over {tran.name} transaction", self, cycles=cycles) as check:
				self.do_transaction(tran=tran, check=check, transaction_traces=transaction_traces, assume_invariances=False, no_asserts=True)
				# assume this particular invariance
				for ii in invariances:
					check.assume_at(0, ii)
				# invariance should hold after transaction
				for ii in invariances:
					check.assert_at(cycles, ii)

	def check_transaction_trace_format(self, transaction_traces):
		# if there are no (blackboxed) submodules, there is no need for transaction traces
		if len(self.mod.submodules) == 0:
			return {}
		assert isinstance(transaction_traces, dict), f"Invalid instruction traces provided: {transaction_traces}"

		# check that for each transaction we have a set of traces
		for tran in self.spec.transactions:
			assert tran.name in transaction_traces, f"Missing transaction trace for {tran.name}: {list(transaction_traces.keys())}"
			traces = transaction_traces[tran.name]
			# check that for each balckboxed submodule we have a trace of the correct length
			for bb in self.mod.submodules.values():
				assert bb.name in traces, f"Missing transaction trace for {tran.name} for submodule {bb.name}"
				trace = traces[bb.name]['trace']
				trace_len = sum(len(tt.proto) for tt in trace)
				assert trace_len == len(tran.proto), f"Transaction trace for {tran.name} for submodule {bb.name} is {trace_len} cycles long, needs to be {len(tran.proto)}"
				spec = traces[bb.name]['spec']
				assert isinstance(spec, Spec), f"No valid spec provided!"
		return transaction_traces

	def proof_all(self, transaction_traces = None):
		transaction_traces = self.check_transaction_trace_format(transaction_traces)
		self.proof_invariances(transaction_traces)
		self.proof_transactions(transaction_traces)
