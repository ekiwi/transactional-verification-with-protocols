#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import itertools
from pysmt.shortcuts import *
from .module import Module, LowActiveReset, HighActiveReset
from .utils import *
from .spec import *
from .spec_check import check_verification_problem
from .bounded import BoundedCheck

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

	def do_transaction(self, tran: Transaction, check: BoundedCheck, trace: Dict[str, List[Transaction]], no_asserts=False):
		""" (symbolically) execute a transaction of the module being verified  """
		assert check.cycles == transaction_len(tran), f"need to fully unroll transaction! {check.cycles} vs {transaction_len(tran)}"

		# assume invariances hold at the beginning of the transaction
		for inv in self.prob.invariances:
			check.assume_at(0, inv)

		# assume reset is inactive during the transaction
		check.assume_always(Not(self.reset_active()))

		# declare transaction args
		for instance, tpe in tran.args.items():
			check.constant(Symbol(instance, tpe))

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
		sub_arch_state, sub_arch_state_n = {}, {}
		for instance, subspec in self.prob.submodules.items():
			trace = transaction_traces[tran.name][instance]['trace']
			cycles = [0] + list(itertools.accumulate(len(tt.proto) for tt in trace))
			def make_state(pre, post=""): return { n: Symbol(pre + n + post, tpe) for n, tpe in subspec.state.items() }
			arch_state_begin = make_state(f"__{instance}_")
			arch_state_end = make_state(f"__{instance}_", "_n")
			# start with start state + declare it as unconstrained symbolic input
			current_state = arch_state_begin
			for sym in current_state.values(): check.constant(sym)
			for ii, (start_cycle, subtran) in enumerate(zip(cycles, trace)):
				is_last = ii == len(trace) - 1
				prefix = f"__{instance}_{ii}_{subtran.name}_"
				next_state = make_state(prefix) if not is_last else arch_state_end
				self.model_submodule_transaction(subtran, check, mod, start_cycle, prefix, current_state, next_state)
				current_state = next_state
			assert current_state == arch_state_end
			sub_arch_state[instance] = arch_state_begin
			sub_arch_state_n[instance] = arch_state_end

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


	def proof_invariances(self):
		for ii in self.prob.invariances:
			with BoundedCheck(f"invariance holds after reset ({ii})", self, cycles=1) as check:
				# we assume that the reset comes after uploading the bit stream which initializes the registers + memory
				check.initialize_state()
				check.assume_at(0, self.reset_active())
				# invariance should hold after reset
				check.assert_at(1, ii)

		for tran in self.prob.spec.transactions:
			cycles = transaction_len(tran)
			with BoundedCheck(f"invariances are inductive over {tran.name} transaction", self, cycles=cycles) as check:
				self.do_transaction(tran=tran, check=check, assume_invariances=False, no_asserts=True)
				# assume this particular invariance
				for ii in self.prob.invariances:
					check.assume_at(0, ii)
				# invariance should hold after transaction
				for ii in self.prob.invariances:
					check.assert_at(cycles, ii)

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
		assert set(self.prob.submodules.keys()) == {'regfile', 'add'}, f"{list(self.prob.submodules.keys())}"
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

	def verify_transaction_trace(self, tran: Transaction, trace: Dict[str, List[Transaction]]):
		""" ensures that the transaction trace selected is the only feasible one """
		if len(self.prob.submodules) == 0:
			assert len(trace) == 0, f"Did not expect a trace: {trace}"
			return
		self.verify_transaction_trace_format(tran, trace)
		raise NotImplementedError("TODO")


	def verify_transaction_output(self, tran: Transaction, trace: Dict[str, List[Transaction]]):
		""" checks that the transaction output is correct """
		cycles = transaction_len(tran)
		with BoundedCheck(f"transaction {tran.name} is correct", self, cycles=cycles) as check:
			# instantiate unrolled transaction
			sub_arch_state_index, sub_arch_state_n_index = self.do_transaction(tran=tran,trace=trace, check=check)

			# declare architectural state input
			for state_name, state_tpe in self.prob.spec.state.items():
				check.constant(Symbol(state_name, state_tpe))

			# connect initial circuit and arch state
			for mapping in self.prob.mappings:
				check.assume_at(0, Equals(mapping.arch, mapping.impl))

			# submodule arch state
			# def astate(tpe, index):
			#	instance, st = tpe.split(".")
			#	return index[instance][st]
			# sub_arch_state   = {name: astate(tpe, sub_arch_state_index)   for name, tpe in self.prob.spec.state.items() }
			# sub_arch_state_n = {name: astate(tpe, sub_arch_state_n_index) for name, tpe in self.prob.spec.state.items() }

			# semantics as next state function for spec state and outputs
			for ret_name, ret_tpe in tran.ret_args.items():
				expr = tran.semantics[ret_name]
				check.function(Symbol(ret_name, ret_tpe), expr)
			for state_name, state_tpe in self.prob.spec.state.items():
				# keep state the same if no update specified
				prev_state = Symbol(state_name, state_tpe)
				next_state = tran.semantics.get(state_name, prev_state)
				check.function(Symbol(state_name + "_n", state_tpe), next_state)

			# verify arch states after transaction
			arch_next = {Symbol(name, tpe): Symbol(name + "_n", tpe) for name, tpe in self.prob.spec.state.items()}
			for mapping in self.prob.mappings:
				arch = substitute(mapping.arch, arch_next)
				check.assert_at(cycles, Equals(arch, mapping.impl))

	# verify submodule arch state equivalence
	# for name, sym in sub_arch_state_n.items():
	#	check.assert_at(cycles, equal(sem_out[name], sym))

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
