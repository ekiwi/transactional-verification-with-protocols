#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

import copy
import itertools
from pysmt.shortcuts import *
from .module import Module, LowActiveReset, HighActiveReset
from .utils import *
from .spec import *
from .spec_check import check_verification_problem, merge_indices
from .bounded import BoundedCheck
from .proto import VeriSpec, to_verification_graph, check_verification_graph, VeriState, VeriEdge, EdgeRelation
from typing import Iterable, Tuple, Union
from collections import defaultdict

def transaction_len(tran: Transaction) -> int:
	return len(tran.proto.transitions)

def transaction_trace_len(trace: List[Transaction]) -> int:
	return sum(transaction_len(tt) for tt in trace)

def print_traces(traces: Dict[str,List[Transaction]]):
	for ii, trace in traces.items():
		print(f"{ii:<10}: {[tt.name for tt in trace]}")

def get_inactive_reset(module: RtlModule) -> Optional[SmtExpr]:
	if module.reset is None: return None
	rst = Symbol(module.io_prefix + module.reset.name, BVType(1))
	if isinstance(module.reset, HighActiveReset):
		return Equals(rst, BV(0, 1))
	else:
		assert isinstance(module.reset, LowActiveReset)
		return Equals(rst, BV(1, 1))

def declare_constants(check: BoundedCheck, symbols: Dict[str, Symbol]):
	for sym in symbols.values(): check.constant(sym)

def make_symbols(symbols: Dict[str, SmtSort], prefix: str = "", suffix: str = "") -> Dict[str, Symbol]:
	return {name: Symbol(prefix + name + suffix, tpe) for name, tpe in symbols.items()}

def map_symbols(symbols: Dict[str, Symbol]) -> Dict[Symbol, Symbol]:
	return {Symbol(name, sym.symbol_type()): sym for name, sym in symbols.items()}

def apply_semantics(tran: Transaction, check: BoundedCheck, state: Dict[str, Symbol], prefix: str = ""):
	# the semantics operate on previous arch state and input args
	if len(prefix) > 0:
		args = make_symbols(tran.args, prefix)
		state_syms = make_symbols(state, prefix)
		mapping = map_symbols(merge_indices(args, state_syms))
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

def generate_outputs(tran: Transaction, module: RtlModule, state: Dict[str, SmtSort], check: BoundedCheck,
					 offset: int = 0,
					 prefix: str = "", assume_dont_assert_requirements: bool = True):
	""" generates output assumptions/assertions on module for offset..transaction_len(tran)+offset
		assumption: input args have been declared
	"""

	# declare architectural state input
	declare_constants(check, make_symbols(state, prefix))

	# calculate semantics of this transaction
	apply_semantics(tran, check, state, prefix)

	# we may need to rename references to the transaction arguments in the protocol mapping
	mappings = map_symbols(make_symbols(tran.ret_args, prefix))

	for ii, tt in enumerate(tran.proto.transitions):
		# stop generating inputs when we are at the end of the check
		if ii + offset > check.cycles: break
		# connect outputs
		for signal_name, expr in tt.outputs.items():
			sig = Symbol(module.io_prefix + signal_name, module.outputs[signal_name])
			expr = Equals(sig, substitute(expr, mappings))
			if assume_dont_assert_requirements:
				check.assume_at(ii + offset, expr)
			else:
				check.assert_at(ii + offset, expr)


def generate_inputs(tran: Transaction, module: RtlModule, check: BoundedCheck, offset: int = 0,
					prefix: str = "", assume_dont_assert_requirements: bool = False):
	""" generates input assumptions/assertions on module for offset..transaction_len(tran)+offset """

	# reset should be inactive during a transaction
	inactive_rst = get_inactive_reset(module)
	if inactive_rst is not None:
		for ii in range(transaction_len(tran)):
			# stop generating inputs when we are at the end of the check
			if ii + offset > check.cycles: break
			if assume_dont_assert_requirements:
				check.assume_at(ii + offset, inactive_rst)
			else:
				check.assert_at(ii + offset, inactive_rst)

	# variable -> interval -> (cycle, signal_expr)
	var2inputs: Dict[SmtExpr, Dict[Tuple[int, int], List[Tuple[int, SmtExpr]]]] = defaultdict(lambda: defaultdict(list))

	# find constant and variable mapping on the protocol inputs
	for ii, tt in enumerate(tran.proto.transitions):
		# stop generating inputs when we are at the end of the check
		if ii + offset > check.cycles: break
		for signal_name, expr in tt.inputs.items():
			sig = Symbol(module.io_prefix + signal_name, module.inputs[signal_name])
			for (signal_msb, signal_lsb, (var_msb, var_lsb, var)) in FindVariableIntervals.find(expr):
				is_full = signal_lsb == 0 and signal_msb + 1 == sig.symbol_type().width
				if is_full:
					sig_expr = sig
				else:
					sig_expr = BVExtract(sig, start=signal_lsb, end=signal_msb)
				if var.is_symbol():
					var2inputs[var][(var_msb, var_lsb)].append((ii + offset, sig_expr))
				else:
					assert var_lsb == 0 and var_msb + 1 == var.get_type().width, f"Expect constants to be simplified!"
					# check that the input has the correct constant value in cycle ii+offset
					if assume_dont_assert_requirements:
						check.assume_at(ii + offset, Equals(sig_expr, var))
					else:
						check.assert_at(ii + offset, Equals(sig_expr, var))

	# make sure that all arguments of the transaction are defined in the protocol
	for name, tpe in tran.args.items():
		if Symbol(name, tpe) not in var2inputs:
			# TODO: uncomment
			#print(f"WARN: in transaction {tran.name}: argument {name} is not defined by the protocol. Will be random!")
			check.constant(Symbol(prefix + name, tpe))

	# declare protocol arguments and their restrictions
	for var, refs in var2inputs.items():
		# check that there are no overlapping intervals as they aren't supported yet
		covered_bits = set()
		for (msb, lsb) in refs.keys():
			for bit in range(lsb, msb + 1):
				assert bit not in covered_bits, f"Overlapping intervals on {var}[{bit}]"
				covered_bits.add(bit)

		# check that all bits are defined
		for bit in range(var.symbol_type().width):
			if bit not in covered_bits:
				# TODO: uncomment
				#print(f"WARN: in transaction {tran.name}: argument bit {var}[{bit}] is not defined by the protocol.")
				pass

		# generate input constant
		var_sym = Symbol(prefix + var.symbol_name(), var.symbol_type())
		check.constant(var_sym)

		# generate conditions for each interval
		for ((msb, lsb), mappings) in refs.items():
			assert len(mappings) > 0
			full_range = msb + 1 == var.symbol_type().width and lsb == 0

			# find (one of) the first references to this interval
			mappings_sorted_by_cycle = sorted(mappings, key=lambda ii: ii[0])
			start = mappings_sorted_by_cycle[0]

			# we bind the start mapping to a constant and then check every other mapping against the constant
			if full_range:
				constant = var_sym
			else:
				constant = BVExtract(var_sym, start=lsb, end=msb)

			# map the constant to the input variable symbol
			check.assume_at(start[0], Equals(constant, start[1]))
			for cycle, expr in mappings_sorted_by_cycle[1:]:
				if assume_dont_assert_requirements:
					check.assume_at(cycle, Equals(expr, constant))
				else:
					check.assert_at(cycle, Equals(expr, constant))


def do_transaction(tran: Transaction, check: BoundedCheck, traces: Dict[str, List[Transaction]],
				   invariances: List[SmtExpr], mod: RtlModule, subspecs: Dict[str, Spec],
				   allow_incomplete: bool = False):
	""" (symbolically) execute a transaction of the module being verified  """
	assert check.cycles > 0, f"Zero cycle checks are not supported!"
	if not allow_incomplete:
		assert check.cycles == transaction_len(tran), f"need to fully unroll transaction! {check.cycles} vs {transaction_len(tran)}"

	# assume invariances hold at the beginning of the transaction
	for inv in invariances:
		check.assume_at(0, inv)

	# assume the environment applies the correct inputs to the toplevel module
	generate_inputs(tran, mod, check, assume_dont_assert_requirements=True)

	# apply cycle behavior of submodules
	sub_arch_state_n = {}
	for instance, subspec in subspecs.items():
		subtrace = traces[instance]
		submodule = mod.submodules[instance]

		# declare architectural state at the beginning and at the end of the toplevel transaction
		arch_state_begin = make_symbols(subspec.state, instance + ".")
		declare_constants(check, arch_state_begin)
		arch_state_end = make_symbols(subspec.state, instance + ".", "_n")
		declare_constants(check, arch_state_end)
		sub_arch_state_n = {**sub_arch_state_n, **{instance + "." + name: sym for name, sym in arch_state_end.items()}}

		# start with start state
		current_state = arch_state_begin

		offsets = [0] + list(itertools.accumulate(transaction_len(tt) for tt in subtrace))
		for ii, (offset, subtran) in enumerate(zip(offsets, subtrace)):
			prefix = f"{instance}.{subtran.name}.{offset}."
			# check that toplevel module applies valid inputs to the submodule
			generate_inputs(subtran, submodule, check, offset, prefix, assume_dont_assert_requirements=False)
			# assume that the submodule generates the correct outputs (this is ok because we assume no combinatorial loops)
			generate_outputs(subtran, submodule, subspec.state, check, offset, prefix, assume_dont_assert_requirements=True)
			# connect input state
			for name, sym in current_state.items():
				check.assume_always(Equals(Symbol(prefix+name, sym.symbol_type()), sym))
			# remember output state
			current_state = make_symbols(subspec.state, prefix, "_n")

		# connect output state
		for name, sym in arch_state_end.items():
			check.assume_always(Equals(sym, current_state[name]))

	return sub_arch_state_n

class Verifier:
	def __init__(self, mod: Module, prob: VerificationProblem, engine):
		check_verification_problem(prob, mod)
		self.prob = prob
		self.mod = mod
		self.engine = engine
		self.topgraph = to_veri_spec(self.mod, self.prob.spec)
		self.verbose = True

	def verify_inductive_base_case(self):
		""" prove that the invariances hold after reset """
		if len(self.prob.invariances) == 0: return
		reset_active = Not(get_inactive_reset(self.mod))
		assert reset_active is not None, f"Cannot prove any invariances if there is not reset. ({self.mod.name})"
		with BoundedCheck(f"invariances on state in {self.prob.implementation} hold after reset ", self, cycles=1) as check:
			# we assume that the reset comes after uploading the bit stream which initializes the registers + memory
			check.initialize_state()
			check.assume_at(0, reset_active)
			# all invariances should hold after reset
			for ii in self.prob.invariances:
				check.assert_at(1, ii)

	def find_transaction_trace(self, tran: Transaction, subspecs: Dict[str, Spec]) -> Dict[str, List[Transaction]]:
		raise NotImplementedError()

	def verify_transaction_trace_format(self, tran: Transaction, trace: Dict[str, List[Transaction]]):
		raise NotImplementedError()

	def verify_transaction(self, tran: Transaction, traces: Dict[str, List[Transaction]]):
		""" checks that the transaction output and the input to subtransactions is correct """
		cycles = transaction_len(tran)
		with BoundedCheck(f"transaction {tran.name} is correct", self, cycles=cycles) as check:
			# instantiate unrolled transaction
			subarch_n = do_transaction(tran=tran,traces=traces, check=check, invariances=self.prob.invariances,
			                           mod=self.mod, subspecs=self.prob.submodules)

			# verify that the outputs are correct
			generate_outputs(tran, self.mod, self.prob.spec.state, check, assume_dont_assert_requirements=False)

			# connect initial circuit and arch state
			for mapping in self.prob.mappings:
				check.assume_at(0, Equals(mapping.arch, mapping.impl))

			# verify arch states after transaction
			arch_next = {Symbol(name, tpe): Symbol(name + "_n", tpe) for name, tpe in self.prob.spec.state.items()}
			subarch_next = {Symbol(name, sym.symbol_type()): sym for name, sym in subarch_n.items()}
			for mapping in self.prob.mappings:
				arch = substitute(mapping.arch, arch_next)
				impl = substitute(mapping.impl, subarch_next)
				check.assert_at(cycles, Equals(arch, impl))

	def verify_inductive_step(self, tran: Transaction, traces: Dict[str, List[Transaction]]):
		""" checks that the the invariants are inductive over transaction tran """
		raise NotImplementedError()



	def proof_all(self):
		self.verify_inductive_base_case()

		with BoundedCheck(f"module {self.mod.name} correct implements its spec", self, cycles=self.topgraph.max_k) as check:
			encode_veri_graph(self.prob.spec, self.topgraph, check, self.prob.invariances)



		#for tran in self.prob.spec.transactions:
			#traces = self.find_transaction_trace(tran, self.prob.submodules)
			#self.verify_transaction_trace_format(tran, traces)
			#self.verify_transaction(tran, traces)
			#self.verify_inductive_step(tran, traces)


def to_veri_spec(mod: RtlModule, spec: Spec) -> VeriSpec:
	# turn every individual transaction into a graph
	tran_graphs = [to_verification_graph(tran.proto, tran, mod, "") for tran in spec.transactions]
	if len(tran_graphs) > 1:
		raise NotImplementedError("TODO: implement graph merging!")
	else:
		spec_graph = tran_graphs[0]
	# verify graph to check if it satisfies assumptions
	return check_verification_graph(spec_graph)

def encode_veri_graph(spec: Spec, graph: VeriSpec, check: BoundedCheck, invariances: List[SmtExpr]):
	return VeriGraphToCheck().convert(spec, graph, check, invariances)

class VeriGraphToCheck:
	offset: int = 0
	check: BoundedCheck = None
	spec: Spec = None
	graph: VeriSpec = None
	invariances: List[SmtExpr] = field(default_factory=list)
	final_states: List[Symbol] = field(default_factory=list)


	def convert(self, spec: Spec, graph: VeriSpec, check: BoundedCheck, invariances: List[SmtExpr]):
		assert graph.checked, f"Graph not checked! {graph}"
		self.offset = 0
		self.spec = spec
		self.check = check
		self.graph = graph
		self.invariances = invariances
		self.final_states = []

		# declare all semantics
		# TODO: generalize
		assert len(spec.state) == 0, f"{spec}"
		for tran in spec.transactions:
			for arg_name, arg_tpe in tran.args.items():
				self.check.constant(Symbol(arg_name, arg_tpe))
			for ret_name, ret_tpe in tran.ret_args.items():
				expr = tran.semantics[ret_name]
				check.function(Symbol(ret_name, ret_tpe), expr)

		# explore graph
		self.visit_state(graph.start, TRUE())

		# we have to explore at least one final state
		at_least_one = disjunction(*self.final_states)
		self.check.assert_at(self.graph.max_k-1, at_least_one)

	def visit_state(self, state: VeriState, guard: SmtExpr):
		if len(state.edges) == 0:
			return
		ii = state.edges[0].ii + self.offset
		if ii >= self.check.cycles:
			return # incomplete

		if ii == self.offset:
			# in the first state, we assume the invariances
			for inv in self.invariances:
				self.check.assume_at(ii, inv)

		if len(state.edges) == 0:
			# finaly state!
			if ii == self.offset:
				# in any final state, the invariances need to hold!
				for inv in self.invariances:
					self.check.assert_at(ii, inv)
			self.final_states.append(guard)

		##### constraints
		# input constraints
		I = [conjunction(*edge.constraints.input) for edge in state.edges]
		# argument mappings
		A = [conjunction(*edge.constraints.arg) for edge in state.edges]
		# output constraints
		O = [conjunction(*edge.constraints.output) for edge in state.edges]
		# return argument mappings
		R = [conjunction(*edge.constraints.ret_arg) for edge in state.edges]

		###########################################################################################
		# naive encoding (assuming all edges could have common inputs, but I/O is always exclusive)
		###########################################################################################

		# restrict inputs to any of the provided edges
		input_assumption = Implies(guard, disjunction(*I))
		self.check.assume_at(ii, input_assumption)

		# output requirements for any combination of active edges
		for bits in range(1 << len(state.edges)):
			active = [(bits & (1<<ii)) != 0 for ii in range(len(state.edges))]

			# TODO: check if antecedent is infeasible
			inputs = [I[ii] if active[ii] else Not(I[ii]) for ii in range(len(state.edges))]
			antecedent = And(guard, conjunction(*inputs))

			outputs = [O[ii] for ii in range(len(state.edges)) if active[ii]]
			consequent = disjunction(*outputs)

			self.check.assert_at(ii, Implies(antecedent, consequent))

		# path computation and argument mappings
		for ei, edge in enumerate(state.edges):
			# next guard (is this edge taken)?
			next_cond = And(guard, And(I[ei], O[ei]))
			edge_sym = self.graph.edge_symbols[id(edge)]
			self.check.constant(edge_sym)
			self.check.assume_at(ii, Iff(edge_sym, next_cond))
			# argument mapping
			self.check.assume_at(ii, Implies(next_cond, A[ei]))
			self.check.assert_at(ii, Implies(next_cond, R[ei]))

		# visit next states
		for edge in state.edges:
			self.visit_state(edge.next, self.graph.edge_symbols[id(edge)])


class FindVariableIntervals:
	@staticmethod
	def find(expr: SmtExpr):
		raise NotImplementedError("Old Code")