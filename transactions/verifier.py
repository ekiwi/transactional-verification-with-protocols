#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

from pysmt.shortcuts import *
from .module import Module, LowActiveReset, HighActiveReset
from .utils import *
from .spec import *
from .spec_check import check_verification_problem, merge_indices
from .bounded import BoundedCheck
from .proto import VeriSpec, to_verification_graph, check_verification_graph, VeriState, merge_constraint_graphs

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

	def proof_all(self):
		self.verify_inductive_base_case()

		with BoundedCheck(f"module {self.mod.name} correct implements its spec", self, cycles=self.topgraph.max_k) as check:
			# reset should be inactive during a transaction
			inactive_rst = get_inactive_reset(self.mod)
			if inactive_rst is not None:
				check.assume_always(inactive_rst)
			encode_veri_graph(self.prob.spec, self.topgraph, check, self.prob.invariances, self.prob.mappings)



		#for tran in self.prob.spec.transactions:
			#traces = self.find_transaction_trace(tran, self.prob.submodules)
			#self.verify_transaction_trace_format(tran, traces)
			#self.verify_transaction(tran, traces)
			#self.verify_inductive_step(tran, traces)


def to_veri_spec(mod: RtlModule, spec: Spec) -> VeriSpec:
	# turn every individual transaction into a graph
	tran_graphs = [to_verification_graph(tran.proto, tran, mod, "") for tran in spec.transactions]
	spec_graph = tran_graphs[0]
	for other in tran_graphs[1:]:
		spec_graph = merge_constraint_graphs(spec_graph, other)
	# verify graph to check if it satisfies assumptions
	return check_verification_graph(spec_graph)

def encode_veri_graph(spec: Spec, graph: VeriSpec, check: BoundedCheck, invariances: List[SmtExpr], mappings: List[StateMapping]):
	return VeriGraphToCheck().convert(spec, graph, check, invariances, mappings)

class VeriGraphToCheck:
	offset: int = 0
	check: BoundedCheck = None
	spec: Spec = None
	graph: VeriSpec = None
	invariances: List[SmtExpr] = field(default_factory=list)
	mappings: List[StateMapping] = field(default_factory=list)
	final_states: List[Symbol] = field(default_factory=list)


	def convert(self, spec: Spec, graph: VeriSpec, check: BoundedCheck, invariances: List[SmtExpr], mappings: List[StateMapping]):
		assert graph.checked, f"Graph not checked! {graph}"
		self.offset = 0
		self.spec = spec
		self.check = check
		self.graph = graph
		self.invariances = invariances
		self.mappings = mappings
		self.final_states = []

		# declare all semantics
		# TODO: generalize

		# declare architectural state input
		prefix = ""
		declare_constants(check, make_symbols(self.spec.state, prefix))
		for tran in spec.transactions:
			declare_constants(check, make_symbols(tran.args, prefix=f"{tran.name}."))
			# calculate semantics of this transaction
			apply_semantics(tran, check, self.spec.state, prefix=f"{tran.name}.")

		# explore graph
		self.visit_state(graph.start, TRUE(), self.offset)

		# we have to explore at least one final state
		assert len(self.final_states) > 0, f"found not final states!"
		at_least_one = disjunction(*self.final_states)
		self.check.assert_at(self.graph.max_k-1, at_least_one)

	def assume_implies_at(self, ii: int, antecedent: SmtExpr, consequent: SmtExpr):
		if consequent == TRUE(): return
		self.check.assume_at(ii, Implies(antecedent, consequent))
	def assert_implies_at(self, ii: int, antecedent: SmtExpr, consequent: SmtExpr):
		if consequent == TRUE(): return
		self.check.assert_at(ii, Implies(antecedent, consequent))

	def visit_initial_state(self, ii: int):
		# in the first state, we assume the invariances
		for inv in self.invariances:
			self.check.assume_at(ii, inv)

		# connect initial circuit and arch state
		for mapping in self.mappings:
			# TODO: this does not really work for offset != 0
			self.check.assume_at(ii, Equals(mapping.arch, mapping.impl))

	def visit_final_state(self, guard: SmtExpr, ii: int):
		# in any final state, the invariances need to hold!
		for inv in self.invariances:
			self.assert_implies_at(ii, guard, inv)
		self.final_states.append(guard)

		# verify arch states after transaction
		arch_next = {Symbol(name, tpe): Symbol(name + "_n", tpe) for name, tpe in self.spec.state.items()}
		for mapping in self.mappings:
			arch = substitute(mapping.arch, arch_next)
			self.assert_implies_at(ii, guard, Equals(arch, mapping.impl))

	def visit_state(self, state: VeriState, guard: SmtExpr, ii: int):
		if ii >= self.check.cycles:
			return # incomplete

		if ii == self.offset:
			self.visit_initial_state(ii)

		if len(state.edges) == 0:
			return self.visit_final_state(guard, ii)

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
		self.assume_implies_at(ii, guard, disjunction(*I))

		# output requirements for any combination of active edges
		for bits in range(1 << len(state.edges)):
			active = [(bits & (1<<ii)) != 0 for ii in range(len(state.edges))]

			# TODO: check if antecedent is infeasible
			inputs = [I[ii] if active[ii] else Not(I[ii]) for ii in range(len(state.edges))]
			antecedent = And(guard, conjunction(*inputs))

			outputs = [O[ii] for ii in range(len(state.edges)) if active[ii]]
			consequent = disjunction(*outputs)

			self.assert_implies_at(ii, antecedent, consequent)

		# path computation and argument mappings
		for ei, edge in enumerate(state.edges):
			# next guard (is this edge taken)?
			next_cond = And(guard, And(I[ei], O[ei]))
			edge_sym = self.graph.edge_symbols[id(edge)]
			self.check.constant(edge_sym)
			self.check.assume_at(ii, Iff(edge_sym, next_cond))
			# argument mapping
			self.assume_implies_at(ii, edge_sym, A[ei])
			self.assert_implies_at(ii, edge_sym, R[ei])

		# visit next states
		for edge in state.edges:
			self.visit_state(edge.next, self.graph.edge_symbols[id(edge)], ii+1)