#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

import itertools

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




class Verifier:
	def __init__(self, mod: Module, prob: VerificationProblem, engine):
		check_verification_problem(prob, mod)
		self.prob = prob
		self.mod = mod
		self.engine = engine
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

		topgraph = to_veri_spec(self.mod, self.prob.spec)
		subgraphs = {nn: to_veri_spec(self.mod.submodules[nn], spec) for nn, spec in self.prob.submodules.items()}
		with BoundedCheck(f"module {self.mod.name} correct implements its spec", self, cycles=topgraph.max_k) as check:
			# test state encoding
			check.state(Symbol("test_state"), Symbol("test_state"))

			encode_toplevel_module(graph=topgraph, check=check, spec=self.prob.spec, mod=self.mod,
			                       invariances=self.prob.invariances, mappings=self.prob.mappings)
			for instance, spec in self.prob.submodules.items():
				encode_submodule(offset=0, instance=instance, graph=subgraphs[instance], check=check, spec=spec, mod=self.mod.submodules[instance])



def to_veri_spec(mod: RtlModule, spec: Spec) -> VeriSpec:
	# turn every individual transaction into a graph
	tran_graphs = [to_verification_graph(tran.proto, tran, mod) for tran in spec.transactions]
	spec_graph = tran_graphs[0]
	for other in tran_graphs[1:]:
		spec_graph = merge_constraint_graphs(spec_graph, other)
	# verify graph to check if it satisfies assumptions
	return check_verification_graph(spec_graph, io_prefix=mod.io_prefix)

def encode_submodule(offset: int, instance: str, graph: VeriSpec, check: BoundedCheck, spec: Spec, mod: RtlModule):
	final_states = encode_module(is_toplevel=False, offset=offset, prefix=f"{instance}.", graph=graph, check=check, spec=spec, mod=mod)

	assert len(final_states) > 0, f"found no final states!"
	# TODO: search for paths...


def encode_toplevel_module(graph: VeriSpec, check: BoundedCheck, spec: Spec, mod: RtlModule, invariances: List[SmtExpr], mappings: List[StateMapping]):
	# in the first state, we assume the invariances hold
	for inv in invariances:
		check.assume_at(0, inv)

	# in the initial state, the state mapping holds
	for mapping in mappings:
		check.assume_at(0, Equals(mapping.arch, mapping.impl))

	#
	final_states = encode_module(is_toplevel=True, offset=0, prefix="", graph=graph, check=check, spec=spec, mod=mod)

	for state in final_states:
		# in any final state, the invariances need to hold!
		for inv in invariances:
			check.assert_at(state.ii, Implies(state.guard, inv))
		# verify arch states after transaction
		arch_next = {Symbol(name, tpe): Symbol(f"{mod.name}.{name}_n", tpe) for name, tpe in spec.state.items()}
		for mapping in mappings:
			arch = substitute(mapping.arch, arch_next)
			check.assert_at(state.ii, Implies(state.guard, Equals(arch, mapping.impl)))

	# we have to explore at least one final state
	assert len(final_states) > 0, f"found no final states!"
	at_least_one = disjunction(*(st.guard for st in final_states))
	check.assert_at(graph.max_k-1, at_least_one)

def encode_module(is_toplevel: bool, offset: int, prefix: str, graph: VeriSpec, check: BoundedCheck, spec: Spec, mod: RtlModule) -> List[FinalState]:
	assert not is_toplevel or prefix == "", f"For the toplevel we expect an empty prefix, not {prefix}"

	module_prefix = prefix + mod.name + "."

	# generate variable mappings in case there is another prefix:
	# in general state variables are of the form: ModuleName.StateName
	# if we have multiple instances, we need to convert them to: InstanceName.ModuleName.StateName
	# a similar thing is true for arguments and return arguments
	if prefix == "":
		mapping = {}
	else:
		mapping = {Symbol(f"{mod.name}.{name}", tpe): Symbol(f"{prefix}{mod.name}.{name}", tpe) for name, tpe in spec.state.items()}
		for tran in spec.transactions:
			a_map = {Symbol(f"{mod.name}.{tran.name}.{name}", tpe): Symbol(f"{prefix}{mod.name}.{tran.name}.{name}", tpe)
					 for name, tpe in itertools.chain(tran.args.items(), tran.ret_args.items())}
			mapping = {**mapping, **a_map}

	# declare architectural state
	state_syms = make_symbols(spec.state, module_prefix)
	declare_constants(check, state_syms)

	# declare inputs and calculate semantics of every transaction
	for tran in spec.transactions:
		tran_prefix = f"{module_prefix}{tran.name}."
		arg_syms = make_symbols(tran.args, prefix=tran_prefix)
		declare_constants(check, arg_syms)

		# calculate semantics of this transaction
		for ret_name, ret_tpe in tran.ret_args.items():
			expr = tran.semantics[ret_name]
			check.function(Symbol(tran_prefix + ret_name, ret_tpe), substitute(expr, mapping))

		for state_name, state_tpe in spec.state.items():
			# keep state the same if no update specified
			prev_state = state_syms[state_name]
			next_state = tran.semantics.get(state_name, prev_state)
			check.function(Symbol(module_prefix + state_name + "_n", state_tpe), substitute(next_state, mapping))



	# encode graph
	final_states = VeriGraphToCheck(is_toplevel, offset, module_prefix, graph, check, get_inactive_reset(mod), mapping).convert()
	return final_states

@dataclass
class FinalState:
	guard: SmtExpr
	ii: int

SymMap = Dict[Symbol, Symbol]

class VeriGraphToCheck:
	def __init__(self, is_toplevel: bool, offset: int, prefix: str, graph: VeriSpec, check: BoundedCheck, inactive_rst: Optional[SmtExpr], var_sub: SymMap):
		assert graph.checked, f"Graph not checked! {graph}"
		self.offset = offset
		self.prefix = prefix
		self.check = check
		self.graph = graph
		self.inactive_rst = inactive_rst
		self.is_toplevel = is_toplevel
		self.final_states: List[FinalState] = []
		self.arg_sub = var_sub
		self.edge_symbols = {}

	def convert(self) -> List[FinalState]:
		self.visit_state(self.graph.start, TRUE(), self.offset)
		return self.final_states

	def assume_implies_at(self, ii: int, antecedent: SmtExpr, consequent: SmtExpr):
		self.check.assume_at(ii, Implies(antecedent, consequent))
	def assert_implies_at(self, ii: int, antecedent: SmtExpr, consequent: SmtExpr):
		self.check.assert_at(ii, Implies(antecedent, consequent))

	def visit_state(self, state: VeriState, guard: SmtExpr, ii: int):
		if ii >= self.check.cycles:
			return # incomplete

		if len(state.edges) == 0:
			self.final_states.append(FinalState(guard=guard, ii=ii))
			return

		##### constraints
		# input constraints
		I = [conjunction(*edge.constraints.input) for edge in state.edges]
		# argument mappings
		A = [substitute(conjunction(*edge.constraints.arg), self.arg_sub) for edge in state.edges]
		# output constraints
		O = [conjunction(*edge.constraints.output) for edge in state.edges]
		# return argument mappings
		R = [substitute(conjunction(*edge.constraints.ret_arg), self.arg_sub) for edge in state.edges]

		###########################################################################################
		# naive encoding (assuming all edges could have common inputs, but I/O is always exclusive)
		###########################################################################################

		# we need the reset to be inactive in every state
		if self.inactive_rst is not None:
			if self.is_toplevel: self.assume_implies_at(ii, guard, self.inactive_rst)
			else:                self.assert_implies_at(ii, guard, self.inactive_rst)

		if self.is_toplevel:
			# restrict inputs to any of the provided edges
			self.assume_implies_at(ii, guard, disjunction(*I))
		else:
			# make sure that the environment applies only allowed inputs
			self.assert_implies_at(ii, guard, disjunction(*I))

		# output requirements for any combination of active edges
		for bits in range(1 << len(state.edges)):
			active = [(bits & (1<<ii)) != 0 for ii in range(len(state.edges))]

			# TODO: check if antecedent is infeasible
			inputs = [I[ii] if active[ii] else Not(I[ii]) for ii in range(len(state.edges))]
			antecedent = And(guard, conjunction(*inputs))

			outputs = [O[ii] for ii in range(len(state.edges)) if active[ii]]
			consequent = disjunction(*outputs)

			if self.is_toplevel:
				# verify that output constraints are satisfied
				self.assert_implies_at(ii, antecedent, consequent)
			else:
				# assume that outputs are according to the constraints
				self.assume_implies_at(ii, antecedent, consequent)


		# path computation and argument mappings
		for ei, edge in enumerate(state.edges):
			# next guard (is this edge taken)?
			next_cond = And(guard, And(I[ei], O[ei]))

			# create edge symbol from edge name and prefix
			edge_name = self.graph.edge_id_to_name[id(edge)]
			edge_sym = Symbol(self.prefix + edge_name, BOOL)
			self.edge_symbols[id(edge)] = edge_sym
			self.check.constant(edge_sym)

			# assigning the path condition to the edge symbol always needs to be done by an "assume"
			self.check.assume_at(ii, Iff(edge_sym, next_cond))

			# argument mapping
			# the argument mapping is essentially just an assignment, giving a name to a prior input, thus it always needs an "assume"
			self.assume_implies_at(ii, edge_sym, A[ei])
			if self.is_toplevel:
				# verify that the output follows the transaction semantics
				self.assert_implies_at(ii, edge_sym, R[ei])
			else:
				# assume that the output will follow the transaction semantics
				self.assume_implies_at(ii, edge_sym, R[ei])

		# visit next states
		for edge in state.edges:
			self.visit_state(edge.next, self.edge_symbols[id(edge)], ii+1)