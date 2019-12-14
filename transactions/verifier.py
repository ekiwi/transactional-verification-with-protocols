#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

import collections
import itertools

from pysmt.shortcuts import *
from typing import Tuple
from .module import Module, LowActiveReset, HighActiveReset
from .utils import *
from .spec import *
from .spec_check import check_verification_problem, merge_indices
from .bounded import BoundedCheck
from .proto import VeriSpec, to_verification_graph, check_verification_graph, VeriState, merge_constraint_graphs, \
	VeriEdge, add_idle_edge


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
			check.state(Symbol("test_state", BVType()), Symbol("test_state", BVType()), BV(0,32))

			encode_toplevel_module(graph=topgraph, check=check, spec=self.prob.spec, mod=self.mod,
			                       invariances=self.prob.invariances, mappings=self.prob.mappings)
			for instance, spec in self.prob.submodules.items():
				encode_submodule(instance=instance, graph=subgraphs[instance], check=check, spec=spec, mod=self.mod.submodules[instance])



def to_veri_spec(mod: RtlModule, spec: Spec) -> VeriSpec:
	# turn every individual transaction into a graph
	tran_graphs = [to_verification_graph(tran.proto, tran, mod) for tran in spec.transactions]
	spec_graph = tran_graphs[0]
	for other in tran_graphs[1:]:
		spec_graph = merge_constraint_graphs(spec_graph, other)
	# verify graph to check if it satisfies assumptions
	return check_verification_graph(spec_graph, io_prefix=mod.io_prefix)


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
		arch_next = {Symbol(f"{mod.name}.{name}", tpe): Symbol(f"{mod.name}.{name}_n", tpe) for name, tpe in spec.state.items()}
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
		if len(state.edges) == 0:
			self.final_states.append(FinalState(guard=guard, ii=ii))
			return

		if ii >= self.check.cycles:
			return # incomplete

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


def encode_submodule(instance: str, graph: VeriSpec, check: BoundedCheck, spec: Spec, mod: RtlModule):
	idle_tran = Transaction("IDLE")
	idle_edge = to_verification_graph(spec.idle, tran=idle_tran, mod=mod).start.edges[0]
	graph = add_idle_edge(graph, idle_edge)
	# TODO: recheck the graph after adding idle edge since the add_idle_edge implementation is probbably buggy
	VeriGraphToModel(instance, mod.name, graph, check, get_inactive_reset(mod), spec.transactions).convert()


@dataclass
class VariableMapping:
	name: str
	msb: int
	lsb: int
	mappings: List[int] = field(default_factory=list)

class VeriGraphToModel:
	def __init__(self, instance: str, mod_name: str, graph: VeriSpec, check: BoundedCheck, inactive_rst: Optional[SmtExpr], transactions: List[Transaction], arch_state: Dict[str, SmtSort]):
		assert graph.checked, f"Graph not checked! {graph}"
		self.instance = instance
		self.mod_name = mod_name
		self.check = check
		self.graph = graph
		self.inactive_rst = inactive_rst
		self.final_states: List[FinalState] = []
		self.edge_symbols = {}
		self.states: List[str] = ["Init"]
		self.transitions: List[Tuple[SmtExpr, int]] = []
		self.var_maps: Dict[str, VariableMapping] = {}
		self.state = Symbol(f"{self.instance}.{self.mod_name}.state", BVType(16))
		self.mappings: Dict[Tuple[str,int,int],List[Tuple[SmtExpr, SmtExpr]]] = collections.defaultdict(list)
		self.transactions = {tt.name: tt for tt in transactions}
		self.input_subs: Dict[Symbol, Symbol] = {}
		self.arch_state = arch_state
		self.arch_state_updates: Dict[str, List[Tuple[SmtExpr, SmtExpr]]] = collections.defaultdict(list)
		for tran in transactions:
			for name, tpe in tran.args.items():
				full_name = f"{mod_name}.{tran.name}.{name}"
				self.input_subs[Symbol(full_name, tpe)] = self.get_var(full_name)

	def convert(self) -> List[FinalState]:
		self.visit_state(self.graph.start, Equals(self.state, BV(0, 16)))

		# implement state transitions
		invalid_state = BV((1<<16)-1, 16)
		state_next = invalid_state
		for guard, state_id in self.transitions: state_next = Ite(guard, BV(state_id, 16), state_next)
		self.check.state(self.state, state_next, init_expr=BV(0,16))

		# check if transaction done
		transaction_done = disjunction(*(tt[0] for tt in self.transitions if tt[1] == 0))

		# implement variable mappings
		for (name, msb, lsb), mappings in self.mappings.items():
			assert len(mappings) > 0, f"{name}[{msb}:{lsb}] was never mapped!"
			sym = Symbol(f"{self.instance}.{name}_{msb}_{lsb}", BVType(msb-lsb+1))
			expr_next = sym
			for guard, value in mappings: expr_next = Ite(guard, value, expr_next)
			self.check.state(sym, expr_next)
			sym_valid = Symbol(sym.symbol_name() + "_valid", BOOL)
			expr_next_valid = And(disjunction(sym_valid, *(g for g,_ in mappings)), Not(transaction_done))
			self.check.state(sym_valid, expr_next_valid, init_expr=FALSE())
			# TODO: invalidate when transitioning back to initial state

		return self.final_states

	def get_var(self, name: str):
		assert len(self.graph.intervals[name]) > 0, f"No intervals for {name}"
		intervals = sorted(self.graph.intervals[name], key=lambda x: x[0])
		pieces = [Symbol(f"{self.instance}.{name}_{msb}_{lsb}", BVType(msb - lsb + 1)) for msb, lsb in intervals]
		assert len(pieces) == len(self.graph.intervals[name])
		return reduce(BVConcat, pieces)


	def get_var_at(self, name: str, edge: VeriEdge) -> SmtExpr:
		assert len(self.graph.intervals[name]) > 0, f"No intervals for {name}"
		# sort by msb (bigger first)
		intervals = sorted(self.graph.intervals[name], key=lambda x: x[0])
		pieces = []
		for msb, lsb in intervals:
			try:
				# this will fail if the argument is not mapped at the current edge
				mapping = next(filter(lambda a: a.name == name and a.msb == msb and a.lsb == lsb, edge.arg_mappings))
				pieces.append(mapping.expr)
			except:
				pieces.append(Symbol(f"{self.instance}.{name}_{msb}_{lsb}", BVType(msb-lsb+1)))
		assert len(pieces) == len(self.graph.intervals[name])
		return reduce(BVConcat, pieces)

	def compute_outputs(self, tran: Transaction, edge: VeriEdge) -> Dict[Symbol, SmtExpr]:
		tran_prefix = f"{self.mod_name}.{tran.name}."
		# TODO: include arch state state
		subs = {Symbol(tran_prefix+name,tpe): self.get_var_at(tran_prefix+name, edge) for name, tpe in tran.args.items()}
		return {Symbol(tran_prefix+name,tpe): substitute(tran.semantics[name],subs) for name, tpe in tran.ret_args.items()}


	def visit_state(self, state: VeriState, guard: SmtExpr):
		if len(state.edges) == 0:
			return

		##### constraints
		# input constraints
		I = [substitute(conjunction(*edge.constraints.input), self.input_subs) for edge in state.edges]
		# output constraints
		O = [conjunction(*edge.constraints.output) for edge in state.edges]

		###########################################################################################
		# naive encoding (assuming all edges could have common inputs, but I/O is always exclusive)
		###########################################################################################

		# make sure that the environment applies only allowed inputs
		self.check.assert_always(Implies(guard, disjunction(*I)))

		# output requirements for any combination of active edges
		for bits in range(1 << len(state.edges)):
			active = [(bits & (1<<ii)) != 0 for ii in range(len(state.edges))]

			# TODO: check if antecedent is infeasible
			inputs = [I[ii] if active[ii] else Not(I[ii]) for ii in range(len(state.edges))]
			antecedent = And(guard, conjunction(*inputs))

			outputs = [O[ii] for ii in range(len(state.edges)) if active[ii]]
			consequent = disjunction(*outputs)

			# TODO: State -> I... -> O.. vc. State and I... -> O...
			self.check.assume_always(Implies(And(guard, antecedent), consequent))


		# path computation and argument mappings
		for ei, edge in enumerate(state.edges):
			# next guard (is this edge taken)?
			next_cond = And(guard, And(I[ei], O[ei]))
			if len(edge.next.edges) == 0:
				next_state = 0
			else:
				next_state = len(self.states)
				self.states.append('') # TODO: name
			self.transitions.append((next_cond, next_state))

			# argument mapping
			for m in edge.arg_mappings:
				self.mappings[(m.name, m.msb, m.lsb)].append((next_cond, m.expr))

			# assume that the output will follow the transaction semantics
			if len(edge.constraints.ret_arg) > 0:
				assert len(edge.transactions) == 1, f"{edge.transactions}"
				tran_name = list(edge.transactions)[0]
				outputs = self.compute_outputs(tran=self.transactions[tran_name], edge=edge)
				R = substitute(conjunction(*edge.constraints.ret_arg), outputs)
				self.check.assume_always(Implies(next_cond, R))

			# if this is the last edge => update architectural state
			if next_state == 0 and len(self.arch_state) > 0:
				assert len(edge.transactions) == 1, f"{edge.transactions}"
				tran = self.transactions[list(edge.transactions)[0]]
				for name, tpe in self.arch_state.items():
					if name in tran.semantics:



			# visit next states
			self.visit_state(edge.next, Equals(self.state, BV(next_state, 16)))