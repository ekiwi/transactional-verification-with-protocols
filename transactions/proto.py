#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

import collections
import itertools

from .spec import *
from dataclasses import dataclass, replace
from .smt2 import is_unsat
from pysmt.shortcuts import Symbol, And, BV, BVType, BVExtract, Equals, substitute, BOOL, Not, Iff, Implies
from .utils import conjunction, disjunction
from typing import Set, Union, Iterator, Tuple
import copy
from enum import Enum

def make_symbols(symbols: Dict[str, SmtSort], prefix: str = "", suffix: str = "") -> Dict[str, Symbol]:
	return {name: Symbol(prefix + name + suffix, tpe) for name, tpe in symbols.items()}

@dataclass
class ConstraintCache:
	""" generates and caches cycle specific constraints (e.g. (done = 1), 2 --> (done@2 = 1) """
	inputs: Dict[str, SmtSort]
	outputs: Dict[str, SmtSort]
	_substitution_cache: Dict[int, Tuple[Dict[Symbol, Symbol], Dict[Symbol, Symbol]]] = field(default_factory=dict)
	_constraint_cache: Dict[int, EdgeConstraints] = field(default_factory=dict)
	def _get_substitution(self, cycle: int) -> Tuple[Dict[Symbol, Symbol], Dict[Symbol, Symbol]]:
		if cycle not in self._substitution_cache:
			sub_i = {Symbol(name, typ): Symbol(f"{name}@{cycle}", typ) for name, typ in self.inputs.items()}
			sub_o = {Symbol(name, typ): Symbol(f"{name}@{cycle}", typ) for name, typ in self.outputs.items()}
			self._substitution_cache[cycle] = (sub_i, sub_o)
		return self._substitution_cache[cycle]

	@staticmethod
	def _substitute(constraints: List[SmtExpr], sub):
		return [substitute(f, sub) for f in constraints]

	def get(self, edge: VeriEdge):
		# convert "time-less" i/o constraints/mappings into cycle unique symbols
		# e.g.: `(done = 1)` --> `(done@1 = 1)`
		if id(edge) not in self._constraint_cache:
			sub_i, sub_o = self._get_substitution(edge.ii)
			self._constraint_cache[id(edge)] = EdgeConstraints(
				input=self._substitute(edge.constraints.input, sub_i),
				output=self._substitute(edge.constraints.output, sub_o),
				arg=self._substitute(edge.constraints.arg, sub_i),
				ret_arg=self._substitute(edge.constraints.ret_arg, sub_o)
			)
		return self._constraint_cache[id(edge)]

###################### IDLE Edge Addition
def add_idle_edge(g0: VeriSpec, idle: VeriEdge) -> VeriSpec:
	return VeriGraphIdleAdder().add_idle(g0, idle)


@dataclass
class VeriGraphIdleAdder:
	_constraints : ConstraintCache = None
	idle: VeriEdge = None

	def add_idle(self, g0: VeriSpec, idle: VeriEdge) -> VeriSpec:
		assert len(idle.constraints.ret_arg) == 0
		assert len(idle.constraints.arg) == 0
		assert idle.ii == 0
		self._constraints = ConstraintCache(g0.inputs, g0.outputs)
		self.idle = idle
		self.visit_state(g0.start)
		return g0


	def visit_state(self, s0: VeriState):
		if len(s0.edges) == 0: return
		idle = replace(self.idle, ii=s0.edges[0].ii)

		# see which edges could alias with an idle transaction
		idle_in  = conjunction(*self._constraints.get(idle).input)
		idle_out = conjunction(*self._constraints.get(idle).output)
		for edge in  s0.edges:
			edge_in  = conjunction(*self._constraints.get(edge).input)
			edge_out = conjunction(*self._constraints.get(edge).output)
			edge_implies_idle = Implies(And(edge_in, edge_out), And(idle_in, idle_out))
			if is_unsat(Not(edge_implies_idle)):
				self.visit_state(edge.next)

		# add an edge to the current state
		not_others = Not(disjunction(*(conjunction(*e.constraints.input) for e in s0.edges)))
		new_idle_const = And(conjunction(*self.idle.constraints.input), not_others)
		idle = replace(idle,
					   constraints=EdgeConstraints(input=[new_idle_const],output=self.idle.constraints.output, arg=[], ret_arg=[]),
					   next=VeriState(edges=[], transactions={}))
		s0.edges.append(idle)


###################### Constraint Graph Merging
def merge_constraint_graphs(g0: VeriSpec, g1: VeriSpec) -> VeriSpec:
	return VeriGraphMerger().merge(g0, g1)


@dataclass
class VeriGraphMerger:
	_constraints : ConstraintCache = None

	def merge(self, g0: VeriSpec, g1: VeriSpec) -> VeriSpec:
		assert g0.inputs == g1.inputs
		assert g0.outputs == g1.outputs
		assert g0.io_prefix == g1.io_prefix
		self._constraints = ConstraintCache(g0.inputs, g1.outputs)
		path_constraints: List[SmtExpr] = []
		start = self.merge_states(g0.start, g1.start, path_constraints)
		tts = {**g0.transactions, **g1.transactions}
		return VeriSpec(inputs=g0.inputs, outputs=g0.outputs, io_prefix=g0.io_prefix, checked=False, start=start, transactions=tts,
						intervals={**g0.intervals, **g1.intervals})


	def merge_states(self, s0: VeriState, s1: VeriState, path_constraints: List[SmtExpr]) -> VeriState:
		#ii = s0.edges[0].ii
		#print(f"Trying to merge @ {ii}: s0({s0.transactions} and s1({s1.transactions})")
		new_state = VeriState([], {})
		new_state.transactions = s0.transactions | s1.transactions
		new_state.edges = copy.copy(s0.edges)

		for e1 in s1.edges:
			e1_constraints = self._constraints.get(e1)
			merged = False
			for e0 in new_state.edges:
				e0_constraints = self._constraints.get(e0)
				exclusive = is_unsat(conjunction(*(#path_constraints + # TODO: do we need path constraints? why? why not?
									 e0_constraints.input + e0_constraints.output +
									 e1_constraints.input + e1_constraints.output)))
				if exclusive: continue
				same = is_unsat(Not(And(
					Iff(conjunction(*e0_constraints.input),  conjunction(*e1_constraints.input)),
					Iff(conjunction(*e0_constraints.output), conjunction(* e1_constraints.output)))))
				if same:
					assert len(e0.constraints.arg) == 0 and len(e1.constraints.arg) == 0, f"TODO: implement merging for edges that have variable mappings"
					next_state = self.merge_states(e0.next, e1.next, path_constraints + e0_constraints.input + e0_constraints.output)
					# replace e0 with merged edge
					new_state.edges.remove(e0)
					new_state.edges.append(replace(e0, next=next_state))
					merged = True
					break
				assert same | exclusive, f"Edges {e0} and {e1} are not the same but also not mutually exclusive. Merge failed!"
			# add new mutually exclusive edge
			if not merged:
				new_state.edges.append(e1)

		return new_state




###################### Constraint Graph Verification + Meta Data Generator

class EdgeRelation(Enum):
	InputExclusive = 1 # (forall) I_0 & I_1 = 0
	IOExclusive = 2    # (forall) I_0 & O_0 & I_1 & O_1 = 0
	CommonIOTrace = 3

def compare_edges(path_constraints: List[SmtExpr], a: EdgeConstraints, b: EdgeConstraints) -> EdgeRelation:
	# if there does *not* exist an I/O trace such that both edges input constraints are satisfied
	input_exclusive = path_constraints + a.input + b.input
	if is_unsat(input_exclusive):
		return EdgeRelation.InputExclusive
	# if there does *not* exist an I/O trace such that both edges I/O constraints are satisfied
	io_exclusive = input_exclusive + a.output + b.output
	if is_unsat(io_exclusive):
		return EdgeRelation.IOExclusive
	# else, there is a concrete I/O trace that matches both edges
	return EdgeRelation.CommonIOTrace

@dataclass
class VeriGraphChecker:
	_edge_relations: Dict[Tuple[int, int], EdgeRelation] = field(default_factory=dict)
	_max_k: int = 0
	_edge_names: Dict[str, int] = field(default_factory=dict)
	_constraints : ConstraintCache = None

	def get_unique_edge_name(self, ii:int) -> str:
		prefix = f"edge@{ii}"
		name = prefix
		suffix = 0
		while name in self._edge_names:
			name = f"{prefix}_{suffix}"
			suffix += 1
		return name

	def check(self, graph: VeriSpec, io_prefix: str) -> Tuple[Dict[Tuple[int, int], EdgeRelation], int, Dict[str, int]]:
		self._constraints = ConstraintCache(graph.inputs, graph.outputs)
		path_constraints: List[SmtExpr] = []
		self.visit_state(graph.start, path_constraints)
		return self._edge_relations, self._max_k, self._edge_names

	def visit_state(self, state: VeriState, path_constraints: List[SmtExpr]):
		for edge in state.edges:
			edge_constraints = self._constraints.get(edge)
			# check relationship with other edges
			for other in state.edges:
				if id(edge) == id(other): continue
				relation = compare_edges(path_constraints, edge_constraints, self._constraints.get(other))
				assert relation != EdgeRelation.CommonIOTrace, f"Edges with a common IO-trace are not supported by out model checking algorithm!" \
															   f"Maybe reshape the graph. {edge} vs {other}"
				# remember relationship
				self._edge_relations[(id(edge), id(other))] = relation
				self._edge_relations[(id(other), id(edge))] = relation
			self.visit_edge(edge, path_constraints)

	def visit_edge(self, edge: VeriEdge, path_constraints: List[SmtExpr]):
		assert edge.next is not None and isinstance(edge.next, VeriState)
		assert len(edge.next.transactions) > 0, f"No transactions @ {edge}"
		# if multiple transactions could be active on this edge, then we don't support mapping variables yet...
		# TODO: revisit this
		if len(edge.next.transactions) > 1:
			assert len(edge.constraints.arg) == 0, f"Cannot map arguments while multiple transactions could be active!" \
											       f"{edge.constraints.arg} @ {[tt.name for tt in edge.next.transactions]}"
			assert len(edge.constraints.ret_arg) == 0, f"Cannot map arguments while multiple transactions could be active!" \
											           f"{edge.constraints.ret_arg} @ {[tt.name for tt in edge.next.transactions]}"
		#
		self._max_k = max(self._max_k, edge.ii+1)
		# create an edge symbol
		self._edge_names[self.get_unique_edge_name(edge.ii)] = id(edge)
		#
		cc = self._constraints.get(edge)
		self.visit_state(edge.next, path_constraints + cc.input + cc.arg + cc.output + cc.ret_arg)

def check_verification_graph(graph: VeriSpec, io_prefix: str) -> VeriSpec:
	edge_relations, max_k, edge_name_to_id = VeriGraphChecker().check(graph, io_prefix)
	edge_id_to_name = {ii: name for name, ii in edge_name_to_id.items()}
	return replace(graph, checked=True, edge_relations=edge_relations, max_k=max_k, edge_name_to_id=edge_name_to_id, edge_id_to_name=edge_id_to_name)

##### Verification Protocol
@dataclass
class VeriState:
	edges: List[VeriEdge]
	transactions: Set[str]

@dataclass
class ArgMapping:
	name: str
	msb: int
	lsb: int
	expr: SmtExpr

@dataclass
class VeriEdge:
	ii: int
	# constraints of the form: `(done = 1)`
	constraints: EdgeConstraints
	arg_mappings: List[ArgMapping] = field(default_factory=list)
	next: Optional[VeriState] = None
	def __str__(self):
		return f"Edge(ii={self.ii}, constraints={self.constraints}, next=State(transactions={self.next.transactions}, degree={len(self.next.edges)})"

@dataclass
class EdgeConstraints:
	input: List[SmtExpr]
	output: List[SmtExpr]
	arg: List[SmtExpr]
	ret_arg: List[SmtExpr]

@dataclass
class VeriSpec:
	start: VeriState
	inputs: Dict[str, SmtSort]
	outputs: Dict[str, SmtSort]
	io_prefix: str
	transactions: Dict[str, Transaction]
	max_k: int = 0
	checked : bool = False
	edge_relations: Dict[Tuple[int, int], EdgeRelation] =  field(default_factory=dict)
	edge_id_to_name: Dict[int, str] = field(default_factory=dict)
	edge_name_to_id: Dict[str, int] = field(default_factory=dict)
	# var_name -> List[(msb,lsb)]
	intervals: Dict[str,List[Tuple[int, int]]] = field(default_factory=dict)



###################### Protocol to Constraint Graph

def extract_if_not_redundant(expr: SmtExpr, msb: int, lsb: int) -> SmtExpr:
	assert expr.get_type().is_bv_type(), f"{expr} : {expr.get_type()}"
	assert msb >= lsb >= 0, f"Failed: {msb} >= {lsb} >= 0"
	is_full = lsb == 0 and msb + 1 == expr.get_type().width
	if is_full: return expr
	else:       return BVExtract(expr, start=lsb, end=msb)

def range_to_bitmap(msb: int, lsb: int) -> int:
	assert msb >= lsb >= 0, f"Failed: {msb} >= {lsb} >= 0"
	width = msb - lsb + 1
	mask = (1 << width) - 1
	return mask << lsb

def find_constraints_and_mappings(io_prefix: str, signals: Dict[str, SmtExpr], var_map: Dict[str, int])\
		-> Tuple[List[SmtExpr], List[SmtExpr], Dict[str, int], List[Tuple[str, int, int, SmtExpr]]]:
	""" works for input or output signals """

	constraints: List[SmtExpr] = []
	mappings: List[SmtExpr] = []
	new_var_map = copy.copy(var_map)
	new_mappings: List[Tuple[str, int, int, SmtExpr]] = []

	for signal_name, expr in signals.items():
		assert expr.get_type().is_bv_type(), f"{expr} : {expr.get_type()}"

		expr_width = expr.get_type().width
		sig = Symbol(io_prefix + signal_name, BVType(expr_width))

		# iterate over all "bit-bindings" in the expression
		# this assumes that all the expression does is map signal bits to a constant or a variable bit
		# something like: Cat(v0[2:1], 0b00, v1[3:1])
		for (signal_msb, signal_lsb, (var_msb, var_lsb, var)) in FindVariableIntervals.find(expr):

			sig_expr = extract_if_not_redundant(sig, msb=signal_msb, lsb= signal_lsb)

			# if this is a mapping to bits of a variable
			if var.is_symbol():
				var_name = var.symbol_name()
				assert var_name in var_map, f"Unexpected variable: {var} in {signal_name} = {expr}. Expecteds variables are: {list(var_map.keys())}"
				var_expr = extract_if_not_redundant(var, msb=var_msb, lsb=var_lsb)

				current_bits = range_to_bitmap(var_msb, var_lsb)
				existing_bits = var_map[var_name]

				# update new variable mapping
				new_var_map[var_name] = existing_bits | current_bits

				if current_bits & existing_bits == 0:
					# these bits have never been mapped before => generate new mapping
					mappings.append(Equals(sig_expr, var_expr))
					new_mappings.append((var_name, var_msb, var_lsb, sig_expr))
				elif current_bits & existing_bits == current_bits:
					# all current bits have been mapped before => just enforce equality
					constraints.append(Equals(sig_expr, var_expr))
				else:
					# if some bits have been mapped before and others are new, we give up
					# (the solution would be to identify intervals that are mapped/not mapped and
					#  generate multiple constraints/ mappings)
					assert False, f"Overlapping bit mappings are not supported: {current_bits} & {existing_bits} = {current_bits & existing_bits}. In: {signal_name} = {expr}"

			# if this is a mapping to a constant
			else:
				assert var_lsb == 0 and var_msb + 1 == var.get_type().width, f"Expect constants to be simplified!"
				constraints.append(Equals(sig_expr, var))

	return constraints, mappings, new_var_map, new_mappings

def check_arg_map(args: Dict[str, SmtSort], arg_map: Dict[str, int], path: str, prefix: str):
	for name_suffix, typ in args.items():
		name = prefix + name_suffix
		assert name in arg_map, f"Argument {name} : {typ} missing in path: {path}"
		assert typ.is_bv_type()
		full = range_to_bitmap(typ.width - 1, 0)
		assert arg_map[name] == full, f"Bits missing from {name}: {arg_map[name]} != {full} in path: {path}"

@dataclass
class ProtocolToVerificationGraphConverter:
	io_prefix: str = ""
	arg_prefix: str = ""
	tran: Transaction = None
	# var_name -> List[(msb,lsb)]
	intervals: Dict[str,List[Tuple[int, int]]] = field(default_factory=lambda: collections.defaultdict(list))
	def convert(self, proto: Protocol, tran: Transaction, io_prefix: str, mod_name: str) -> Tuple[VeriState, Dict[str,List[Tuple[int, int]]]]:
		self.io_prefix = io_prefix
		self.arg_prefix = f"{mod_name}.{tran.name}."
		self.tran = tran
		arg_map     = {self.arg_prefix + name: 0 for name in tran.args.keys()}
		ret_arg_map = {self.arg_prefix + name: 0 for name in tran.ret_args.keys()}
		start = self.visit_state([], arg_map, ret_arg_map, proto.start)
		return start, self.intervals

	def visit_edge(self, prefix: List[VeriEdge], arg_map: Dict[str, int], ret_arg_map: Dict[str, int], edge: ProtocolEdge) -> VeriEdge:
		# the current transition id is the prefix length
		ii = len(prefix)

		input_constraints,  input_mappings, new_arg_map, new_mappings  = find_constraints_and_mappings(self.io_prefix, edge.inputs, arg_map)
		output_constraints, output_mappings, new_ret_arg_map, _ = find_constraints_and_mappings(self.io_prefix, edge.outputs, ret_arg_map)
		constraints = EdgeConstraints(input_constraints, output_constraints, input_mappings, output_mappings)

		for name, msb, lsb, expr in new_mappings:
			self.intervals[name].append((msb,lsb))
		arg_mappings = [ArgMapping(name=name, msb=msb, lsb=lsb, expr=expr) for name,msb,lsb,expr in new_mappings]

		new_edge = VeriEdge(ii, constraints, arg_mappings=arg_mappings)

		#print("Edge @ ", ii, input_constraints, input_mappings, output_constraints, output_mappings)
		new_edge.next = self.visit_state(prefix + [new_edge], new_arg_map, new_ret_arg_map, edge.next)
		return new_edge

	def visit_state(self, prefix: List[VeriEdge], arg_map: Dict[str, int], ret_arg_map: Dict[str, int], state: ProtocolState) -> VeriState:
		new_state = VeriState([], transactions={self.tran.name})
		for edge in state.edges:
			new_edge = self.visit_edge(prefix, arg_map, ret_arg_map, edge)
			new_state.edges.append(new_edge)
		if len(state.edges) == 0:
			self.check_path(prefix, arg_map, ret_arg_map)
		return new_state

	def check_path(self, path: List[VeriEdge], arg_map: Dict[str, int], ret_arg_map: Dict[str, int]):
		# check to make sure all input and output arguments of the transactions are mapped to module I/Os
		# TODO: there might be legit use cases for not mapping all outputs (maybe even inputs)
		check_arg_map(self.tran.args, arg_map, str(path), self.arg_prefix)
		check_arg_map(self.tran.ret_args, ret_arg_map, str(path), self.arg_prefix)


def to_verification_graph(proto: Protocol, tran: Transaction, mod: RtlModule) -> VeriSpec:
	start, intervals = ProtocolToVerificationGraphConverter().convert(proto, tran, mod.io_prefix, mod.name)
	tts = {tran.name: tran}
	inputs = {mod.io_prefix+name: tpe for name, tpe in mod.inputs.items()}
	outputs = {mod.io_prefix + name: tpe for name, tpe in mod.inputs.items()}
	return VeriSpec(start=start, io_prefix=mod.io_prefix, inputs=inputs, outputs=outputs, transactions=tts,intervals=intervals)



###################### Protocol Builder Code
@dataclass
class DontCareClass:
	pass
DontCare = DontCareClass()

ValueTypes = Union[bool, int, SmtExpr, DontCareClass]

def protocol_edges(proto: Protocol) -> Iterator[ProtocolEdge]:
	""" returns iterator of edges in protocol, only works if protocol is a tree! """
	states: List[ProtocolState] = [proto.start]
	while len(states) > 0:
		s = states.pop()
		for ed in s.edges:
			assert isinstance(ed, ProtocolEdge), f"{ed} in {s}"
			yield ed
			states.append(ed.next)

@dataclass
class OutputSignal:
	name: str
	parent: ProtocolBuilder
	def expect(self, value:ValueTypes):
		self.parent._expect(self.name, value)
	def wait(self, value: ValueTypes, max: int):
		self.parent._wait(self.name, value, max)

def _get_value(typ: SmtSort, value: ValueTypes) -> Optional[SmtExpr]:
	if isinstance(value, DontCareClass):
		return None
	elif isinstance(value, int) or isinstance(value, bool):
		return BV(int(value), typ.width)
	else:
		assert typ == value.get_type()
		return value

class ProtocolBuilder:
	def __init__(self, mod: RtlModule):
		self._mod = mod
		self._input_constraints: Dict[str, SmtExpr] = {}
		self._output_constraints: Dict[str, SmtExpr] = {}
		self._start: ProtocolState = ProtocolState()
		self._states: List[ProtocolState] = [self._start]
		self._active: bool = True

	def __setitem__(self, name: str, value: ValueTypes):
		assert isinstance(name, str)
		assert name in self._mod.inputs, f"{list(self._mod.inputs.keys())}"
		vv = _get_value(self._mod.inputs[name], value)
		if vv is None:
			assert name in self._input_constraints
			self._input_constraints.pop(name)
		else:
			self._input_constraints[name] = vv

	def __getitem__(self, name: str) -> OutputSignal:
		assert isinstance(name, str)
		assert name in self._mod.outputs, f"{list(self._mod.outputs.keys())}"
		return OutputSignal(name=name, parent=self)

	def _wait(self, name: str, value: ValueTypes, max: int):
		assert len(self._output_constraints) == 0, f"{list(self._output_constraints)}"
		assert name in self._mod.outputs, f"{list(self._mod.outputs.keys())}"
		typ = self._mod.outputs[name]
		assert typ == BVType(1), f"wait only supported for 1-bit signals for now {name} : {typ}"
		assert value in {1,0}
		assert 1024 > max > 0, f"{max} is too big or too small"
		not_value = BV({1:0, 0:1}[value], 1)

		new_states = []
		for state in self._states:
			# for every state, append the correct number of wait states
			wait_states = [ProtocolState() for _ in range(max)]
			new_states += wait_states
			sts = [state] + wait_states
			for ii in range(max):
				sts[ii].edges += [ProtocolEdge(inputs=self._input_constraints, outputs={name: not_value})]
				sts[ii].edges[-1].next = sts[ii+1]

		self._states += new_states
		self._output_constraints = {name: BV(value, 1)}
		self._input_constraints = copy.copy(self._input_constraints)

	def _if(self, pin: str, value: ValueTypes, body):
		# remember current states and inputs/outputs for backtracking after the body
		_inp = copy.copy(self._input_constraints)
		_out = copy.copy(self._output_constraints)
		_states = copy.copy(self._states)


	def _expect(self, name: str, value: ValueTypes):
		assert name in self._mod.outputs, f"{list(self._mod.outputs.keys())}"
		vv = _get_value(self._mod.outputs[name], value)
		if vv is None:
			assert False, "No way to remove output constraints!"
		else:
			self._output_constraints[name] = vv

	def inputs(self, **kwargs) -> ProtocolBuilder:
		assert self._active
		for name, value in kwargs.items():
			self.__setitem__(name, value)
		return self

	def outputs(self, **kwargs) -> ProtocolBuilder:
		assert self._active
		for name, value in kwargs.items():
			self._expect(name, value)
		return self

	def _advance_states(self, edge: ProtocolEdge):
		assert edge.next is None, f"{edge}"

		next_states = []
		for st in self._states:
			ed = copy.copy(edge)
			st.edges += [ed]
			ed.next = ProtocolState()
			next_states.append(ed.next)
		self._states = next_states

	def _step(self):
		edge = ProtocolEdge(inputs=self._input_constraints, outputs=self._output_constraints)
		self._advance_states(edge)
		self._output_constraints = {}
		self._input_constraints = copy.copy(self._input_constraints)

	def step(self, cycles: ValueTypes = 1):
		assert self._active
		if isinstance(cycles, int):
			assert cycles >= 0
			for _ in range(cycles):
				self._step()
		else:
			assert isinstance(cycles, SmtExpr)
			assert cycles.get_type().is_bv_type()
			raise NotImplementedError("A symbolic number of steps is not supported in the current verson!")

	def finish(self) -> Protocol:
		assert self._active
		assert len(self._input_constraints) > 0 or len(self._output_constraints) > 0, "No constraints in last cycle!"
		self.step()
		self._active = False
		return Protocol(self._start)

from pysmt.walkers import DagWalker

class FindVariableIntervals(DagWalker):
	_instance: Optional[FindVariableIntervals] = None
	@staticmethod
	def find(expr: SmtExpr):
		if FindVariableIntervals._instance is None:
			FindVariableIntervals._instance = FindVariableIntervals()
		return FindVariableIntervals._instance.walk(expr)
	def __init__(self, env=None):
		super().__init__(env)
	def bits(self, formula): return formula.get_type().width
	def walk(self, formula, **kwargs):
		res = super().walk(formula, **kwargs)
		if isinstance(res, list):
			# fixup offsets of concatenation
			res_rev = list(reversed(res))
			widths = [ii[0] - ii[1] + 1 for ii in res_rev]
			offsets = [0] + list(itertools.accumulate(widths))
			final_res = [(ww - 1 + oo, oo, ii) for oo, ww, ii in zip(offsets, widths, res_rev)]
			return final_res
		else:
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
