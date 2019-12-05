#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from .spec import *
from pysmt.shortcuts import Symbol, And, BV, BVType, BVExtract, Equals
from collections import defaultdict
from typing import Set, Union, Iterator
import copy

##### Verification Protocol
@dataclass
class VeriState:
	edges: List[VeriEdge]
	transactions: List[Transaction]

@dataclass
class VeriEdge:
	ii: int
	input_constraints: List[SmtExpr]
	output_constraints: List[SmtExpr]
	arg_mapping: List[SmtExpr]
	ret_arg_mapping: List[SmtExpr]
	next: Optional[VeriState] = None

@dataclass
class VeriSpec:
	start: VeriState


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

def find_constraints_and_mappings(io_prefix: str, signals: Dict[str, SmtExpr], var_map: Dict[str, int]) -> Tuple[List[SmtExpr], List[SmtExpr], Dict[str, int]]:
	""" works for input or output signals """

	constraints: List[SmtExpr] = []
	mappings: List[SmtExpr] = []
	new_var_map = copy.copy(var_map)

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

	return constraints, mappings, new_var_map

@dataclass
class ProtocolToVerificationGraphConverter:
	io_prefix: str = ""
	tran: Transaction = None
	def convert(self, proto: Protocol, tran: Transaction, io_prefix: str) -> VeriSpec:
		self.io_prefix = io_prefix
		self.tran = tran
		arg_map = {name: 0 for name in tran.args.keys()}
		ret_arg_map = {name: 0 for name in tran.ret_args.keys()}
		start = self.visit_state([], arg_map, ret_arg_map, proto.start)
		return VeriSpec(start)

	def visit_edge(self, prefix: List[VeriEdge], arg_map: Dict[str, int], ret_arg_map: Dict[str, int], edge: ProtocolEdge) -> VeriEdge:
		# the current transition id is the prefix length
		ii = len(prefix)

		input_constraints,  input_mappings, new_arg_map  = find_constraints_and_mappings(self.io_prefix, edge.inputs, arg_map)
		output_constraints, output_mappings, new_ret_arg_map = find_constraints_and_mappings(self.io_prefix, edge.outputs, ret_arg_map)

		new_edge = VeriEdge(ii, input_constraints, output_constraints, input_mappings, output_mappings)

		print("Edge @ ", ii, input_constraints, input_mappings, output_constraints, output_mappings)
		new_edge.next = self.visit_state(prefix + [new_edge], new_arg_map, new_ret_arg_map, edge.next)
		return new_edge

	def visit_state(self, prefix: List[VeriEdge], arg_map: Dict[str, int], ret_arg_map: Dict[str, int], state: ProtocolState) -> VeriState:
		new_state = VeriState([], transactions=[self.tran])
		for edge in state.edges:
			new_edge = self.visit_edge(prefix, arg_map, ret_arg_map, edge)
			new_state.edges.append(new_edge)
		if len(state.edges) == 0:
			print("PATH end", new_state)
		return new_state

def to_verification_graph(proto: Protocol, tran: Transaction, io_prefix: str) -> VeriSpec:
	return ProtocolToVerificationGraphConverter().convert(proto, tran, io_prefix)



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
