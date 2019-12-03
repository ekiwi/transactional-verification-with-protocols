#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from .spec import *
from pysmt.shortcuts import Symbol, And, BV, BVType
from collections import defaultdict
from typing import Set, Union, Iterator
import copy

def make_symbols(symbols: Dict[str, SmtSort], prefix: str = "", suffix: str = "") -> Dict[str, Symbol]:
	return {name: Symbol(prefix + name + suffix, tpe) for name, tpe in symbols.items()}

# protocol processing algorithms

@dataclass
class Range:
	msb: int
	lsb: int

@dataclass
class Signal:
	name: str
	range: Optional[Range] = None
	def __str__(self):
		if self.range is None: return self.name
		return f"{self.name}[{self.range.msb}:{self.range.lsb}]"

@dataclass
class Constraint:
	signal: Signal

@dataclass
class ConstConstraint(Constraint):
	value: int
	def __str__(self): return f"{self.signal} = {self.value}"
	def __repr__(self): return str(self)

@dataclass
class EquivalenceConstraint(Constraint):
	transition: int
	other: Signal

@dataclass
class ProtocolGraph:
	pass

@dataclass
class ProtocolGraphTransition:
	inputs: Dict[str, List[Constraint]]
	outputs: Dict[str, List[Constraint]]
	guard: SmtExpr

@dataclass
class ProtocolGraphEdge:
	guards: List[SmtExpr]
	input_constraints: SmtExpr
	input_mappings: Dict[str, ]
	inputs: Dict[str, SmtExpr]
	outputs: Dict[str, SmtExpr]
	transactions: Set[Transaction]

@dataclass
class ProtocolGraphState:
	next: List[ProtocolGraphTransition]

ProtocolPath = List[ProtocolGraphTransition]


###################### New Types
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
		assert 1024 > max > 0, f"{max} is too big or too small"

		wait_states = self._states
		tru = ProtocolEdge(inputs=self._input_constraints, outputs={name: value})
		fals = ProtocolEdge(inputs=self._input_constraints, outputs={name: value})


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

	def _advance_states(self, edges: List[ProtocolEdge]):
		assert all(e.next is None for e in edges), f"{edges}"
		assert len(edges) > 0, f"{edges}"
		next_states = []
		for st in self._states:
			assert len(st.edges) == 0
			st.edges = [copy.copy(ed) for ed in edges]
			for ed in st.edges:
				ed.next = ProtocolState()
				next_states.append(ed.next)
		self._states = next_states


	def _step(self):
		edges = [ProtocolEdge(inputs=self._input_constraints, outputs=self._output_constraints)]
		self._advance_states(edges)
		self._output_constraints = {}

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

class ProtocolMerger:
	def __init__(self, tran0: Transaction, tran1: Transaction):
		self.args = make_symbols(tran.args)
		self.ret_args = make_symbols(tran.ret_args)

	def merge(self, s0: ProtocolGraphState, s1: ProtocolGraphState) -> ProtocolGraphState:
		
		for t0 in s0.next:
			for t1 in s1.next:
				if input_different(t0, t1):
					continue
				if output_compatible(t0, t1):
					merge(t0, t1)
					break
				# there exists a common input trace, but outputs are not compatible
				# => if this is between two different transactions -> abort!
				# => if this is for the same transaction -> new edge


def merge_protocols(s0: ProtocolGraphState, s1: ProtocolGraphState) -> ProtocolGraphState:
	pass

def compare_transitions(t1: Transition, t2: Transition):
	inputs = set(t1.inputs.keys()) | set(t2.inputs.keys())
	for ii in inputs:
		# unconstrained in one example
		if ii not in t1.inputs: print(f"{ii} missing from t1")
		if ii not in t2.inputs: print(f"{ii} missing from t2")
		# load expressions
		e1, e2 = t1.inputs[ii], t2.inputs[ii]
		if e1 == e2: print(f"{ii} is the same in t1 and t2")
		# check for constant constraint

def is_unsat(expr: SmtExpr) -> bool:
	return False



def get_input_constraints(tt: ProtocolGraphTransition) -> SmtExpr:
	return True

def visit_edges(prefix: SmtExpr, e0: ProtocolGraphEdge, e1: ProtocolGraphEdge) -> List[ProtocolGraphEdge]:
	# check if there is an input that satisfies both edges
	input_constraints = And(prefix, And(e0.input_constraints, e1.input_constraints))
	common_input_exists = not is_unsat(input_constraints)

	# if the edges are mutually exclusive, we stop merging
	if not common_input_exists:
		return [e0, e1]

	# check to see if the two edges refer to the same transaction
	same_transaction = len(e0.transactions) == len(e1.transactions) == 1 and e0.transactions[0] == e1.transactions[0]

	# check if the outputs are compatible

def protocol_constraints(proto: LegacyProtocol):
	""" compute i/o constraints of protocol (without semantics) """

	# NOTE: this replaces parts of `generate_inputs` in `verifier.py`

	# variable -> interval -> (cycle, signal_expr)
	var2inputs: Dict[SmtExpr, Dict[Tuple[int, int], List[Tuple[int, Signal]]]] = defaultdict(lambda: defaultdict(list))

	input_constraints = [defaultdict(list) for _ in range(len(proto.transitions))]

	# find constant and variable mapping on the protocol inputs
	for ii, tt in enumerate(proto.transitions):
		for signal_name, expr in tt.inputs.items():
			expr_width = expr.get_type().width
			for (signal_msb, signal_lsb, (var_msb, var_lsb, var)) in FindVariableIntervals.find(expr):
				is_full = signal_lsb == 0 and signal_msb + 1 == expr_width
				if is_full:
					sig_expr = Signal(name = signal_name)
				else:
					sig_expr = Signal(name = signal_name, range=Range(lsb=signal_lsb, msb=signal_msb))
				if var.is_symbol():
					var2inputs[var][(var_msb, var_lsb)].append((ii, sig_expr))
				else:
					assert var_lsb == 0 and var_msb + 1 == var.get_type().width, f"Expect constants to be simplified!"
					value = int(var.bv_str(), 2)
					input_constraints[ii][signal_name].append(ConstConstraint(signal=sig_expr, value=value))

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
				print(f"WARN:  argument bit {var}[{bit}] is not defined by the protocol.")

		# generate conditions for each interval
		for ((msb, lsb), mappings) in refs.items():
			assert len(mappings) > 0
			# if a variable is only referenced once, then this imposes no constraints
			if len(mappings) == 0: continue
			full_range = msb + 1 == var.symbol_type().width and lsb == 0

			# find (one of) the first references to this interval
			mappings_sorted_by_cycle = sorted(mappings, key=lambda ii: ii[0])
			start = mappings_sorted_by_cycle[0]

			# we bind the start mapping to a constant and then check every other mapping against the constant
			transition = start[0]
			if full_range:	const = Signal(start[1])
			else:			const = Signal(start[1], Range(lsb=lsb, msb=msb))

			# create constraint for every signal/cycle
			for cycle, expr in mappings_sorted_by_cycle[1:]:
				input_constraints[cycle][expr.name] = EquivalenceConstraint(signal=expr, transition=transition, other=const)

	print(input_constraints)



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
