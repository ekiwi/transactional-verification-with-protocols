#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from .spec import *
from pysmt.shortcuts import Symbol, And
from collections import defaultdict
from typing import Set

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
class ProtocolGraphEdge:
	guards: List[SmtExpr]
	input_constraints: SmtExpr
	input_mappings: Dict[str, ]
	inputs: Dict[str, SmtExpr]
	outputs: Dict[str, SmtExpr]
	transactions: Set[Transaction]


@dataclass
class ProtocolGraphState:
	pass

def is_unsat(expr: SmtExpr) -> bool:
	return False


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





def protocol_constraints(proto: Protocol):
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