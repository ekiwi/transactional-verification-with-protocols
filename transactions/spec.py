#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from dataclasses import dataclass, field
from typing import Optional, Callable, List, Tuple, Dict, Any
@dataclass
class SmtSort:
	pass
@dataclass
class BitVecSort(SmtSort):
	width: int
@dataclass
class ArraySort(SmtSort):
	index: BitVecSort
	data: BitVecSort
@dataclass
class SmtFormula:
	sort: SmtSort
	expr : Any # essentially a pysmt fnode
@dataclass
class BitVecExpr:
	width: int
	def sort(self): return BitVecSort(self.width)
@dataclass
class BitVecConst(BitVecExpr):
	value: int
@dataclass
class BitVecSymbol(BitVecExpr):
	name: str
@dataclass
class BitVecConcat(BitVecExpr):
	msb: BitVecExpr
	lsb: BitVecExpr
@dataclass
class BitVecExtract(BitVecExpr):
	base: BitVecExpr
	msb: int
	lsb: int
@dataclass
class ArraySymbol:
	name: str
	sort: ArraySort
@dataclass
class ArraySelect(BitVecExpr):
	array: ArraySymbol
	index: int

@dataclass
class Mapping:
	"""
	 A mapping relates a module pin to constant or symbolic bits.
	"""
	pin : str
	# TODO: change back to SmtExpr for now (using pysmt) try to check properties instead of structurally enforcing them
	expr : BitVecExpr

@dataclass
class Transition:
	mappings : List[Mapping]

@dataclass
class Protocol:
	"""
	 A protocol is a fixed length sequence of transitions.
	 TODO: - allow backward edges that are waiting for external events (from the environment)
	       - allow various length paths that could be controlled by the model (instead of the environment)
	"""
	transitions : List[Transition]

@dataclass
class Transaction:
	# name is used for debugging and error handling
	name : str
	proto : Protocol
	semantics : Dict[str, SmtFormula]
	args: List[BitVecSymbol] = field(default_factory=list)
	ret_args: List[BitVecSymbol] = field(default_factory=list)

@dataclass
class Spec:
	state : List[Tuple[str, SmtSort]] = field(default_factory=list)
	transactions : List[Transaction] = field(default_factory=list)

@dataclass
class StateMapping:
	# TODO: change back to SmtExpr for now (using pysmt) try to check properties instead of structurally enforcing them
	arch: BitVecExpr
	impl: BitVecExpr

@dataclass
class VerificationProblem:
	# the spec to be verified
	spec: Spec
	# name of the module to be verified
	implementation: str
	# submodules that will be replaced by their specs
	submodules: List[Tuple[str, Spec]] = field(default_factory=list)
	# invariances are formulas over implementation state that hold at the beginning
	# and the end of each transaction as well as after reset
	invariances : List[SmtFormula] = field(default_factory=list)
	# mappings specify how bits in the spec state correspond to bits in the implementation state
	mappings : List[StateMapping] = field(default_factory=list)
