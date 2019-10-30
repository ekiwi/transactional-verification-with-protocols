#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from dataclasses import dataclass, field
from typing import Optional, Callable, List, Tuple
@dataclass
class SmtSort:
	pass
@dataclass
class BitVecSort:
	width: int
@dataclass
class ArraySort:
	index: BitVecSort
	data: BitVecSort
@dataclass
class SmtFormula:
	sort: SmtSort
	expr : object # essentially a pysmt fnode
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
class Mapping:
	"""
	 A mapping relates a module pin to constant or symbolic bits.
	"""
	pin : str
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
	semantics : Callable
	args: List[BitVecSymbol] = field(default_factory=list)
	ret_args: List[BitVecSymbol] = field(default_factory=list)

@dataclass
class Spec:
	state : List[Tuple[str, SmtSort]] = field(default_factory=list)
	transactions : List[Transaction] = field(default_factory=list)

@dataclass
class VerificationProblem:
	# the spec to be verified
	spec: Spec
	# name of the module to be verified
	implementation: str
	# submodules that will be replaced by their specs
	submodules: List[Tuple[str, Spec]]
	# invariances are formulas over implementation state that hold at the beginning
	# and the end of each transaction as well as after reset
	invariances : List[SmtFormula] = field(default_factory=list)
	# mappings specify how bits in the spec state correspond to bits in the implementation state
	mappings : List[Mapping] = field(default_factory=list)