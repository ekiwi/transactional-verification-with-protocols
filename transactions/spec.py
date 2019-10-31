#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from dataclasses import dataclass, field
from typing import Optional, Callable, List, Tuple, Dict, Any
import pysmt.fnode

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
class Symbol:
	name: str
	sort: SmtSort
@dataclass
class SmtExpr:
	""" transparent wrapper arround a pysmt fnode expr """
	expr : pysmt.fnode.FNode

@dataclass
class Mapping:
	"""
	 A mapping relates a module pin to constant or symbolic bits.
	"""
	pin : str
	expr : SmtExpr

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
	semantics : Dict[str, SmtExpr]
	args: List[Symbol] = field(default_factory=list)
	ret_args: List[Symbol] = field(default_factory=list)

@dataclass
class Spec:
	state : List[Symbol] = field(default_factory=list)
	transactions : List[Transaction] = field(default_factory=list)

@dataclass
class StateMapping:
	arch: SmtExpr
	impl: SmtExpr

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
	invariances : List[SmtExpr] = field(default_factory=list)
	# mappings specify how bits in the spec state correspond to bits in the implementation state
	mappings : List[StateMapping] = field(default_factory=list)
