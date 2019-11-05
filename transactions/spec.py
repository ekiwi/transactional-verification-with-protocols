#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Callable, List, Tuple, Dict, Any
import pysmt.fnode

""" an SmtExpr is represented by a pysmt node """
SmtExpr = pysmt.fnode.FNode

""" a SmtSort is also represented by a pysmt node (which needs to actually be a is_type()) """
SmtSort = pysmt.fnode.FNode

@dataclass
class Transition:
	# constraints on/mappings of the module inputs
	inputs: Dict[str, SmtExpr] = field(default_factory=dict)
	# expected output
	outputs: Dict[str, SmtExpr] = field(default_factory=dict)

@dataclass
class Protocol:
	"""
	 A protocol is a fixed length sequence of transitions.
	 TODO: - allow backward edges that are waiting for external events (from the environment)
	       - allow various length paths that could be controlled by the model (instead of the environment)
	"""
	transitions : List[Transition] = field(default_factory=lambda: [Transition()])

@dataclass
class Transaction:
	# name is used for debugging and error handling
	name : str
	proto : Protocol = field(default_factory=Protocol)
	# TODO: allow semantics to refer to subtransactions which could then be verified as uninterpreted functions
	semantics : Dict[str, SmtExpr] = field(default_factory=dict)
	args: Dict[str, SmtSort] = field(default_factory=dict)
	ret_args: Dict[str, SmtSort] = field(default_factory=dict)

@dataclass
class Spec:
	state : Dict[str, SmtSort] = field(default_factory=dict)
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
	submodules: Dict[str, Spec] = field(default_factory=dict)
	# invariances are formulas over implementation state that hold at the beginning
	# and the end of each transaction as well as after reset
	invariances : List[SmtExpr] = field(default_factory=list)
	# mappings specify how bits in the spec state correspond to bits in the implementation state
	mappings : List[StateMapping] = field(default_factory=list)

@dataclass
class RtlModule:
	name: str
	inputs: Dict[str, SmtSort]
	outputs: Dict[str, SmtSort]
	state: Dict[str, SmtSort]
	submodules: Dict[str, RtlModule]
