#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Callable, List, Tuple, Dict, Any, Union
import pysmt.fnode, pysmt.typing

""" an SmtExpr is represented by a pysmt node """
SmtExpr = pysmt.fnode.FNode

""" a SmtSort is represented by a pysmt sort type """
SmtSort = pysmt.typing.PySMTType

@dataclass
class Protocol:
	start: ProtocolState

@dataclass
class ProtocolState:
	edges: List[ProtocolEdge] = field(default_factory=list)

@dataclass
class ProtocolEdge:
	inputs: Dict[str, SmtExpr] = field(default_factory=dict)
	outputs: Dict[str, SmtExpr] = field(default_factory=dict)
	next: Optional[ProtocolState] = None

@dataclass
class Transition:
	# constraints on/mappings of the module inputs
	inputs: Dict[str, SmtExpr] = field(default_factory=dict)
	# expected output
	outputs: Dict[str, SmtExpr] = field(default_factory=dict)

@dataclass
class LegacyProtocol:
	"""
	 A protocol is a fixed length sequence of transitions.
	 TODO: - allow backward edges that are waiting for external events (from the environment)
	       - allow various length paths that could be controlled by the model (instead of the environment)
	"""
	transitions : List[Transition] = field(default_factory=lambda: [Transition()])
	#guard: Optional[SmtExpr] = None # determines when this protocol is enabled (guard can only refer to transaction arguments)

@dataclass
class Transaction:
	# name is used for debugging and error handling
	name : str
	proto : Union[LegacyProtocol, Protocol] = field(default_factory=LegacyProtocol)
	# TODO: allow semantics to refer to subtransactions which could then be verified as uninterpreted functions
	semantics : Dict[str, SmtExpr] = field(default_factory=dict)
	args: Dict[str, SmtSort] = field(default_factory=dict)
	ret_args: Dict[str, SmtSort] = field(default_factory=dict)

@dataclass
class Spec:
	state : Dict[str, SmtSort] = field(default_factory=dict)
	transactions : List[Transaction] = field(default_factory=list)
	# input/output constraints when no other transaction is active
	idle: Optional[LegacyProtocol] = field(default_factory=LegacyProtocol)

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
class Reset:
	name: str
@dataclass
class HighActiveReset(Reset): pass
@dataclass
class LowActiveReset(Reset): pass
@dataclass
class RtlModule:
	name: str
	inputs: Dict[str, SmtSort]
	outputs: Dict[str, SmtSort]
	state: Dict[str, SmtSort]
	submodules: Dict[str, RtlModule]
	reset: Optional[Reset]
	# the string that needs to be prepended to io names to access this io
	# (this is a detail necessary for our "expose submodule" implementation)
	io_prefix: str = ""
