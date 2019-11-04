#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# code to verify the well-formedness (i.e. semantic checks) of a verification problem and spec

from .spec import *
from .module import Module
from pysmt.shortcuts import get_free_variables, BOOL, BVType, ArrayType, Symbol
import pysmt.fnode
from typing import Optional, Set, Union

SmtSort = pysmt.fnode.FNode

def check_smt_expr(e: SmtExpr, allowed_symbols: Dict[str, Any], msg: str, tpe: Optional[SmtSort] = None):
	for sym in get_free_variables(e):
		name, sort = sym.symbol_name(), sym.symbol_type()
		assert name in allowed_symbols, f"Expression {e} refers to unknown symbol {sym}.\n{msg}"
		assert sort == allowed_symbols[name], f"Type mismatch for symbol {sym} in expression {e}. Expected {allowed_symbols[name]} \n{msg}"
	if tpe is not None:
		assert e.get_type() == tpe, f"Expression {e} is of type {e.get_type()} but needs to be {tpe}"

def symbol_list_to_index(symbols: List[Symbol], prefix: str = "", no_arrays = False) -> Dict[str, Any]:
	index = {}
	for sym in symbols:
		name = prefix + sym.name
		tpe = sym.get_type()
		if no_arrays:
			assert tpe.is_bv_type() or tpe.is_bool_type(), f"Symbol {name} needs to a BitVector or Bool, not {tpe}!"
		assert name not in index, f"Symbol {index[name]} already defined, cannot redefine!"
		index[name] = tpe
	return index

def merge_indices(in0: dict, in1: dict) -> dict:
	common_keys = in0.keys() & in1.keys()
	assert len(common_keys) == 0, f"Common keys: {common_keys}"
	return {**in0, **in1}

def symbol_index(symbols):
	return { s.symbol_name(): s.symbol_type() for s in symbols }

def require_scalar(symbols: List[Symbol], kind: str):
	for sym in symbols:
		tpe = sym.symbol_type()
		assert tpe.is_bv_type() or tpe.is_bool_type(), f"{kind} {sym.symbol_name()} needs to bge bitvector or bool, not {tpe}"

def check_verification_problem(prob: VerificationProblem, mod: RtlModule):
	""" runs semantic checks on verification problem """


	assert mod.name == prob.implementation, f"Loaded module and implementation do not match!"

	# make sure there are matching pairs of submodules (instances) and corresponding specs
	for name, _ in prob.submodules:
		assert name in mod.submodules, f"{name} is not an instance in {mod.name}"
	specs = { name for name, _ in prob.submodules }
	for name in mod.submodules.keys():
		assert name in specs, f"Spec missing for submodule {name} in {mod.name}"

	# specification (aka architectural) state symbols
	arch_state_symbols = symbol_list_to_index(prob.spec.state)

	# extract potential symbols from the implementation
	submodule_state_symbols = {}
	for instance_name, instance_spec in prob.submodules:
		instance_arch_state = symbol_list_to_index(instance_spec.state, prefix=instance_name + ".")
		submodule_state_symbols = merge_indices(submodule_state_symbols, instance_arch_state)

	# check the symbols referred to by the invariances
	invariance_symbols = merge_indices(mod.state, submodule_state_symbols)
	for inv in prob.invariances:
		msg = "Invariances can only refer to implementation state or architectural state of abstracted submodules."
		check_smt_expr(inv, invariance_symbols, msg, tpe=BOOL)

	# check the symbols referred to by the mappings
	for mapping in prob.mappings:
		check_smt_expr(mapping.arch, arch_state_symbols,
					   msg="Should only refer to architectural state.")
		check_smt_expr(mapping.impl, invariance_symbols,
					   msg="Should only refer to implementation state or architectural state of abstracted submodules.")


	# check transactions
	tran_index = {}
	for tran in prob.spec.transactions:
		assert tran.name not in tran_index, f"Transaction of name {tran.name} already exists: {tran} vs {tran_index[tran.name]}"
		tran_index[tran.name] = tran
		check_transaction(tran, mod, arch_state_symbols)


def check_transaction(tran: Transaction, mod: RtlModule, arch_state_symbols: Dict[str, SmtSort]):
	require_scalar(tran.args, "Transaction argument")
	require_scalar(tran.ret_args, "Transaction return argument")

	input_symbols = merge_indices(arch_state_symbols, symbol_index(tran.args))
	output_symbols = merge_indices(arch_state_symbols, symbol_index(tran.ret_args))
