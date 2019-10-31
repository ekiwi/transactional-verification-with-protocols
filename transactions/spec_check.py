#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# code to verify the well-formedness (i.e. semantic checks) of a verification problem and spec

from .spec import *
from .module import Module
from pysmt.shortcuts import get_free_variables, BOOL, BVType, ArrayType, Symbol
from typing import Optional, Set, Union


def check_symbols(symbols: list, allowed_symbols: Dict[str, Any], help: str):
	for sym in symbols:
		name, sort = sym.symbol_name(), sym.symbol_type()
		assert name in allowed_symbols, f"Formula refers to unknown symbol {sym}.\n{help}"
		assert sort == allowed_symbols[name], f"Type mismatch for symbol {sym}. Expected {allowed_symbols[name]} \n{help}"

def get_symbols_of_bitvec_expr(e: BitVecExpr) -> list:
	if isinstance(e, ArraySelect): return [to_pysmt_symbol(e.array.name, e.array.sort)]
	if isinstance(e, BitVecSymbol): return [to_pysmt_symbol(e.name, BitVecSort(e.width))]
	if isinstance(e, BitVecConst): return []
	if isinstance(e, BitVecConcat): return get_symbols_of_bitvec_expr(e.msb) + get_symbols_of_bitvec_expr(e.lsb)
	if isinstance(e, BitVecExtract): return get_symbols_of_bitvec_expr(e.base)
	assert False, f"Unexpected BitVecExpr: {e} : {type(e)}"

def typecheck_bitvec_expr(e: BitVecExpr):
	if isinstance(e, ArraySelect):
		assert e.array.sort.index.width > 0, f"address range must be greater 0"
		assert e.array.sort.data.width == e.width, f"{e} returns {e.array.sort.data}, not {e.width}"
		assert e.index >= 0, f"Select index may not be negative"


def check_smt_formula_type(f: SmtFormula):
	py_smt_type = to_pysmt_sort(f.sort)
	assert py_smt_type == f.expr.get_type(), f"mismatched type {py_smt_type} vs {f.expr.get_type()}"

def to_pysmt_sort(sort: SmtSort):
	if isinstance(sort, BitVecSort):
		if sort.width == 1: return BOOL
		assert sort.width > 1, f"BV width too small: {sort.width}"
		return BVType(sort.width)
	if isinstance(sort, ArraySort):
		return ArrayType(to_pysmt_sort(sort.index), to_pysmt_sort(sort.data))
	assert False, f"Unsupported sort: {sort} : {type(sort)}"

def to_pysmt_symbol(name: str, sort: SmtSort):
	return Symbol(name, to_pysmt_sort(sort))

def symbol_index(symbols):
	return { s.symbol_name(): s.symbol_type() for s in symbols }

def check_verification_problem(prob: VerificationProblem, mod: Module):
	""" runs semantic checks on verification problem """


	assert mod.name == prob.implementation, f"Loaded module and implementation do not match!"

	# make sure there are matching pairs of submodules (instances) and corresponding specs
	for name, _ in prob.submodules:
		assert name in mod.submodules, f"{name} is not an instance in {mod.name}"
	specs = { name for name, _ in prob.submodules }
	for name in mod.submodules.keys():
		assert name in specs, f"Spec missing for submodule {name} in {mod.name}"

	# specification (aka architectural) state symbols
	arch_state_symbols = [to_pysmt_symbol(name, sort) for name,sort in prob.spec.state]

	# extract potential symbols from the implementation
	impl_state_symbols = [st.symbol for st in mod.state]
	submodule_state_symbols = []
	for instance_name, instance_spec in prob.submodules:
		submodule_state_symbols += [to_pysmt_symbol(instance_name + name, sort) for name, sort in instance_spec.state]

	# check the symbols referred to by the invariances
	invariance_symbols = symbol_index(impl_state_symbols + submodule_state_symbols)
	for inv in prob.invariances:
		assert inv.sort == BitVecSort(1), f"unexpected invariance type {inv.sort}"
		check_smt_formula_type(inv)
		msg = "Invariances can only refer to implementation state or architectural state of abstracted submodules."
		check_symbols(get_free_variables(inv), invariance_symbols, msg)

	# check the symbols referred to by the mappings
	for mapping in prob.mappings:
		assert

