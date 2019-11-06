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

def require_scalar(symbols: Dict[str, SmtSort], kind: str):
	for name, tpe in symbols.items():
		assert tpe.is_bv_type() or tpe.is_bool_type(), f"{kind} {name} needs to bge bitvector or bool, not {tpe}"

def check_verification_problem(prob: VerificationProblem, mod: RtlModule):
	""" runs semantic checks on verification problem """


	assert mod.name == prob.implementation, f"Loaded module and implementation do not match!"

	# make sure there are matching pairs of submodules (instances) and corresponding specs
	for name in prob.submodules.keys():
		assert name in mod.submodules, f"{name} is not an instance in {mod.name}"
	specs = { name for name in prob.submodules.keys() }
	for name in mod.submodules.keys():
		assert name in specs, f"Spec missing for submodule {name} in {mod.name}"

	# specification (aka architectural) state symbols
	arch_state_symbols = prob.spec.state

	# extract potential symbols from the implementation
	submodule_state_symbols = {}
	for instance_name, instance_spec in prob.submodules.items():
		instance_arch_state = {instance_name + "." + n: t for n,t in instance_spec.state.items()}
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

	input_symbols = merge_indices(arch_state_symbols, tran.args)
	output_symbols = merge_indices(arch_state_symbols, tran.ret_args)

	# check semantics
	for arg_name, arg_tpe in tran.ret_args.items():
		assert arg_name in tran.semantics, f"Need to define return parameter {arg_name} : {arg_tpe} in semantics!"
		check_smt_expr(tran.semantics[arg_name], input_symbols, tpe=arg_tpe,
					   msg="Semantics can only refer to arguments and architectural state.")
	for state_name, state_tpe in arch_state_symbols.items():
		if state_name in tran.semantics:
			check_smt_expr(tran.semantics[state_name], input_symbols, tpe=state_tpe,
						   msg="Semantics can only refer to arguments and architectural state.")
	output_names = set(output_symbols.keys())
	unknown_outputs = set(tran.semantics.keys()) - output_names
	assert len(unknown_outputs) == 0, f"Semantics write to undeclared outputs {unknown_outputs}."

	# check protocol
	assert len(tran.proto.transitions) > 0, f"In transaction {tran.name}: zero transition protocols are not allowed!"
	for tt in tran.proto.transitions:
		for pin, expr in tt.inputs.items():
			assert pin in mod.inputs, f"{pin} is not a valid input of module {mod.name}. Inputs: {mod.inputs}"
			check_smt_expr(expr, tran.args, tpe=mod.inputs[pin],
						   msg="Input pins may be bound to constants or transaction arguments.")
		for pin, expr in tt.outputs.items():
			assert pin in mod.outputs, f"{pin} is not a valid output of module {mod.name}. Outputs: {mod.outputs}"
			check_smt_expr(expr, tran.ret_args, tpe=mod.outputs[pin],
						   msg="Output pins may be bound to constants or transaction return arguments.")

