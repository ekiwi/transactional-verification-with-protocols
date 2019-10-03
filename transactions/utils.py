#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from functools import reduce
from pysmt.shortcuts import Equals, BV, Iff, And, Or, BVConcat

def default(expr, default):
	return expr if expr is not None else default

def get_type(expr):
	if expr.is_symbol(): return expr.symbol_type()
	if expr.is_function_application():
		return expr.function_name().symbol_type().return_type
	if expr.is_select():
		return expr.arg(0).get_type().elem_type
	assert False, f"should not get here! {expr}"

def is_bool(expr):
	try:
		return expr.get_type().is_bool_type()
	except:
		if expr.is_bool_constant() or expr.is_bool_op(): return True
		if expr.is_bv_constant() or expr.is_bv_op(): return False
		if expr.is_symbol(): return expr.symbol_type().is_bool_type()
		if expr.is_function_application():
			return expr.function_name().symbol_type().return_type.is_bool_type()
		if expr.is_select():
			return expr.arg(0).get_type().elem_type.is_bool_type()
		if expr.is_ite():
			return is_bool(expr.arg(1))
		if expr.is_store() or expr.is_array_value():
			return False
		else:
			assert False, f"should not get here! {expr}"

def to_bool(expr):
	assert not is_bool(expr)
	assert expr.bv_width() == 1
	return  Equals(expr, BV(1, 1))

def equal(e0, e1):
	if not is_bool(e0) and not is_bool(e1): return Equals(e0, e1)
	if not is_bool(e0): e0 = to_bool(e0)
	if not is_bool(e1): e1 = to_bool(e1)
	return Iff(e0, e1)

def conjunction(*args):
	assert len(args) > 0
	if len(args) == 1: return args[0]
	else: return reduce(And, args)

def cat(*args):
	assert len(args) > 0
	if len(args) == 1: return args[0]
	else: return reduce(BVConcat, args)

def disjunction(*args):
	assert len(args) > 0
	if len(args) == 1: return args[0]
	else: return reduce(Or, args)