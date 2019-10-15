#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import Optional
from itertools import zip_longest
from pysmt.shortcuts import *
from .utils import *

def merge_dicts(a: dict, b: dict) -> dict:
	keys = a.keys() | b.keys()
	if len(keys) < len(a) + len(b):
		for k in keys:
			assert not (k in a and k in b), f"Key {k} is used in a and b!"
	return {**a, **b}

class Protocol:
	def __init__(self, mappings: list):
		self.mappings = mappings

	def __len__(self):
		return len(self.mappings)

	def __or__(self, other):
		assert isinstance(other, Protocol)
		m = [merge_dicts(*c) for c in zip_longest(self.mappings, other.mappings, fillvalue=dict())]
		return Protocol(mappings=m)

	def __add__(self, other):
		assert isinstance(other, Protocol)
		m = self.mappings + other.mappings
		return Protocol(mappings=m)

	def __mul__(self, other):
		assert isinstance(other, int)
		assert other < 1000
		m = self.mappings * other
		return Protocol(mappings=m)

	def __rshift__(self, other):
		assert isinstance(other, int)
		m = [dict() for _ in range(other)] + self.mappings
		return Protocol(mappings=m)

	def __lshift__(self, other):
		assert isinstance(other, int)
		m = self.mappings + [dict() for _ in range(other)]
		return Protocol(mappings=m)

def BitSerial(signal: str, sym, max_bits: Optional[int] = None) -> Protocol:
	max_bits = default(max_bits, sym.bv_width())
	bits = min(max_bits, sym.bv_width())
	return Protocol([{signal: BVExtract(sym, ii, ii)} for ii in range(bits)])

def Repeat(signal: str, sym, cycles) -> Protocol:
	return Protocol([{signal: sym}] * cycles)

def Map(signal:str, sym) -> Protocol:
	return Protocol([{signal: sym}])

class Transaction:
	def __init__(self, name: str, args: list, ret_args: list, proto: Protocol, semantics):
		self.name = name
		self.args = args
		self.ret_args = ret_args
		self.proto = proto
		self.semantics = semantics

class Spec:
	def __init__(self, arch_state=None, mapping=None, transactions=None, invariances=None, case_split=None):
		self.arch_state = default(arch_state, {})
		self.transactions = default(transactions, [])
		# TODO: invariances maybe should not be part of the Spec as they are more of an implementation detail
		self.invariances = default(invariances, [])
		self.mapping = default(mapping, lambda state: [])
		self.case_split = default(case_split, list())