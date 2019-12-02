#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# contains convenience code to build spec with less words!

from itertools import zip_longest
from typing import Optional
from pysmt.shortcuts import *
from .utils import *
from .spec import LegacyProtocol, Transition


def merge_dicts(a: dict, b: dict) -> dict:
	keys = a.keys() | b.keys()
	if len(keys) < len(a) + len(b):
		for k in keys:
			assert not (k in a and k in b), f"Key {k} is used in a and b!"
	return {**a, **b}

class ProtoBuilder:
	def __init__(self, mappings: list):
		self.mappings = mappings
		assert len(self) > 0, f"Protocol must describe at least one transition!"

	def __len__(self):
		return len(self.mappings)

	def __or__(self, other):
		assert isinstance(other, ProtoBuilder)
		m = [merge_dicts(*c) for c in zip_longest(self.mappings, other.mappings, fillvalue=dict())]
		return ProtoBuilder(mappings=m)

	def __add__(self, other):
		assert isinstance(other, ProtoBuilder)
		m = self.mappings + other.mappings
		return ProtoBuilder(mappings=m)

	def __mul__(self, other):
		assert isinstance(other, int)
		assert other < 1000
		m = self.mappings * other
		return ProtoBuilder(mappings=m)

	def __rshift__(self, other):
		assert isinstance(other, int)
		m = [dict() for _ in range(other)] + self.mappings
		return ProtoBuilder(mappings=m)

	def __lshift__(self, other):
		assert isinstance(other, int)
		m = self.mappings + [dict() for _ in range(other)]
		return ProtoBuilder(mappings=m)

	def finish(self):
		return LegacyProtocol([Transition(t) for t in self.mappings])

def BitSerial(signal: str, sym, max_bits: Optional[int] = None) -> ProtoBuilder:
	max_bits = default(max_bits, sym.bv_width())
	bits = min(max_bits, sym.bv_width())
	return ProtoBuilder([{signal: BVExtract(sym, ii, ii)} for ii in range(bits)])

def Repeat(signal: str, sym, cycles) -> ProtoBuilder:
	return ProtoBuilder([{signal: sym}] * cycles)

def Map(signal:str, sym) -> ProtoBuilder:
	return ProtoBuilder([{signal: sym}])