#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# wip lightweight testbench layer
from dataclasses import dataclass
from typing import Dict, Union, List, Optional, Any
import random
from .module import load_module

class BitVector:
	@staticmethod
	def random(bits):
		assert bits > 0
		return BitVectorValue(random.randrange(start=0, stop=1 << bits), bits=bits)

class BitVectorValue(BitVector):
	def __init__(self, value: int, bits: int):
		assert bits > 0
		assert value >= 0
		assert value < (1 << bits)
		self.value = value
		self.bits = bits




@dataclass
class VerilatorSignal:
	name: str
	typ: str
	dir: str

	def __le__(self, other):
		if isinstance(other, int):
			print(f"{self.name} <= int({other})")
		elif isinstance(other, bool):
			print(f"{self.name} <= bool({other})")
		else:
			assert False, f"Unexpected type: {other}"

def dict_to_module(module_data: dict, src: Optional[dict], reset: Optional[Any], submodules: Optional[dict]) -> VerilatorModule:
	assert submodules is None
	assert reset is None
	for cat in ['inputs', 'outputs', 'state', 'wires']:
		module_data[cat] = {name: to_signal_type(cat, name, *a) for name, a in module_data[cat].items()}
	if src is None: src = {'smt2': '', 'btor': '', 'v': ''}
	module_data['io_prefix'] = module_data.get('io_prefix', '')
	return Module(**module_data, reset=reset)

class VerilatorModule:
	@staticmethod
	def load(toplevel: str, src: List[str]) ->VerilatorModule:
		return load_module(name=toplevel, verilog_files=src, dict_to_mod=dict_to_module)


	def __init__(self, signals: Dict[str, VerilatorSignal]):
		self.signals = signals

	def __getattr__(self, item) -> VerilatorSignal:
		assert isinstance(item, str), f"Expected string not {type(item)} ({item})"
		return self.signals[item]

def expect(expr):
	assert expr

def ensure(expr):
	assert expr

def cat(a, b):
	raise NotImplementedError("TODO")
