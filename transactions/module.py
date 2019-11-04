from __future__ import annotations
import os
from dataclasses import dataclass
from typing import List,  Dict, Optional
from .spec import SmtSort
from pysmt.shortcuts import BOOL, BVType, ArrayType
from .yosys import parse_verilog, parse_yosys_smt2, parse_yosys_btor, merge_smt2_and_btor, parse_ilang, expose_module

@dataclass
class Reset:
	name: str
@dataclass
class HighActiveReset(Reset):
	pass
@dataclass
class LowActiveReset(Reset):
	pass

def to_signal_type(name, typ, nid, sym_name):
	if typ[0] == 'bv':
		return BVType(typ[1])
	elif typ[0] == 'array':
		assert typ[1][0] == 'bv'
		assert typ[2][0] == 'bv'
		return ArrayType(BVType(typ[1][1]), BVType(typ[2][1]))

def dict_to_module(module_data: dict, src: Optional[dict], reset: Optional[str], submodules: Optional[dict]) -> Module:
	for cat in ['inputs', 'outputs', 'state', 'wires']:
		module_data[cat] = {name: to_signal_type(name, *a) for name, a in module_data[cat].items()}
	if src is None: src = {'smt2': '', 'btor': '', 'v': ''}
	return Module(**module_data, smt2_src=src['smt2'], btor2_src=src['btor'], verilog_src=src['v'], submodules=submodules, reset=reset)

def load_module(name: str, verilog_files: List[str], reset:Optional[Reset], ignore_wires: bool, blackbox: Optional[List[str]]):
	for ff in verilog_files:
		assert os.path.isfile(ff), ff

	pre_mc_cmds = []
	submodules = {}
	if blackbox is not None and len(blackbox) > 0:
		for bb in blackbox:
			src = parse_verilog(verilog_files, top=name, ignore_wires=ignore_wires, formats=['ilang'],
								pre_mc_cmds=pre_mc_cmds)
			ilang_modules = parse_ilang(src['ilang'])
			cmds, submod_data = expose_module(ilang_modules, top=name, expose=bb)
			pre_mc_cmds += [f"select {name}"] + cmds + ["select *", "clean"]
			for data in submod_data:
				submod = dict_to_module(data, src=None, reset=None, submodules=None)
				submodules[submod.name] = submod

	src = parse_verilog(verilog_files, top=name, ignore_wires=ignore_wires, formats=['v', 'smt2', 'btor'], pre_mc_cmds=pre_mc_cmds)
	smt2_names = parse_yosys_smt2(src['smt2'])
	btor2_names = parse_yosys_btor(src['btor'])
	module_data = merge_smt2_and_btor(smt2_names, btor2_names)
	return dict_to_module(module_data, src, reset, submodules)


class Module:
	@staticmethod
	def load(name: str, verilog_files: List[str], reset:Optional[Reset] = None, ignore_wires: bool = True, blackbox: Optional[List[str]] = None):
		return load_module(name=name, verilog_files=verilog_files, reset=reset, ignore_wires=ignore_wires, blackbox=blackbox)

	def __init__(self, name: str, type: str, inputs: Dict[str,SmtSort], outputs: Dict[str,SmtSort], state: Dict[str,SmtSort],
	wires: Dict[str,SmtSort], smt2_src: str, btor2_src: str, verilog_src: str, submodules: Dict[str, Module],
	reset: Optional[Reset] = None):
		self._name = name
		self._type = type
		self.inputs = inputs
		self.outputs = outputs
		self.state = state
		self.wires = wires
		self.signals = {**self.wires, **self.state, **self.inputs, **self.outputs}
		self.smt2_src = smt2_src
		self.btor2_src = btor2_src
		self.verilog_src = verilog_src
		self.submodules = submodules if submodules is not None else {}
		for name, submod in self.submodules.items():
			self.signals = {**self.signals, **{f'{name}.{n}': s for n,s in submod.signals.items()}}
		self.reset = reset
		if self.reset is not None:
			assert self.reset.name in self.inputs, f"Reset signal `{self.reset}` not found in module inputs: {list(self.inputs.keys())}"

	@property
	def name(self): return self._name
	def is_input(self, name: str):
		return name in self.inputs
	def is_output(self, name: str):
		return name in self.outputs
	def is_state(self, name: str):
		return name in self.state

	@property
	def non_mem_state(self):
		return [s for s in self.state if not isinstance(s, ArraySignal)]

	def __str__(self):
		dd = [self._name, '-' * len(self._name), ""]
		def render_fields(fields)-> List[str]:
			return [str(ff) for ff in fields.values()]
		dd += ["Inputs:"] + render_fields(self.inputs) + [""]
		dd += ["Outputs:"] + render_fields(self.outputs) + [""]
		dd += ["State:"] + render_fields(self.state) + [""]
		dd += ["Wires:"] + render_fields(self.wires) + [""]
		return '\n'.join(dd)
	def __repr__(self): return str(self)