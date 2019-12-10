from __future__ import annotations
import os
from typing import List,  Dict, Optional, Set
from .spec import SmtSort, RtlModule, Reset, HighActiveReset, LowActiveReset
from pysmt.shortcuts import BVType, ArrayType
from .yosys import parse_verilog, parse_yosys_smt2, parse_yosys_btor, merge_smt2_and_btor, parse_ilang, expose_modules

ResetSignalNames = ['reset', 'rst', 'i_rst']

def to_signal_type(name, typ, nid, sym_name):
	if typ[0] == 'bv':
		return BVType(typ[1])
	elif typ[0] == 'array':
		assert typ[1][0] == 'bv'
		assert typ[2][0] == 'bv'
		return ArrayType(BVType(typ[1][1]), BVType(typ[2][1]))

def dict_to_module(module_data: dict, src: Optional[dict], reset: Optional[Reset], submodules: Optional[dict]) -> Module:
	for cat in ['inputs', 'outputs', 'state', 'wires']:
		module_data[cat] = {name: to_signal_type(name, *a) for name, a in module_data[cat].items()}
	if src is None: src = {'smt2': '', 'btor': '', 'v': ''}
	module_data['io_prefix'] = module_data.get('io_prefix', '')
	return Module(**module_data, smt2_src=src['smt2'], btor2_src=src['btor'], verilog_src=src['v'], submodules=submodules, reset=reset)

def load_module(name: str, verilog_files: List[str], ignore_wires: bool, blackbox: Optional[List[str]], high_active_reset=True, dict_to_mod=dict_to_module):
	for ff in verilog_files:
		assert os.path.isfile(ff), ff

	cmds = []
	submodules = {}
	if blackbox is not None and len(blackbox) > 0:
		src = parse_verilog(verilog_files, top=name, ignore_wires=ignore_wires, formats=['ilang'])
		ilang_modules = parse_ilang(src['ilang'])
		cmds, submod_data = expose_modules(ilang_modules, top=name, expose=blackbox)
		cmds = [f"select {name}"] + cmds + ["select *", "clean"]
		for subname, data in submod_data.items():
			submodules[subname] = dict_to_module(data, src=None, reset=find_reset(data, high_active_reset), submodules=None)

	src = parse_verilog(verilog_files, top=name, ignore_wires=ignore_wires, formats=['v', 'smt2', 'btor'], pre_mc_cmds=cmds)
	smt2_names = parse_yosys_smt2(src['smt2'])
	btor2_names = parse_yosys_btor(src['btor'])
	module_data = merge_smt2_and_btor(smt2_names, btor2_names)
	reset = find_reset(module_data, high_active_reset)
	return dict_to_mod(module_data, src, reset, submodules)


class Module(RtlModule):
	@staticmethod
	def load(name: str, verilog_files: List[str], ignore_wires: bool = True, blackbox: Optional[List[str]] = None, high_active_reset=True):
		return load_module(name=name, verilog_files=verilog_files, ignore_wires=ignore_wires, blackbox=blackbox, high_active_reset=high_active_reset)

	def __init__(self, name: str, inputs: Dict[str,SmtSort], outputs: Dict[str,SmtSort], state: Dict[str,SmtSort],
	wires: Dict[str,SmtSort], smt2_src: str, btor2_src: str, verilog_src: str, submodules: Dict[str, Module],
	reset: Optional[Reset] = None, io_prefix: str = ""):
		self._name = name
		self.io_prefix = io_prefix
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

def find_reset(module_data: dict, high_active_reset: bool) -> Reset:
	reset_name = find_pin(set(module_data['inputs'].keys()), ResetSignalNames)
	return HighActiveReset(reset_name) if high_active_reset else LowActiveReset(reset_name)

def find_pin(names: Set[str], candidates: List[str]) -> str:
	names_lower = {nn.lower() for nn in names}
	for name in candidates:
		if name in names:
			return name
	for name in candidates:
		if name.lower() in names:
			return name
	for name in candidates:
		for pp in names:
			if name in pp:
				return pp
	for name in candidates:
		for pp in names_lower:
			if name.lower() in pp:
				return pp
	raise RuntimeError(f"Failed ot find pin in {pins} (candidates: {candidates})")