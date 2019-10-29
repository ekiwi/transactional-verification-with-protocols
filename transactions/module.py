import os
from dataclasses import dataclass
from typing import List,  Dict, Optional
from pysmt.shortcuts import *

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

def to_signal(name, typ, nid, sym_name):
	if typ[0] == 'bv' and typ[1] == 1:
		return BoolSignal(name, nid, sym_name)
	elif typ[0] == 'bv':
		return BVSignal(name, typ[1], nid, sym_name)
	elif typ[0] == 'array':
		assert typ[1][0] == 'bv'
		assert typ[2][0] == 'bv'
		return ArraySignal(name, address_bits=typ[1][1], data_bits=typ[2][1], nid=nid, sym_name=sym_name)

def dict_to_module(module_data: dict, src: Optional[dict], reset: Optional[str], submodules: Optional[dict]) -> "Module":
	for cat in ['inputs', 'outputs', 'state', 'wires']:
		module_data[cat] = {name: to_signal(name, *a) for name, a in module_data[cat].items()}
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

	def __init__(self, name: str, type: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"],
	wires: Dict[str,"Signal"], smt2_src: str, btor2_src: str, verilog_src: str, submodules: Optional[Dict[str, "Module"]],
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

	def __getitem__(self, name: str):
		assert isinstance(name, str)
		assert name in self.signals, f"Unknown io/state element {name}.\nAvailable elements:{list(self.signals.keys())}"
		return self.signals[name].symbol

class Signal:
	def __init__(self, name: str, nid: int = -1, sym_name: Optional[str] = None):
		self.name = name
		self.tpe = None
		self.nid = nid
		self._sym_name = sym_name if sym_name is not None else self.name
	def __str__(self):
		return f"{self.name} : ?"

class BVSignal(Signal):
	def __init__(self, name: str, bits: int, nid: int = -1, sym_name: Optional[str] = None):
		super().__init__(name=name, nid=nid, sym_name=sym_name)
		self.bits = bits
		self.tpe = BVType(bits)
		self.symbol = Symbol(self._sym_name, self.tpe)
	def __str__(self):
		return f"{self.name} : bv<{self.bits}>"

class BoolSignal(Signal):
	def __init__(self, name: str, nid: int = -1, sym_name: Optional[str] = None):
		super().__init__(name=name, nid=nid, sym_name=sym_name)
		self.tpe = BOOL
		self.bits = 1
		self.symbol = Symbol(self._sym_name, self.tpe)
	def __str__(self):
		return f"{self.name} : bool"

# https://www.reddit.com/r/yosys/comments/39t2fl/new_support_for_memories_in_write_smt2_via_arrays/
class ArraySignal(Signal):
	def __init__(self, name: str, address_bits: int, data_bits: int, nid: int = -1, sym_name: Optional[str] = None):
		super().__init__(name=name, nid=nid, sym_name=sym_name)
		self.name = name
		self.address_bits = address_bits
		self.data_bits = data_bits
		self.tpe = ArrayType(BVType(self.address_bits), BVType(self.data_bits))
		self.symbol = Symbol(self._sym_name, self.tpe)
	@staticmethod
	def from_memory(name: str, address_bits: int, data_bits: int, read_ports: int, write_ports: int, async_read: bool):
		assert not async_read, "asynchronous memories are not supported!"
		return ArraySignal(name=name, address_bits=address_bits, data_bits=data_bits)
	@staticmethod
	def from_yosys(name: str, address_bits: str, data_bits: str, read_ports: str, write_ports: str, async_read: str):
		return ArraySignal.from_memory(name=name, address_bits=int(address_bits), data_bits=int(data_bits),
									   read_ports=int(read_ports), write_ports=int(write_ports),
									   async_read=(async_read == "async"))
	def __str__(self):
		return f"{self.name} : bv<{self.address_bits}> -> bv<{self.data_bits}>"