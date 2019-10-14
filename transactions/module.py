import os
from typing import List,  Dict, Optional
from pysmt.shortcuts import *

from .yosys import parse_verilog, parse_yosys_smt2, parse_yosys_btor, merge_smt2_and_btor, parse_ilang, expose_module


def to_signal(name, typ, nid):
	if typ[0] == 'bv' and typ[1] == 1:
		return BoolSignal(name, nid)
	elif typ[0] == 'bv':
		return BVSignal(name, typ[1], nid)
	elif typ[0] == 'array':
		assert typ[1][0] == 'bv'
		assert typ[2][0] == 'bv'
		return ArraySignal(name, address_bits=typ[1][1], data_bits=typ[2][1], nid=nid)


class Module:
	@staticmethod
	def load(name: str, verilog_files: List[str], reset:Optional[str] = None, ignore_wires: bool = True):
		for ff in verilog_files:
			assert os.path.isfile(ff), ff
		src = parse_verilog(verilog_files, top=name, arrays=True, ignore_wires=ignore_wires)

		# DEBUG
		if name == 'serv_top':
			ilang_modules = parse_ilang(src['ilang'])
			cmds = expose_module(ilang_modules, top=name, expose='serv_regfile')



		smt2_names = parse_yosys_smt2(src['smt2'])
		btor2_names = parse_yosys_btor(src['btor'])
		module_data = merge_smt2_and_btor(smt2_names, btor2_names)
		for cat in ['inputs', 'outputs', 'state', 'wires']:
			module_data[cat] = {name: to_signal(name, *a) for name, a in module_data[cat].items()}
		return Module(**module_data, smt2_src=src['smt2'], btor2_src=src['btor'], verilog_src=src['v'], reset=reset)

	def __init__(self, name: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"], wires: Dict[str,"Signal"], smt2_src: str, btor2_src: str, verilog_src: str, reset: Optional[str] = None):
		self._name = name
		self.inputs = inputs
		self.outputs = outputs
		self.state = state
		self.wires = wires
		self.signals = {**self.wires, **self.state, **self.inputs, **self.outputs}
		self.smt2_src = smt2_src
		self.btor2_src = btor2_src
		self.verilog_src = verilog_src
		self.reset = reset
		if self.reset is not None:
			assert self.reset in self.inputs, f"Reset signal `{self.reset}` not found in module inputs: {list(self.inputs.keys())}"

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
	def __init__(self, name: str, nid: int = -1):
		self.name = name
		self.tpe = None
		self.nid = nid
	def __str__(self):
		return f"{self.name} : ?"

class BVSignal(Signal):
	def __init__(self, name: str, bits: int, nid: int = -1):
		super().__init__(name=name, nid=nid)
		self.bits = bits
		self.tpe = BVType(bits)
		self.symbol = Symbol(self.name, self.tpe)
	def __str__(self):
		return f"{self.name} : bv<{self.bits}>"

class BoolSignal(Signal):
	def __init__(self, name: str, nid: int = -1):
		super().__init__(name=name, nid=nid)
		self.tpe = BOOL
		self.bits = 1
		self.symbol = Symbol(self.name, self.tpe)
	def __str__(self):
		return f"{self.name} : bool"

# https://www.reddit.com/r/yosys/comments/39t2fl/new_support_for_memories_in_write_smt2_via_arrays/
class ArraySignal(Signal):
	def __init__(self, name: str, address_bits: int, data_bits: int, nid: int = -1):
		super().__init__(name=name, nid=nid)
		self.name = name
		self.address_bits = address_bits
		self.data_bits = data_bits
		self.tpe = ArrayType(BVType(self.address_bits), BVType(self.data_bits))
		self.symbol = Symbol(self.name, self.tpe)
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