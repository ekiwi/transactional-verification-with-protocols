import os
from typing import List,  Dict, Optional
from pysmt.shortcuts import *

from .yosys import verilog_to_smt2_and_btor, parse_yosys_smt2, parse_yosys_btor
from .utils import *

class Module:
	@staticmethod
	def load(name: str, verilog_files: List[str], reset:Optional[str] = None, ignore_wires: bool = True):
		for ff in verilog_files:
			assert os.path.isfile(ff), ff
		smt2_src, btor_src = verilog_to_smt2_and_btor(verilog_files, top=name, arrays=True, ignore_wires=ignore_wires)
		smt2_names = parse_yosys_smt2(smt2_src, BVSignal.from_yosys, ArraySignal.from_yosys)
		#print(btor_src)
		parse_yosys_btor(btor_src, BVSignal.from_yosys, ArraySignal.from_yosys)
		return Module(**smt2_names, smt2_src=smt2_src, reset=reset)

	def __init__(self, name: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"], wires: Dict[str,"Signal"], smt2_src: str, reset: Optional[str] = None):
		self._name = name
		self._inputs = inputs
		self._outputs = outputs
		self._state = state
		self._wires = wires
		self.state_t = Type(name + "_s")
		self._transition_fun = Symbol(name + "_t", FunctionType(BOOL, [self.state_t, self.state_t]))
		self._inital_fun = Symbol(name + "_i", FunctionType(BOOL, [self.state_t]))
		self.smt2_src = smt2_src
		self.reset = reset
		if self.reset is not None:
			assert self.reset in self._inputs, f"Reset signal `{self.reset}` not found in module inputs: {list(self._inputs.keys())}"

	@property
	def name(self): return self._name

	def is_input(self, name: str):
		return name in self._inputs
	def is_output(self, name: str):
		return name in self._outputs
	def is_state(self, name: str):
		return name in self._state
	@property
	def inputs(self):
		return self._inputs.values()
	@property
	def outputs(self):
		return self._outputs.values()
	@property
	def wires(self):
		return self._wires.values()
	@property
	def state(self):
		return self._state.values()
	@property
	def non_mem_state(self):
		return [s for s in self.state if not isinstance(s, ArraySignal)]

	def __str__(self):
		dd = [self._name, '-' * len(self._name), ""]
		def render_fields(fields)-> List[str]:
			return [str(ff) for ff in fields.values()]
		dd += ["Inputs:"] + render_fields(self._inputs) + [""]
		dd += ["Outputs:"] + render_fields(self._outputs) + [""]
		dd += ["State:"] + render_fields(self._state) + [""]
		dd += ["Wires:"] + render_fields(self._wires) + [""]
		return '\n'.join(dd)
	def __repr__(self): return str(self)

	def declare_states(self, solver: Solver, names: List[str]) -> list:
		states = [State(name, self) for name in names]
		for state in states:
			solver.fun(state.sym)
		return states

	def initial(self, solver: Solver, state: "State"):
		assert state._mod == self
		solver.add(Function(self._inital_fun, [state.sym]))

	def transition(self, solver: Solver, states: List["State"]):
		assert all(state._mod == self for state in states)
		if len(states) < 2: return
		for ii in range((len(states) - 1)):
			solver.add(Function(self._transition_fun, [states[ii].sym, states[ii+1].sym]))

	def _get_signal(self, name: str) -> Optional["Signal"]:
		for dd in [self._inputs, self._outputs, self._state, self._wires]:
			if name in dd:
				return dd[name]
		return None

	def get(self, name: str, state: "State"):
		signal = self._get_signal(name=name)
		assert signal is not None, f"Unknown io/state element {name}"
		ft = FunctionType(signal.tpe, [self.state_t])
		if isinstance(signal, ArraySignal):
			fn = self.name + "_m " + signal.name
		else:
			fn = self.name + "_n " + signal.name
		return Function(Symbol(fn, ft), [state.sym])

class Signal:
	def __init__(self, name: str):
		self.name = name
		self.tpe = None

	def __str__(self):
		return f"{self.name} : ?"

class BVSignal(Signal):
	@staticmethod
	def from_yosys(name: str, bits: str):
		bits = int(bits)
		if bits == 1:
			return BoolSignal(name=name)
		assert bits > 1
		return BVSignal(name=name, bits=bits)

	def __init__(self, name: str, bits: int):
		super().__init__(name=name)
		self.bits = bits
		self.tpe = BVType(bits)

	def __str__(self):
		return f"{self.name} : bv<{self.bits}>"

class BoolSignal(Signal):
	def __init__(self, name: str):
		super().__init__(name=name)
		self.tpe = BOOL
		self.bits = 1
	def __str__(self):
		return f"{self.name} : bool"

# https://www.reddit.com/r/yosys/comments/39t2fl/new_support_for_memories_in_write_smt2_via_arrays/
class ArraySignal(Signal):
	def __init__(self, name: str, address_bits: int, data_bits: int):
		super().__init__(name=name)
		self.name = name
		self.address_bits = address_bits
		self.data_bits = data_bits
		self.tpe = ArrayType(BVType(self.address_bits), BVType(self.data_bits))
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


class State:
	def __init__(self, name: str, module: Module):
		self.name = name
		self.sym = Symbol(name, module.state_t)
		self._mod = module

	def __str__(self):
		return f"(declare-fun |{self.name}| () {self._mod.state_t})"

	def __getitem__(self, name) -> str:
		return self._mod.get(name, self)
