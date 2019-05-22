#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List, Tuple, Dict, Optional
from functools import reduce

# local hack (TODO: remove)
yosys_path = os.path.expanduser(os.path.join('~', 'd', 'yosys'))
os.environ['PATH'] = yosys_path + ":" + os.environ['PATH']


# yosys interface functions
def require_yosys() -> str:
	r = subprocess.run(['yosys', '-V'], stdout=subprocess.PIPE)
	assert r.returncode == 0, f"Failed to find yosys! {r}"
	version = re.match(r'Yosys (\d+\.\d+\+\d+)', r.stdout.decode('utf-8')).group(1)
	return version

def verilog_to_smt2(filename: str, arrays: bool = True) -> str:
	assert os.path.isfile(filename)
	with tempfile.TemporaryDirectory() as dd:
		outfile = os.path.join(dd, "module.smt2")
		mem = "memory -nomap -nordff" if arrays else "memory"
		cmds = [f"read_verilog {filename}", "proc", "opt", mem, f"write_smt2 {outfile}"]
		subprocess.run(['yosys', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		with open(outfile) as ff:
			smt2_src = ff.read()
	return smt2_src


def parse_yosys_smt2(smt2_src: str) -> dict:
	res = {
		'inputs': re.compile(r'; yosys-smt2-input ([^\s]+) ([\d+])'),
		'outputs': re.compile(r'; yosys-smt2-output ([^\s]+) ([\d+])'),
		'registers': re.compile(r'; yosys-smt2-register ([^\s]+) ([\d+])'),
		'memories': re.compile(r'; yosys-smt2-memory ([^\s]+) ([\d+]) ([\d+]) ([\d+]) ([\d+]) (async|sync)'),
		'modules': re.compile(r'; yosys-smt2-module ([^\s]+)')
	}
	results = defaultdict(list)
	for line in smt2_src.splitlines():
		for name, regex in res.items():
			m = regex.match(line)
			if m is not None:
				results[name].append(m.groups())
	results = dict(results)
	assert len(results['modules']) == 1, "Currently this software only works for single modules!"
	results['name'] = results['modules'][0][0]
	results.pop('modules')
	for key in ['inputs', 'outputs', 'registers']:
		results[key] = { ii[0]: BVSignal.from_yosys(*ii) for ii in results[key]}
	results['memories'] = { ii[0]: ArraySignal.from_yosys(*ii) for ii in results['memories']}
	results['state'] = {**results['memories'], **results['registers']}
	results.pop('memories')
	results.pop('registers')
	return results


def write_smt2(filename: str, yosysy_smt2: str, cmds: List[str]):
	with open(filename, 'w') as ff:
		print("(set-logic QF_AUFBV)", file=ff)
		print("; smt script generated using yosys + a custom python script", file=ff)
		print(file=ff)
		print("; yosys generated:", file=ff)
		print(yosysy_smt2, file=ff)
		print("; custom cmds", file=ff)
		print('\n'.join(cmds), file=ff)
		print("(check-sat)", file=ff)
		print("(get-model)", file=ff)

class Module:
	def __init__(self, name: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"]):
		self._name = name
		self._inputs = inputs
		self._outputs = outputs
		self._state = state
	@property
	def name(self): return self._name

	def __str__(self):
		dd = [self._name, '-' * len(self._name), ""]
		def render_fields(fields)-> List[str]:
			return [str(ff) for ff in fields.values()]
		dd += ["Inputs:"] + render_fields(self._inputs) + [""]
		dd += ["Outputs:"] + render_fields(self._outputs) + [""]
		dd += ["State:"] + render_fields(self._state) + [""]
		return '\n'.join(dd)
	def __repr__(self): return str(self)

	@property
	def state_t(self):
		return f"|{self._name}_s|"

	def declare_states(self, names: List[str]) -> List["State"]:
		return [State(name, self) for name in names]

	def transition(self, states: List["State"]):
		assert all(state._mod == self for state in states)
		if len(states) < 2: return []
		return [f"(assert (|{self._name}_t| |{states[ii].name}| |{states[ii+1].name}|))" for ii in range(len(states) - 1)]

	def _get_signal(self, name: str) -> Optional["Signal"]:
		for dd in [self._inputs, self._outputs, self._state]:
			if name in dd:
				return dd[name]
		return None

	def get(self, name: str, state: "State") -> str:
		signal = self._get_signal(name=name)
		assert signal is not None, f"Unknown io/state element {name}"
		if isinstance(signal, ArraySignal):
			return f"(|{self.name}_m {name}| |{state.name}|)"
		else:
			return f"(|{self.name}_n {name}| |{state.name}|)"

class Signal:
	def __init__(self, name: str):
		self.name = name

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

	def __str__(self):
		return f"{self.name} : bv<{self.bits}>"

class BoolSignal(Signal):
	def __init__(self, name: str):
		super().__init__(name=name)
	def __str__(self):
		return f"{self.name} : bool"

# https://www.reddit.com/r/yosys/comments/39t2fl/new_support_for_memories_in_write_smt2_via_arrays/
class ArraySignal(Signal):
	def __init__(self, name: str, address_bits: int, data_bits: int):
		super().__init__(name=name)
		self.name = name
		self.address_bits = address_bits
		self.data_bits = data_bits
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
		self._mod = module

	def __str__(self):
		return f"(declare-fun |{self.name}| () {self._mod.state_t})"

	def __getitem__(self, name) -> str:
		return self._mod.get(name, self)



"""
class RegfileSpec:
	def __init__(self):
		self.arch_state = { f'x{ii}': 32 for ii in range(32) }
		
"""



def assert_eq(e0: str, e1: str) -> List[str]:
	return [f"(assert (= {e0} {e1}))"]

def let_eq(name: str, e0: str, e1: str) -> List[str]:
	return [f"(define-fun |{name}| () Bool (= {e0} {e1}))"]

def proof_no_mem_change(regfile: Module) -> List[str]:
	cmds = []

	cmds += ["; declare states"]
	states = regfile.declare_states(['s1', 's2'])
	cmds += [str(state) for state in states]
	cmds += regfile.transition(states) + [""]

	start, end = states[0], states[-1]

	# setup assumptions
	cmds += ["; assuming that i_rd_en is false"]
	cmds += [f"(assert (not {start['i_rd_en']}))"]

	# assert that memory does not change
	use_arrays = True

	cmds += ["; memory should not change across the transition"]

	if use_arrays:
		cmds += [f"(define-fun |mem_eq| () Bool (= {start['memory']} {end['memory']}))"]
	else:
		for ii in range(16*32):
			cmds += let_eq(f'mem_{ii}_eq', start[f'memory[{ii}]'], end[f'memory[{ii}]'])
		all_eq = reduce(lambda a, b: f"(and {a} {b})", (f'|mem_{ii}_eq|' for ii in range(16*32)))
		cmds += [f"(define-fun |mem_eq| () Bool {all_eq})"]
	# assertions need to be negated in order to check for validity
	cmds += [f"(assert (not |mem_eq|))"]

	return cmds




regfile_v = os.path.join('serv', 'rtl', 'serv_regfile.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	smt2_src = verilog_to_smt2(regfile_v)
	smt2_names = parse_yosys_smt2(smt2_src)
	regfile = Module(**smt2_names)

	print(regfile)

	proof = proof_no_mem_change(regfile)
	smt2_output = "proof.smt2"
	write_smt2(filename=smt2_output, yosysy_smt2=smt2_src, cmds=proof)

	print(f"wrote proof to {smt2_output}")
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
