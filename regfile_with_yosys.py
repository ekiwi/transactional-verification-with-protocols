#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List, Tuple, Dict, Optional
from functools import reduce
from itertools import zip_longest
from pysmt.shortcuts import *
from pysmt.smtlib.script import SmtLibScript, smtcmd

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


def write_smt2(filename: str, yosysy_smt2: str, cmds: SmtLibScript):
	with open(filename, 'w') as ff:
		print("(set-logic QF_AUFBV)", file=ff)
		print("; smt script generated using yosys + a custom python script", file=ff)
		print(file=ff)
		print("; yosys generated:", file=ff)
		print(yosysy_smt2, file=ff)
		print("; custom cmds", file=ff)
		cmds.serialize(outstream=ff, daggify=False)
		print("(check-sat)", file=ff)
		print("(get-model)", file=ff)

class Module:
	def __init__(self, name: str, inputs: Dict[str,"Signal"], outputs: Dict[str,"Signal"], state: Dict[str,"Signal"]):
		self._name = name
		self._inputs = inputs
		self._outputs = outputs
		self._state = state
		self.state_t = Type(name + "_s")
		self._transition_fun = Symbol(name + "_t", FunctionType(BOOL, [self.state_t, self.state_t]))

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

	def declare_states(self, script: SmtLibScript, names: List[str]) -> list:
		states = [State(name, self) for name in names]
		for state in states:
			script.add(smtcmd.DECLARE_FUN, [state.sym])
		return states

	def transition(self, script: SmtLibScript, states: List["State"]):
		assert all(state._mod == self for state in states)
		if len(states) < 2: return
		for ii in range((len(states) - 1)):
			t = Function(self._transition_fun, [states[ii].sym, states[ii+1].sym])
			script.add(smtcmd.ASSERT, [t])

	def _get_signal(self, name: str) -> Optional["Signal"]:
		for dd in [self._inputs, self._outputs, self._state]:
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


def merge_dicts(a: dict, b: dict) -> dict:
	keys = a.keys() | b.keys()
	if len(keys) < len(a) + len(b):
		for k in keys:
			assert not (k in a and k in b), f"Key {k} is used in a and b!"
	return {**a, **b}

class Protocol:
	def __init__(self, mappings):
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

def BitSerial(signal: str, sym: Signal) -> Protocol:
	return Protocol([{signal: BVExtract(sym, ii, ii)} for ii in range(sym.bits)])

def Repeat(signal: str, sym: Signal, cycles) -> Protocol:
	return Protocol([{signal: sym}] * cycles)

def Map(signal:str, sym: Signal) -> Protocol:
	return Protocol([{signal: sym}])

class Transaction:
	def __init__(self, name: str, args: List[Signal], ret_args: List[Signal], proto: Protocol, semantics, mapping):
		self.name = name
		self.args = args
		self.ret_args = ret_args
		self.proto = proto
		self.semantics = semantics



class Spec:
	def __init__(self, arch_state, mapping, transactions, idle, invariances):
		self.arch_state = arch_state
		self.transactions = transactions
		self.idle = idle
		self.invariances = invariances
		self.mapping = mapping

class RegfileSpec(Spec):
	def __init__(self):
		x = ArraySignal('x', 5, 32)

		def mapping(state: State, x):
			asserts = []
			memory = state['memory']
			for ii in range(32):
				reg = Select(x, BV(ii, 5))
				for jj in range(16):
					a = Select(memory, BV(ii*16 + jj, 9))
					b = BVExtract(reg, start=jj*2, end=jj*2+1)
					asserts.append(Equals(a, b))
			return asserts

		# build transaction
		rs1_addr = BVSignal('rs1_addr', 5)
		rs2_addr = BVSignal('rs2_addr', 5)
		rd_enable = BoolSignal('rd_enable')
		rd_addr = BVSignal('rd_addr', 5)
		rd_data = BVSignal('rd_data', 32)
		args = [rs1_addr, rs2_addr, rd_enable, rd_addr, rd_data]
		rs1_data = BVSignal('rs1_data', 32)
		rs2_data = BVSignal('rs2_data', 32)
		ret = [rs1_data, rs2_data]

		protocol = (Map('i_go', 1) +
			       (BitSerial('i_rd', rd_data) | BitSerial('o_rs1', rs1_data)     | BitSerial('o_rs2', rs2_data) |
		            Repeat('i_go', 0, 32)      | Repeat('i_rd_en', rd_enable, 32) | Repeat('i_rd_addr', rd_addr, 32) |
		            Repeat('i_rs1_addr', rs1_addr, 32) | Repeat('i_rs2_addr', rs2_addr, 32)))


		def semantics(rs1_addr, rs2_addr, rd_enable, rd_addr, rd_data, x):
			rs1_data = Select(x, rs1_addr)
			rs2_data = Select(x, rs2_addr)
			x_n = Ite(rd_enable, Store(x, rd_addr, rd_data), x)
			return { 'rs1_data': rs1_data, 'rs2_data': rs2_data, 'x': x_n}

		transactions = [Transaction(name="rw", args=args, ret_args=ret, semantics=semantics, proto=protocol)]

		idle = {'i_go': 0, 'i_rd_en': 0}

		# TODO: infer
		inv = {'wcnt': 0}
		super().__init__(arch_state={'x': x}, mapping=mapping, transactions=transactions, idle=idle, invariances=inv)




def proof_no_mem_change(regfile: Module, script: SmtLibScript):
	states = regfile.declare_states(script, ['s1', 's2'])
	regfile.transition(script, states)

	start, end = states[0], states[-1]

	# setup assumptions
	# assuming that i_rd_en is false
	script.add(smtcmd.ASSERT, [Not(start['i_rd_en'])])

	# assert that memory does not change
	script.add(smtcmd.ASSERT, [Not(Equals(start['memory'], end['memory']))])


class ProofEngine:
	def __init__(self, mod: Module, spec: Spec):
		self.mod = mod
		self.spec = spec

	def proof_invariances(self):
		raise RuntimeError("TODO")


regfile_v = os.path.join('serv', 'rtl', 'serv_regfile.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	smt2_src = verilog_to_smt2(regfile_v)
	smt2_names = parse_yosys_smt2(smt2_src)
	regfile = Module(**smt2_names)

	print(regfile)

	script = SmtLibScript()
	proof_no_mem_change(regfile, script)
	smt2_output = "proof.smt2"

	write_smt2(filename=smt2_output, yosysy_smt2=smt2_src, cmds=script)

	print(f"wrote proof to {smt2_output}")
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
