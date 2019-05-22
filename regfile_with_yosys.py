#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List, Tuple, Dict
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

def verilog_to_smt2(filename: str) -> str:
	assert os.path.isfile(filename)
	with tempfile.TemporaryDirectory() as dd:
		outfile = os.path.join(dd, "module.smt2")
		cmds = [f"read_verilog {filename}", "proc", "opt", "memory", f"write_smt2 {outfile}"]
		subprocess.run(['yosys', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		with open(outfile) as ff:
			smt2_src = ff.read()
	return smt2_src


def parse_yosys_smt2(smt2_src: str) -> dict:
	res = {
		'inputs': re.compile(r'; yosys-smt2-input ([^\s]+) ([\d+])'),
		'outputs': re.compile(r'; yosys-smt2-output ([^\s]+) ([\d+])'),
		'registers': re.compile(r'; yosys-smt2-register ([^\s]+) ([\d+])'),
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
		results[key] = {ii[0]: int(ii[1]) for ii in results[key]}
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
	def __init__(self, name: str, inputs: Dict[str,int], outputs: Dict[str,int], registers: Dict[str,int]):
		self._name = name
		self._inputs = inputs
		self._outputs = outputs
		self._registers = registers
	@property
	def name(self): return self._name

	def __str__(self):
		dd = [self._name, '-' * len(self._name), ""]
		def render_fields(fields)-> List[str]:
			return [f"{name}: {'bool' if bits == 1 else bits}" for name, bits in fields.items()]
		dd += ["Inputs:"] + render_fields(self._inputs) + [""]
		dd += ["Outputs:"] + render_fields(self._outputs) + [""]
		dd += ["Registers:"] + render_fields(self._registers)
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

	def get(self, name: str, state: "State") -> str:
		assert name in self._inputs or name in self._outputs or name in self._registers, f"Unknown io/state element {name}"
		return f"(|{self.name}_n {name}| |{state.name}|)"


class State:
	def __init__(self, name: str, module: Module):
		self.name = name
		self._mod = module

	def __str__(self):
		return f"(declare-fun |{self.name}| () {self._mod.state_t})"

	def __getitem__(self, name) -> str:
		return self._mod.get(name, self)



#class RegfileSpec:
#	def __init__(self):


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
	cmds += ["; memory should not change across the transition"]
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

	#print(regfile)

	proof = proof_no_mem_change(regfile)
	smt2_output = "proof.smt2"
	write_smt2(filename=smt2_output, yosysy_smt2=smt2_src, cmds=proof)

	print(f"wrote proof to {smt2_output}")
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
