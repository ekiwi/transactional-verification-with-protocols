#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List, Tuple, Dict

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



#class RegfileSpec:
#	def __init__(self):


regfile_v = os.path.join('serv', 'rtl', 'serv_regfile.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	smt2_src = verilog_to_smt2(regfile_v)
	smt2_names = parse_yosys_smt2(smt2_src)
	regfile = Module(**smt2_names)

	print(regfile)



	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
