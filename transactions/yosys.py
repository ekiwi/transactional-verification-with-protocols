#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from collections import defaultdict
from typing import List

# local hack (TODO: remove)
yosys_path = os.path.expanduser(os.path.join('~', 'd', 'yosys'))
os.environ['PATH'] = yosys_path + ":" + os.environ['PATH']


# yosys interface functions
def require_yosys() -> str:
	r = subprocess.run(['yosys', '-V'], stdout=subprocess.PIPE)
	assert r.returncode == 0, f"Failed to find yosys! {r}"
	version = re.match(r'Yosys (\d+\.\d+\+\d+)', r.stdout.decode('utf-8')).group(1)
	return version

def verilog_to_smt2_and_btor(filenames: List[str], top: str,  arrays: bool = True, ignore_wires: bool = True) -> str:
	for ff in filenames:
		assert os.path.isfile(ff), ff
	with tempfile.TemporaryDirectory() as dd:
		outfile = os.path.join(dd, "module.smt2")
		btor_out = os.path.join(dd, "module.btor")
		mem = "memory -nomap -nordff" if arrays else "memory"
		wires = "" if ignore_wires else "-wires"
		cmds  = [f"read_verilog {ff}" for ff in filenames]
		cmds += [f"hierarchy -top {top}", "proc", "opt", "flatten", "opt", mem, f"write_smt2 {wires} {outfile}"]
		cmds += [f"write_btor {btor_out}"]
		subprocess.run(['yosys', '-DRISCV_FORMAL', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		with open(outfile) as ff:
			smt2_src = ff.read()
		with open(btor_out) as ff:
			btor_src = ff.read()
	return smt2_src, btor_src

def parse_yosys_smt2(smt2_src: str, mk_bv_signal, mk_array_signal) -> dict:
	res = {
		'inputs': re.compile(r'; yosys-smt2-input ([^\s]+) ([\d+])'),
		'outputs': re.compile(r'; yosys-smt2-output ([^\s]+) ([\d+])'),
		'registers': re.compile(r'; yosys-smt2-register ([^\s]+) ([\d+])'),
		'memories': re.compile(r'; yosys-smt2-memory ([^\s]+) ([\d+]) ([\d+]) ([\d+]) ([\d+]) (async|sync)'),
		'modules': re.compile(r'; yosys-smt2-module ([^\s]+)'),
		'wires': re.compile(r'; yosys-smt2-wire ([^\s]+) ([\d+])'),
	}
	results = defaultdict(list)
	for line in smt2_src.splitlines():
		for name, regex in res.items():
			m = regex.match(line)
			if m is not None:
				results[name].append(m.groups())
	assert len(results['modules']) == 1, "Currently this software only works for single modules!"
	results['name'] = results['modules'][0][0]
	for key in ['inputs', 'outputs', 'registers', 'wires']:
		results[key] = { ii[0]: mk_bv_signal(*ii) for ii in results[key]}
	results['memories'] = { ii[0]: mk_array_signal(*ii) for ii in results['memories']}
	results['state'] = {**results['memories'], **results['registers']}
	results = dict(results)
	results.pop('modules')
	results.pop('memories')
	results.pop('registers')
	return results

def parse_yosys_btor(btor_src: str, mk_bv_signal, mk_array_signal) -> dict:
	res = [
		('input', {'input'}, ('sid', 'str')),
		('state', {'state'}, ('sid', 'str')),
		('output', {'output'}, ('nid', 'str')),
		('op', {'not', 'inc', 'dec', 'neg', 'redand', 'redor', 'redxor'}, ('sid', 'nid')),
		('op', {'uext', 'sext'}, ('sid', 'nid', 'int')),
		('op', {'slice'}, ('sid', 'nid', 'int', 'int')),
		('op', {'iff', 'implies', 'eq', 'neq', 'sgt', 'ugt', 'sgte', 'ugte', 'slt', 'ult', 'slte', 'ulte',
				'and', 'nand', 'nor', 'or', 'xnor', 'xor', 'rol', 'ror', 'sll', 'sra', 'srl',
				'add', 'mul', 'sdiv', 'udiv', 'smod', 'srem', 'urem', 'sub',
				'saddo', 'uaddo', 'sdivo', 'udivo', 'smulo', 'umulo', 'ssubo', 'usubo',
				'concat', 'read'}, ('sid', 'nid', 'nid')),
		('op', {'ite', 'write'}, ('sid', 'nid', 'nid', 'nid')),
		('const', {'const'}, ('sid', 'int'))

	]
	results = defaultdict(list)
	sorts = {}
	nodes = {}

	for line in btor_src.splitlines():
		if line.strip().startswith(';'): continue
		parts = line.split(' ')
		ii = int(parts[0])
		cmd = parts[1]
		if cmd == 'sort':
			if parts[2] == 'bitvec':
				entry = ('bv', int(parts[3]))
			else:
				assert parts[2] == 'array'
				entry = ('array', sorts[int(parts[3])], sorts[int(parts[4])])
			sorts[ii] = entry
		else:
			for name, keywords, form in res:
				if cmd in keywords:
					entry = []
					for value, ff in zip(parts[2:], form):
						if ff == 'str': entry.append(value)
						elif ff == 'int': entry.append(int(value))
						elif ff == 'sid': entry.append(sorts[int(value)])
						elif ff == 'nid': entry.append(int(value))
						else: raise RuntimeError(f"unknown format {ff}")
					nodes[ii] = [cmd] + entry

					if len(parts) > 2 + len(form):
						name = parts[2+len(form)]
						results['wires'].append((ii, entry[0], name))

					# for outputs, get type
					if cmd == 'output':
						entry = [nodes[entry[0]][1]] + entry
					if name in {'output', 'input', 'state'}:
						results[name + "s"].append(tuple([ii] + entry))

	return dict(results)