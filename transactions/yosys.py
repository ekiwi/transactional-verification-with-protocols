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
		wires = "" if ignore_wires else "-wires"
		cmds  = [f"read_verilog -sv -defer {ff}" for ff in filenames]
		cmds += [f"prep -flatten -nordff -top {top}", "setattr -unset keep", f"write_smt2 {wires} {outfile}"]
		cmds += [f"write_btor -v {btor_out}"]
		subprocess.run(['yosys', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		#'-DRISCV_FORMAL',
		with open(outfile) as ff:
			smt2_src = ff.read()
		with open(btor_out) as ff:
			btor_src = ff.read()
	return smt2_src, btor_src

def parse_yosys_smt2(smt2_src: str) -> dict:
	grammar = {
		'inputs': re.compile(r'; yosys-smt2-input ([^\s]+) ([\d]+)'),
		'outputs': re.compile(r'; yosys-smt2-output ([^\s]+) ([\d]+)'),
		'registers': re.compile(r'; yosys-smt2-register ([^\s]+) ([\d]+)'),
		'memories': re.compile(r'; yosys-smt2-memory ([^\s]+) ([\d]+) ([\d]+) ([\d]+) ([\d]+) (async|sync)'),
		'modules': re.compile(r'; yosys-smt2-module ([^\s]+)'),
		'wires': re.compile(r'; yosys-smt2-wire ([^\s]+) ([\d]+)'),
	}
	res = defaultdict(list)
	for line in smt2_src.splitlines():
		for name, regex in grammar.items():
			m = regex.match(line)
			if m is not None:
				res[name].append(m.groups())
	assert len(res['modules']) == 1, "Currently this software only works for single modules!"
	module = {'name': res['modules'][0][0]}
	for key in ['inputs', 'outputs', 'registers', 'wires']:
		module[key] = { ii[0]: (('bv', int(ii[1])), -1)  for ii in res[key]}
	module['memories'] = { ii[0]: (('array', ('bv', int(ii[1])), ('bv', int(ii[2]))), -1) for ii in res['memories']}
	return module

def parse_yosys_btor(btor_src: str) -> dict:
	grammar = [
		('input', {'input'}, ('sid', 'str')),
		('state', {'state'}, ('sid', 'str')),
		('output', {'output'}, ('nid', 'str')),
		('next', {'next'}, ('sid', 'nid', 'nid')),
		('init', {'init'}, ('sid', 'nid', 'nid')),
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
	res = defaultdict(dict)
	sorts = {}
	nodes = {}
	ii = -1

	for line in btor_src.splitlines():
		if line.strip().startswith(';'): continue
		parts = line.strip().split(' ')
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
			unknown = True
			for name, keywords, form in grammar:
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
						res['wires'][name] = (entry[0], ii)

					# for outputs, get type
					if name == 'output':
						name = entry[1]
						src = nodes[entry[0]]
						res['outputs'][name] = (src[1], entry[0])
					elif name in {'state', 'output', 'input'}:
						key = "register" if entry[0][0] == 'bv' else "memorie"
						key = key if name == 'state' else name
						# filter out unnamed signals
						if len(entry) > 1:
							res[key + "s"][entry[1]] = (entry[0], ii)
					unknown = False
					break
			assert not unknown, f"command {cmd} is unknown"
	res['ii'] = ii
	res['sorts'] = sorts
	res['symbols'] = {**res['registers'], **res['memories'], **res['inputs'], **res['outputs'], **res['wires']}
	return dict(res)

def merge_smt2_and_btor(smt2_names: dict, btor_names: dict) -> dict:
	mod = {'name': smt2_names['name']}
	for cat in ['inputs', 'outputs', 'registers', 'memories', 'wires']:
		mod[cat] = {}
		for name, args in smt2_names[cat].items():
			if name not in btor_names[cat] and cat in {'registers', 'wires'}:
				print(f"WARN: {cat} {name} missing form btor. Ignoring for now...")
				continue
			assert name in btor_names[cat], f"{cat} {name} missing form btor"
			bnode = btor_names[cat][name]
			assert args[0] ==  bnode[0], f"types of {cat} {name} do not match: {args[0]} vs {bnode[0]}"
			assert bnode[1] > 0, f"node id of {cat} {name} is {bnode[1]} <= 0"
			mod[cat][name] = bnode
	mod['state'] = { **mod['registers'], **mod['memories'] }
	mod.pop('registers')
	mod.pop('memories')
	return mod