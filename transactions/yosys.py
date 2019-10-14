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

def parse_verilog(filenames: List[str], top: str,  arrays: bool = True, ignore_wires: bool = True, formats = None):
	for ff in filenames:
		assert os.path.isfile(ff), ff
	available_formats = ['smt2', 'btor', 'v', 'ilang']
	if formats is None:
		formats = available_formats
	else:
		for ff in formats: assert ff in available_formats, f"Invalid format: {ff}"
	with tempfile.TemporaryDirectory() as dd:
		outprefix = os.path.join(dd, top)
		cmds  = [f"read_verilog -sv -defer {ff}" for ff in filenames]
		cmds += [f"prep -nordff -top {top}"]
		if 'v' in formats: cmds += [f"write_verilog {outprefix}.v"]
		if 'ilang' in formats: cmds += [f"write_ilang {outprefix}.ilang"]
		if 'smt2' in formats or 'btor' in formats:
			cmds += [f"prep -flatten -nordff -top {top}", "setattr -unset keep"]
			if 'smt2' in formats:
				wires = "" if ignore_wires else "-wires"
				cmds += [f"write_smt2 {wires} {outprefix}.smt2"]
			if 'btor' in formats: cmds += [f"write_btor -v {outprefix}.btor"]
		subprocess.run(['yosys', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		#'-DRISCV_FORMAL',
		src = {}
		for suffix in formats:
			with open(outprefix + '.' + suffix) as ff:
				src[suffix] = ff.read()
	return src

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
				if cat != 'wires':
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


def parse_ilang(ilang_src: str) -> dict:
	modules = {}
	attributes = {}
	mod = None
	cell = None

	for line in ilang_src.split('\n'):
		p = line.strip().split(' ')
		# skip comments
		if p[0] == '#': continue
		# skip empty lines
		if len(p) == 1 and p[0].strip() == '': continue

		# parse commands
		if p[0] == 'attribute':
			attributes[p[2]] = p[2:]
		elif p[0] == 'module':
			assert mod is None
			mod = {'attributes': attributes, 'name': p[1], 'cells': {}, 'wires': {}, 'parameters': [], 'connects': []}
		elif p[0] == 'cell':
			assert cell is None
			cell = {'attributes': attributes, 'type': p[1], 'name': p[2], 'parameters': [], 'connects': []}
		elif p[0] == 'end':
			if cell is not None:
				mod['cells'][cell['name']] = cell
				cell = None
			else:
				assert mod is not None
				modules[mod['name']] = mod
				mod = None
		elif p[0] == 'wire':
			assert cell is None
			if len(p) == 2:
				wire = {'attributes': attributes, 'name': p[1], 'direction': 'width', 'bits': 1}
			else:
				wire = {'attributes': attributes, 'direction': p[1], 'bits': int(p[2]), 'name': p[3]}
			mod['wires'][wire['name']] = wire
		elif p[0] == 'parameter':
			param = {'attributes': attributes, 'name': p[1]}
			if cell is not None: cell['parameters'].append(param)
			else: mod['parameters'].append(param)
		elif p[0] == 'connect':
			con = {'attributes': attributes, 'lhs': p[1], 'rhs': p[1]}
			if cell is not None: cell['connects'].append(con)
			else: mod['connects'].append(con)
		elif p[0] in {'autoidx'}:
			pass # ignore
		else:
			raise RuntimeError(f"Unexpected command `{p[0]}` in {line}")
		# reset attributes
		if p[0] != 'attribute':
			attributes = {}

	assert cell is None
	assert mod is None
	assert len(attributes) == 0
	return modules

def expose_module(modules: dict, top: str, expose: str) -> list:
	assert '\\' + top in modules, f"could not find top module: {top} in {list(modules.keys())}"
	assert '\\' + expose in modules, f"could not find expose module: {expose} in {list(modules.keys())}"

	tmod = modules['\\' + top]
	instances = [c for c in tmod['cells'].values() if c['type'] == '\\' + expose]
	assert len(instances) > 0, f"could not find any instance of {expose} in {top}"

	# remember port names in order to avoid name clashes
	port_names = set(w['name'] for w in tmod['wires'].values() if w['direction'] in {'input', 'output'})

	cmds = []
	for ii in instances:
		print(ii['name'])
		con = ii['connects']

