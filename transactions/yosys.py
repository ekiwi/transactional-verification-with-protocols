#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, re, tempfile
from cache_to_disk import cache_to_disk
from itertools import chain
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

#@cache_to_disk(1)
def parse_verilog(filenames: List[str], top: str,  ignore_wires: bool = True, pre_mc_cmds= None, formats = None):
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
			if pre_mc_cmds is not None:	cmds += pre_mc_cmds
			cmds += [f"flatten", "setattr -unset keep"]
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
		module[key] = { ii[0]: (('bv', int(ii[1])), -1, ii[0])  for ii in res[key]}
	module['memories'] = { ii[0]: (('array', ('bv', int(ii[1])), ('bv', int(ii[2]))), -1, ii[0]) for ii in res['memories']}
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

	label_re = re.compile(r'\s*; (\d+) \\(\w+)')

	for line in btor_src.splitlines():
		if line.strip().startswith(';'):
			m = label_re.match(line.strip())
			if m is not None:
				ii, label = m.groups()
				nodes[int(ii)].append(label)
			continue
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

					# some lines have a trailing label
					if len(parts) > 2 + len(form):
						lbl = parts[2+len(form)]
						entry += [lbl]
					nodes[ii] = [name, cmd] + entry
					unknown = False
					break
			assert not unknown, f"command {cmd} is unknown"

	for ii, node in nodes.items():
		name = node[0]
		if name not in {'output', 'input', 'state'}: continue

		if name == 'output': sym_tpe = nodes[node[2]][2]
		else:                sym_tpe = node[2]
		if len(node) > 3:    sym_name = node[3]
		else:                sym_name = None
		# outputs will be deleted later on thus we want to refer to their source id instead
		if name == 'output':
			ii = node[2]

		if sym_name is not None:
			if name == 'state':
				key = 'registers' if sym_tpe[0] == 'bv' else 'memories'
			else:
				key = name + 's'
			res[key][sym_name] = (sym_tpe, ii, sym_name)

	res['ii'] = ii
	res['sorts'] = sorts
	res['symbols'] = {**res['registers'], **res['memories'], **res['inputs'], **res['outputs'], **res['wires']}
	return dict(res)

def merge_smt2_and_btor(smt2_names: dict, btor_names: dict) -> dict:
	mod = {'name': smt2_names['name']}
	mod['type'] = mod['name']
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
	# filter out sumodule i/o
	mod['inputs']  = { nn: ii for nn, ii in mod['inputs'].items()  if not ii[-1].startswith(ExposePrefix) }
	mod['outputs'] = { nn: ii for nn, ii in mod['outputs'].items() if not ii[-1].startswith(ExposePrefix) }
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
			mod = {'attributes': attributes, 'name': p[1], 'cells': {}, 'wires': {}, 'inputs': {}, 'outputs': {}, 'parameters': [], 'connects': []}
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
			typ = 'wire'
			name = p[-1]
			bits = 1
			for ii in range(1, len(p) - 1):
				if p[ii] == 'input': typ = 'input'
				if p[ii] == 'output': typ = 'output'
				if p[ii] == 'width': bits = int(p[ii + 1])
			mod[typ + 's'][name] = {'attributes': attributes, 'name': name, 'bits': bits}
		elif p[0] == 'parameter':
			param = {'attributes': attributes, 'name': p[1]}
			if cell is not None: cell['parameters'].append(param)
			else: mod['parameters'].append(param)
		elif p[0] == 'connect':
			con = {'attributes': attributes, 'lhs': p[1], 'rhs': p[2]}
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

ExposePrefix: str = "__EXP_"

def expose_modules(modules: dict, top: str, expose: List[str]):
	cmds = []
	submods = []
	for instance in expose:
		new_cmds, new_submods = expose_module(modules, top, instance)
		cmds += new_cmds
		submods += new_submods
	return cmds, submods

def expose_module(modules: dict, top: str, instance_name: str):
	assert '\\' + top in modules, f"could not find top module: {top} in {list(modules.keys())}"
	top_type = modules['\\' + top]
	top_cells = top_type['cells']
	assert '.' not in instance_name, f"can only expose direct submodules for now: {instance_name}"
	assert '\\' + instance_name in top_cells, f"could not find expose instance: {instance_name} in {list(top_cells.keys())}"

	instance = top_cells['\\' + instance_name]
	instance_type_name = instance['type'][1:]
	instance_type = modules['\\' + instance_type_name]

	# remember port names in order to avoid name clashes
	port_names = set(w['name'] for w in chain(top_type['inputs'].values(), top_type['outputs'].values()))

	cmds = []
	submods = []

	def add_port(p_mod, p_name: str, p_dir: str, p_bits: int):
		# p_dir is from the view of the module being exposed
		assert p_dir in {'input', 'output'}
		mangled_name = ExposePrefix + (p_mod['name'] + '_' + p_name).replace('\\', '')
		assert mangled_name not in port_names
		port_names.add(mangled_name)
		p_mod[p_dir + 's'][p_name] = (('bv', p_bits), -1, mangled_name)
		# invert direction to expose module at toplevel
		port_dir = "-input" if p_dir == 'out' else "-output"
		cmds.append(f"add {port_dir} {mangled_name} {p_bits}")
		return mangled_name

	con = instance['connects']
	mod = {'name': instance_name, 'type': instance_type_name, 'inputs': {}, 'outputs': {}, 'wires': {}, 'state': {},
		   'io_prefix': f"{ExposePrefix}{instance_name}_"}

	# add i/o
	for inp in instance_type['inputs'].values():
		toplevel_out = add_port(mod, inp['name'][1:], 'input', inp['bits'])
		instance_in = [cc for cc in con if cc['lhs'] == inp['name']]
		assert len(instance_in) > 0, f"could not find connection to {inp['name']} for instance {instance_name}: {con}"
		assert len(instance_in) < 2, f"found multiple: {instance_in}"
		# connect wire feeding the module to be exposed to the toplevel output
		cmds.append(f"connect -set {toplevel_out} {instance_in[0]['rhs']}")
	for out in instance_type['outputs'].values():
		toplevel_in = add_port(mod, out['name'][1:], 'output', out['bits'])
		instance_out = [cc for cc in con if cc['lhs'] == out['name']]
		assert len(instance_out) > 0, f"could not find connection from {out['name']} for instance {instance_name}: {con}"
		assert len(instance_out) < 2, f"found multiple: {instance_out}"
		# connect wire (formally) driven by module output to toplevel input
		cmds.append(f"connect -set {instance_out[0]['rhs']} {toplevel_in}")
	# delete cell
	cmds.append(f"delete {instance_name}")

	submods.append(mod)
	return cmds, submods