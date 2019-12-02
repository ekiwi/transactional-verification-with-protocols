#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from .spec import *
from pysmt.shortcuts import BV
import functools, itertools
import json



def append_mappings(mapping: Dict[str, SmtExpr], signals: Dict[str, Tuple[int, List[str], List[str]]]):
	for name, (bits, wave, data, last) in signals.items():
		next_data = ''
		if name not in mapping:
			next_wave = 'x'
		else:
			e = mapping[name]
			if e == BV(0, 1):   next_wave = '0'
			elif e == BV(1, 1): next_wave = '1'
			else:
				next_wave = '2'
				next_data = str(e)

		next_str = next_wave + next_data
		if last[0] == next_str:
			wave.append('.')
		else:
			last[0] = next_str
			wave.append(next_wave)
			if len(next_data) > 0: data.append(next_data)

def protocol_to_wavedrom(proto: LegacyProtocol) -> dict:
	""" https://wavedrom.com/editor.html """
	inputs, outputs = {}, {}
	get_name = lambda n, e, dir: f"{n} : {dir}(UInt({e.get_type().width}.W))"
	for tt in proto.transitions:
		ii = {n: (get_name(n,e,"Input"), [], [], [""]) for n, e in tt.inputs.items()}
		oo = {n: (get_name(n,e,"Output"), [], [], [""]) for n, e in tt.outputs.items()}
		inputs = {**ii, **inputs}
		outputs = {**oo, **outputs}

	for tt in proto.transitions:
		append_mappings(tt.inputs, inputs)
		append_mappings(tt.outputs, outputs)

	clk = ('clk : Input(Clock)', ['P'] + ['.'] * (len(proto.transitions) - 1), [], [])
	config = {'hscale': 3}

	signals = [clk] + sorted(list(inputs.values()) + list(outputs.values()), key=lambda s: s[0])
	dd = {'signal': [ {'name': name, 'wave': ''.join(wave), 'data': data} for (name, wave, data, _) in signals], 'config': config}
	return dd

def get_x(length: int) -> List[str]:
	assert length > 0
	return ['x'] + ['.'] * (length - 1)

def concat(a: dict, b: dict) -> dict:
	if 'config' in a and 'config' in b:
		assert a['config'] == b['config']
	config = a.get('config', b.get('config', {}))

	a_signals = {s['name']: (s['wave'], s['data']) for s in a['signal']}
	b_signals = {s['name']: (s['wave'], s['data']) for s in b['signal']}
	signal_names = sorted(list(set(a_signals.keys()) | set(b_signals.keys())))

	a_x = ''.join(get_x(len(a['signal'][0]['wave'])))
	b_x = ''.join(get_x(len(b['signal'][0]['wave'])))

	signal = [{
		'name': n,
		'wave': a_signals.get(n, (a_x, None))[0] + b_signals.get(n, (b_x, None))[0],
		'data': a_signals.get(n, (None, []))[1]  + b_signals.get(n, (None, []))[1],
		} for n in signal_names]

	return {'signal': signal, 'config': config}

def trace_to_wavedrom(trace: List[Transaction], start_id: int = 1) -> dict:
	waveforms = [protocol_to_wavedrom(tt.proto) for tt in trace]
	dd = functools.reduce(concat, waveforms)

	# label transactions
	lbls = [f"{ii+start_id}<->{ii+start_id+1} {tt.name}" for ii, tt in enumerate(trace)]
	nodes = ''.join(str(ii+start_id) + ("." * (len(tt.proto.transitions) - 1)) for ii, tt in enumerate(trace))
	nodes += str(len(trace)+start_id)
	dd['signal'].append({'node': nodes})
	dd['edge'] = lbls + dd.get('edge', [])
	return dd

def composition_to_wavedrom(toplevel: str, tran: Transaction, traces: Dict[str, List[Transaction]]) -> dict:
	top = protocol_to_wavedrom(tran.proto)
	offsets = [0] + list(itertools.accumulate(len(tt)+1 for tt in traces.values()))
	sub = [(name, trace_to_wavedrom(trace, o+1)) for o, (name, trace) in zip(offsets, traces.items())]

	signal = [[toplevel] + top['signal'] + [{}]] + [[name] + dd['signal'] + [{}] for name, dd in sub]
	edges = top.get('edge', []) + functools.reduce(lambda a,b: a+b, (s[1].get('edge', []) for s in sub))
	dd = {'signal': signal, 'config': top['config'], 'edge': edges}
	return dd

def protocol_to_wavedrom_file(filename: str, proto: LegacyProtocol):
	dd = protocol_to_wavedrom(proto)
	with open(filename, 'w') as ff:
		json.dump(dd, ff, indent=2)