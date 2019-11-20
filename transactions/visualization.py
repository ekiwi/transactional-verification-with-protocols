#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations
from .spec import *
from pysmt.shortcuts import BV
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

def protocol_to_wavedrom(proto: Protocol) -> dict:
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

def protocol_to_wavedrom_file(filename: str, proto: Protocol):
	dd = protocol_to_wavedrom(proto)
	with open(filename, 'w') as ff:
		json.dump(dd, ff, indent=2)