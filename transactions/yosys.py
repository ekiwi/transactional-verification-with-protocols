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

def verilog_to_smt2(filenames: List[str], top: str,  arrays: bool = True, ignore_wires: bool = True) -> str:
	for ff in filenames:
		assert os.path.isfile(ff), ff
	with tempfile.TemporaryDirectory() as dd:
		outfile = os.path.join(dd, "module.smt2")
		mem = "memory -nomap -nordff" if arrays else "memory"
		wires = "" if ignore_wires else "-wires"
		cmds  = [f"read_verilog {ff}" for ff in filenames]
		cmds += [f"hierarchy -top {top}", "proc", "opt", "flatten", "opt", mem, f"write_smt2 {wires} {outfile}"]
		subprocess.run(['yosys', '-DRISCV_FORMAL', '-p', '; '.join(cmds)], stdout=subprocess.PIPE, check=True)
		with open(outfile) as ff:
			smt2_src = ff.read()
	return smt2_src


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

