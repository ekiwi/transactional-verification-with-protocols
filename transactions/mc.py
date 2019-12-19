#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, tempfile, time, re
from collections import defaultdict
from itertools import chain

from cache_to_disk import cache_to_disk
from typing import Optional
from pysmt.shortcuts import Symbol, BVType, BV, BVAdd, Not, Equals, Implies, BOOL, ArrayType
from pysmt.walkers import DagWalker

from .module import Module
from .yosys import parse_yosys_btor
from .utils import equal, default
from .bounded import BoundedCheckData, CheckSuccess, CheckFailure, Model

class MCProofEngine:
	def __init__(self, outdir=None):
		self.name = "btor2"
		self.verbose = True
		self.outdir = outdir
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)

	def check(self, check: BoundedCheckData, mod: Module):
		start = time.time()
		solver = BtorMC(header=mod.btor2_src)

		# declare custom states
		for state in check.states:
			solver.state(Symbol(state.name, state.tpe), state.next, state.init)

		# unroll for N cycles
		assert check.cycles < 2**16, "Too many cycles"
		solver.comment(f"Unroll for k={check.cycles} cycles")
		cycle = Symbol("cycle_count", BVType(16))
		solver.state(cycle, init=BV(0, 16), next=BVAdd(cycle, BV(1, 16)))
		solver.add_assert(Not(Equals(cycle, BV(check.cycles + 1, 16))))
		def in_cycle(ii: int, expr):
			return Implies(Equals(cycle, BV(ii, 16)), expr)

		# declare constants
		for sym in check.constants:
			solver.comment(f"Symbolic Constant: {sym}")
			solver.state(sym, next=sym)

		# compute functions
		for sym, expr in check.functions:
			solver.comment(f"Function: {sym} = {expr}")
			solver.state(sym, next=sym, init=expr)
			solver.watch(f"__watch_{sym.symbol_name()}", expr)

		# keep track of asserts
		assert_to_cycle = []
		assert_to_expr = []

		# add invariant asserts
		for aa in check.asserts:
			solver.add_assert(aa)
			assert_to_cycle.append(-1)
			assert_to_expr.append(aa)

		# add invariant assumptions
		for aa in check.assumptions:
			solver.add_assume(aa)

		# check each step
		for ii, step in enumerate(check.steps):
			assert step.cycle == ii
			solver.comment(f"-------------------")
			solver.comment(f"- Transition {ii} -> {ii+1}")
			solver.comment(f"-------------------")
			for aa in step.assumptions:
				solver.add_assume(in_cycle(ii, aa))
			for aa in step.assertions:
				solver.add_assert(in_cycle(ii, aa))
				assert_to_cycle.append(ii)
				assert_to_expr.append(aa)

		# watch outputs + state in order to get their values in case of a witness
		watched_state = [(n,t) for n,t in mod.state.items() if not t.is_array_type()]
		watched_outputs = [(n, t) for n, t in mod.outputs.items()]
		watched_custom_state = [(st.name, st.tpe) for st in check.states]
		watched_sub_io = []
		for submod in mod.submodules.values():
			watched_sub_io += [(submod.io_prefix+n, t) for n,t in chain(submod.outputs.items(), submod.inputs.items())]
		watched_signals = watched_state + watched_outputs + watched_custom_state + watched_sub_io
		watch_symbols = { f"__watch_{sig_name}": Symbol(sig_name, sig_tpe) for sig_name, sig_tpe in watched_signals}
		for name, expr in watch_symbols.items(): solver.watch(name, expr)

		# run solver
		if self.outdir is not None:	filename = os.path.join(self.outdir, f"{check.name}.btor2")
		else:                       filename = None
		valid, solver_time, model = solver.check(check.cycles, do_init=check.initialize, filename=filename)

		total_time = time.time() - start

		if valid:
			return CheckSuccess(solver_time, total_time)
		else:
			assert_ii = model['badprop'] - 1
			cycle = assert_to_cycle[assert_ii]
			assert_expr = assert_to_expr[assert_ii]

			# turn model into correct format
			input_signals = {name: Symbol(name, tpe) for name, tpe in mod.inputs.items()}
			all_signals = {**watch_symbols, **input_signals}
			signals = list(all_signals.values())
			indices = {sym.symbol_name(): ii for ii, sym in enumerate(signals)}
			# this relies on stable dictionaries
			data = [[model['steps'][ii][name]['data'] for name, sym in all_signals.items()] for ii in range(cycle+1)]
			# get value for constants
			constants = {name: dd['data'] for name, dd in model['init'].items() if 'data' in dd}
			m = Model(name=mod.name, cycles=cycle+1, indices=indices, signals=signals, data=data, creation_time=0.0, constants=constants)
			return CheckFailure(solver_time, total_time, cycle, assert_ii-1, assert_expr, m, solver_time)

class BtorMC:
	def __init__(self, header, bin='btormc'):
		self.header = header
		self.bin = bin
		subprocess.run(['which', bin], check=True, stdout=subprocess.PIPE)
		# initialized by reset
		self.ii = 0
		self._bv_sorts = {}
		self._name_to_ii = {}
		self._ii_to_sym = {}
		self.lines = []
		self.line_cache = {}
		self.assertions = []
		self.reset()

	def reset(self):
		rr = parse_yosys_btor(self.header)
		self.ii = rr['ii'] + 1
		self._name_to_ii = {}
		self._ii_to_sym = {}
		self.lines = []
		self.line_cache = {}
		self.assertions = []
		# load symbols form parser
		for name, data in rr['symbols'].items():
			typ, ii, _ = data
			if typ[0] == 'bv': typ = BVType(typ[1])
			elif typ[0] == 'array':
				addr = BVType(typ[1][1])
				data = BVType(typ[2][1])
				typ = ArrayType(addr, data)
			else: raise RuntimeError(f"TODO: {typ}")
			self._name_to_ii[name] = ii
			self._ii_to_sym[ii] = Symbol(name, typ)
		# add bv types to line cache
		for ii, s in rr['sorts'].items():
			if s[0] == 'bv':
				self.line_cache[f"sort bitvec {s[1]}"] = ii

	def _l(self, s: str):
		if s not in self.line_cache:
			self.lines.append(f"{self.ii} {s}")
			self.line_cache[s] = self.ii
			self.ii += 1
		return self.line_cache[s]

	def _bv(self, bits):
		return self._l(f"sort bitvec {bits}")

	def _sort(self, typ): return smt_to_btor_sort(self._l, typ)

	def _smt2btor(self, formula):
		converter = Smt2ToBtor2(sym_name_to_nid=self._name_to_ii, line=self._l)
		return converter.walk(formula)

	def get_symbol_by_name(self, name):
		ii = self._name_to_ii[name]
		return self._ii_to_sym[ii]

	def comment(self, s: str):
		self.lines.append("; " + str(s))

	def register_symbol(self, sym: Symbol, ii: int):
		assert sym.symbol_name() not in self._name_to_ii, f"symbol {sym} already exists!"
		assert ii not in self._ii_to_sym, f"symbol {self._ii_to_sym[ii]} already exists @ {ii}!"
		self._name_to_ii[sym.symbol_name()] = ii
		self._ii_to_sym[ii] = sym

	def watch_ii(self, name: str, typ, ii: int):
		assert name not in self._name_to_ii, f"symbol {name} already exists!"
		sort = self._sort(typ)
		self.comment(f"watching {ii}")
		inp = self._l(f"input {sort} {name}")
		sym = Symbol(name, typ)
		self.register_symbol(sym, inp)
		eq = self._l(f"eq {self._bv(1)} {inp} {ii}")
		self._l(f"constraint {eq}")

	def watch(self, name: str, expr):
		assert name not in self._name_to_ii, f"symbol {name} already exists!"
		typ = expr.get_type()
		sort = self._sort(typ)
		inp = self._l(f"input {sort} {name}")
		sym = Symbol(name, typ)
		self.register_symbol(sym, inp)
		self.add_assume(equal(sym, expr))

	def state(self, symbol: Symbol, next: Optional = None, init: Optional = None):
		assert symbol.symbol_name() not in self._name_to_ii, f"symbol {symbol} already exists!"
		typ, name = symbol.symbol_type(), symbol.symbol_name()

		# we need to declare the init expression before the state
		if init is not None:
			init = self._smt2btor(init)
		sort = self._sort(typ)
		st = self._l(f"state {sort} {name}")
		if init is not None:
			self._l(f"init {sort} {st} {init}")
		sym = Symbol(name, typ)
		self.register_symbol(sym, st)
		# next could be referring to state
		if next is not None:
			next = self._smt2btor(next)
			self._l(f"next {sort} {st} {next}")
		return sym

	def add_assume(self, formula):
		self.comment(f"assume: {formula}")
		const = self._smt2btor(formula)
		return self._l(f"constraint {const}")

	def add_assert(self, formula):
		self.comment(f"assert: {formula} (b{len(self.assertions)})")
		self.assertions.append(formula)
		good = self._smt2btor(formula)
		bad = self._l(f"not {self._bv(1)} {good}")
		return self._l(f"bad {bad}")

	def exclude(self, header, command):
		def check(ll: str):
			if ll.startswith(';'): return False
			parts = ll.strip().split(' ')
			return len(parts) > 1 and ll.strip().split(' ')[1] == command
		return [f"; {ll}" if check(ll) else ll for ll in header]

	def _parse_model(self, msg):
		""" Finds the first model and parses it """
		assert msg[0].strip() == 'sat', f"Unexpected msg header: {msg[0]}"
		props = msg[1].strip().split(' ')
		assert len(props) == 1, f"wrong number of bad properties! {props}"
		assert props[0].startswith('b'), f"invalid bad property: {props[0]}"
		bad_prop = int(props[0][1:])

		init = {}
		steps = defaultdict(dict)
		for ii, line in enumerate(msg[2:]):
			if line.startswith('b') or line.startswith('sat'):
				break
			if len(line) == 0 or line[0] in {'#', '@', '.'}:
				continue
			parts = line.split(' ')
			assert len(parts) in {3, 4}, f"Unexpected number of space separated parts @{ii}: {parts}\n{line}\n{msg}"
			if len(parts) == 3:
				entry = { 'data': int(parts[1], 2) }
			else:
				assert parts[1].startswith('[') and parts[1].endswith(']'), f"unexpected address format: {parts[1]} in {parts}"
				entry = { 'addr': int(parts[1][1:-1], 2), 'data': int(parts[2], 2) }
			if '#' in parts[-1]:
				name, suffix = parts[-1].split('#')
				assert int(suffix) == 0
				init[name] = entry
			else:
				assert '@' in parts[-1], f"{parts}"
				name, cycle = parts[-1].split('@')
				steps[int(cycle)][name] = entry

		return {'badprop': bad_prop, 'init': init, 'steps': steps}

	def check(self, k, do_init=False, filename=None):
		# remove outputs
		header = self.exclude(self.header.split('\n'), 'output')
		# remove init
		if not do_init:
			header = self.exclude(header, 'init')

		success, delta, msg = _check(solver=self.bin, k=k, filename=filename, header = header, lines=self.lines)

		if not success:
			model = self._parse_model(msg)
		else:
			model = None
		return success, delta, model

@cache_to_disk(1)
def _check(solver, k, filename, header, lines):
	start = time.time()
	filename = default(filename, tempfile.mkstemp()[1])
	with open(filename, 'w') as ff:
		print('\n'.join(header + lines), file=ff)
	# a kmin that is too big seems to lead to btormc ignoring bad properties.. #'-kmin', str(k)
	r = subprocess.run([solver, filename, '-kmax', str(k)], stdout=subprocess.PIPE, check=True)
	msg = r.stdout.decode('utf-8').split('\n')
	success = 'sat' not in msg[0]
	delta = time.time() - start
	return success, delta, msg

def smt_to_btor_sort(declare_line, typ):
	if typ.is_bool_type(): return declare_line(f"sort bitvec 1")
	elif typ.is_bv_type(): return declare_line(f"sort bitvec {typ.width}")
	elif typ.is_array_type():
		assert typ.index_type.is_bv_type(), f"Array address needs to be bitvector: {typ}"
		assert typ.elem_type.is_bv_type(), f"Array data needs to be bitvector: {typ}"
		addr_sort = smt_to_btor_sort(declare_line, typ.index_type)
		data_sort = smt_to_btor_sort(declare_line, typ.elem_type)
		return declare_line(f"sort array {addr_sort} {data_sort}")
	else: raise RuntimeError(f"unsupported type {typ}")

class Smt2ToBtor2(DagWalker):
	def __init__(self, sym_name_to_nid: dict, line, env=None):
		self.sym_name_to_nid = sym_name_to_nid
		self._l = line
		super().__init__(env)


	def _sort(self, typ): return smt_to_btor_sort(self._l, typ)

	def walk_bv_add(self, formula, args, **kwargs): return self.walk_binop("add", formula, args, **kwargs)
	def walk_bv_sub(self, formula, args, **kwargs): return self.walk_binop("sub", formula, args, **kwargs)
	def walk_bv_mul(self, formula, args, **kwargs): return self.walk_binop("mul", formula, args, **kwargs)
	def walk_bv_or(self, formula, args, **kwargs): return self.walk_binop("or", formula, args, **kwargs)
	def walk_or(self, formula, args, **kwargs): return self.walk_binop("or", formula, args, **kwargs)
	def walk_bv_and(self, formula, args, **kwargs): return self.walk_binop("and", formula, args, **kwargs)
	def walk_and(self, formula, args, **kwargs): return self.walk_binop("and", formula, args, **kwargs)
	def walk_bv_xor(self, formula, args, **kwargs): return self.walk_binop("xor", formula, args, **kwargs)
	def walk_bv_lshl(self, formula, args, **kwargs): return self.walk_binop("sll", formula, args, **kwargs)
	def walk_bv_concat(self, formula, args, **kwargs): return self.walk_binop("concat", formula, args, **kwargs)
	def walk_equals(self, formula, args, **kwargs): return self.walk_binop("eq", formula, args, **kwargs)
	def walk_iff(self, formula, args, **kwargs): return self.walk_binop("eq", formula, args, **kwargs)
	def walk_implies(self, formula, args, **kwargs): return self.walk_binop("implies", formula, args, **kwargs)
	def walk_binop(self, op, formula, args, **kwargs):
		return self._l(f"{op} {self._sort(formula.get_type())} {args[0]} {args[1]}")

	def walk_not(self, formula, args, **kwargs): return self.walk_unop("not", formula, args, **kwargs)
	def walk_unop(self, op, formula, args, **kwargs):
		return self._l(f"{op} {self._sort(formula.get_type())} {args[0]}")

	def walk_bv_zext(self, formula, args, **kwargs):
		return self._l(f"uext {self._sort(formula.get_type())} {args[0]} {formula.bv_extend_step()}")

	def walk_bv_extract(self, formula, args, **kwargs):
		lo = formula.bv_extract_start()
		hi = formula.bv_extract_end()
		return self._l(f"slice {self._sort(formula.get_type())} {args[0]} {hi} {lo}")

	def walk_array_select(self, formula, args, **kwargs): return self.walk_binop("read", formula, args, **kwargs)

	def walk_ite(self, formula, args, **kwargs):
		return self._l(f"ite {self._sort(formula.get_type())} {args[0]} {args[1]} {args[2]}")

	def walk_array_store(self, formula, args, **kwargs):
		return self._l(f"write {self._sort(formula.get_type())} {args[0]} {args[1]} {args[2]}")

	def walk_bv_constant(self, formula, **kwargs):
		return self._l(f"const {self._sort(formula.get_type())} {formula.bv_bin_str()}")

	def walk_bool_constant(self, formula, **kwargs):
		op = "one" if formula.constant_value() else "zero"
		return self._l(f"{op} {self._sort(formula.get_type())}")

	def walk_symbol(self, formula, **kwargs):
		name = formula.symbol_name()
		assert name in self.sym_name_to_nid, f"unknown symbol {formula}. {list(self.sym_name_to_nid.keys())}"
		return self.sym_name_to_nid[name]