#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os
from typing import Optional
from pysmt.shortcuts import Symbol, BVType, BV, BVAdd, Not, Equals, get_type
from pysmt.walkers import DagWalker

from .module import Module, State
from .engine import Spec, Transaction
from .yosys import parse_yosys_btor


class MCProofEngine:
	def __init__(self, mod: Module, spec: Spec, outdir=None):
		self.mod = mod
		self.spec = spec
		self.verbose = True
		self.outdir = outdir
		self.solver = BtorMC(mod.btor2_src)
		self.cycle = Symbol("cycle_count", BVType(16))
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)

	def unroll(self, cycles):
		self.solver.state(self.cycle, init=BV(0, 16), next=BVAdd(self.cycle, BV(1, 16)))
		self.solver.comment(f"max unrolling = {cycles}")
		self.solver.add_assert(Not(Equals(self.cycle, BV(cycles, 16))))

	def proof_transaction(self, tran: Transaction):
		cycles = len(tran.proto)
		self.unroll(cycles)

		# semantics as pure function calculated during initialization
		args = {arg.symbol_name(): arg for arg in tran.args}
		for arg in args.values():
			self.solver.comment(f"{tran.name} <- {arg}")
			self.solver.state(arg, next=arg)
		sem_out = tran.semantics(**args)
		ret_args = {arg.symbol_name(): arg for arg in tran.ret_args}
		for name, sym in ret_args.items():
			self.solver.comment(f"{tran.name} -> {name}")
			self.solver.state(sym, next=sym, init=sem_out[name])

		print('\n'.join(self.solver.lines))

	def proof_transactions(self):
		for trans in self.spec.transactions:
			self.proof_transaction(trans)

	def proof_all(self):
		print("TODO invariances")
		self.proof_transactions()


class BtorMC:
	def __init__(self, header, bin='/home/kevin/d/boolector/build/bin/btormc'):
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
		self.reset()

	def reset(self):
		rr = parse_yosys_btor(self.header)
		self.ii = rr['ii'] + 1
		self._name_to_ii = {}
		self._ii_to_sym = {}
		self.lines = []
		self.line_cache = {}
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

	def _smt2btor(self, formula):
		converter = Smt2ToBtor2(sym_name_to_nid=self._name_to_ii, line=self._l)
		converter.walk(formula)
		return self.ii - 1

	def comment(self, s: str):
		self.lines.append("; " + str(s))

	def state(self, symbol: Symbol, next: Optional = None, init: Optional = None):
		assert symbol.symbol_name() not in self._name_to_ii, f"symbol {symbol} already exists!"
		typ, name = symbol.symbol_type(), symbol.symbol_name()
		assert typ.is_bv_type(), f"unsupported type: {typ}"
		bits = typ.width

		# we need to declare the init expression before the state
		if init is not None:
			init = self._smt2btor(init)
		sort = self._bv(bits)
		st = self._l(f"state {sort} {name}")
		if init is not None:
			self._l(f"init {sort} {st} {init}")
		sym = Symbol(name, BVType(bits))
		self._name_to_ii[name] = st
		self._ii_to_sym[st] = sym
		# next could be referring to state
		if next is not None:
			next = self._smt2btor(next)
			self._l(f"next {sort} {st} {next}")
		return sym

	def add_assume(self, formula):
		const = self._smt2btor(formula)
		return self._l(f"constraint {const}")

	def add_assert(self, formula):
		good = self._smt2btor(formula)
		bad = self._l(f"not {self._bv(1)} {good}")
		return self._l(f"bad {bad}")

class Smt2ToBtor2(DagWalker):
	def __init__(self, sym_name_to_nid: dict, line, env=None):
		self.sym_name_to_nid = sym_name_to_nid
		self._l = line
		self._register_ops(Smt2ToBtor2.BinOps, self.walk_binop)
		self._register_ops(Smt2ToBtor2.UnOps, self.walk_unop)
		super().__init__(env)

	def _register_ops(self, ops, foo):
		for name, op in ops.items():
			ff = lambda formula, args, **kwargs: foo(op, formula, args, **kwargs)
			self.__setattr__('walk_' + name,    ff)
			self.__setattr__('walk_bv_' + name, ff)

	BinOps = {
		'iff': 'iff',
		'implies': 'implies',
		'equals': 'eq',
		'add': 'add',
	}
	UnOps = {
		'not': 'not'
	}

	def _sort(self, typ):
		if typ.is_bool_type(): bits = 1
		elif typ.is_bv_type(): bits = typ.width
		else: raise RuntimeError(f"unsupported type {typ}")
		return self._l(f"sort bitvec {bits}")

	def walk_binop(self, op, formula, args, **kwargs):
		return self._l(f"{op} {self._sort(formula.get_type())} {args[0]} {args[1]}")

	def walk_unop(self, op, formula, args, **kwargs):
		return self._l(f"{op} {self._sort(formula.get_type())} {args[0]}")

	def walk_bv_zext(self, formula, args, **kwargs):
		return self._l(f"uext {args[0]} {formula.bv_extend_step()}")

	def walk_bv_extract(self, formula, args, **kwargs):
		hi = formula.bv_extract_start()
		lo = formula.bv_extract_end()
		return self._l(f"slice {args[0]} {hi} {lo}")

	def walk_bv_constant(self, formula, **kwargs):
		return self._l(f"const {self._sort(formula.get_type())} {formula.bv_bin_str()}")

	def walk_symbol(self, formula, **kwargs):
		name = formula.symbol_name()
		assert name in self.sym_name_to_nid, f"unknown symbol {formula}. {list(self.sym_name_to_nid.keys())}"
		return self.sym_name_to_nid[name]