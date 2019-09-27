#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os
from typing import Optional
from pysmt.shortcuts import Symbol, BVType, BV, BVAdd, Not, Equals, get_type
from pysmt.walkers import TreeWalker

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
		self.reset()

	def reset(self):
		rr = parse_yosys_btor(self.header)
		self.ii = rr['ii'] + 1
		self._bv_sorts = {s[1]: ii for ii, s in rr['sorts'].items() if s[0] == 'bv'}
		self._sym_to_ii = {}
		self._ii_to_sym = {}
		self.lines = []


	def _l(self, s: str):
		self.lines.append(f"{self.ii} {s}")
		ii = self.ii
		self.ii += 1
		return ii

	def _bv(self, bits):
		if bits not in self._bv_sorts:
			self._bv_sorts[bits] = self._l(f"sort bitvec {bits}")
		return self._bv_sorts[bits]

	def _smt2btor(self, formula):
		converter = Smt2ToBtor2(sym_to_nid=self._sym_to_ii, bv=self._bv, ii=self.ii)
		converter.walk(formula)
		self.lines += converter.lines
		self.ii = converter.ii
		return self.ii - 1

	def comment(self, s: str):
		self.lines.append("; " + str(s))

	def state(self, symbol: Symbol, next: Optional = None, init: Optional = None):
		assert symbol not in self._sym_to_ii, f"symbol {symbol} already exists!"
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
		self._name_to_ii[name] = st
		sym = Symbol(name, BVType(bits))
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

class Smt2ToBtor2(TreeWalker):
	def __init__(self, sym_to_nid: dict, bv, ii: int, env=None):
		super().__init__(env)
		self.sym_to_nid = sym_to_nid
		self._bits_to_bv = bv
		self.lines = []
		self.ii = ii

	def _sort(self, formula):
		bits = 1
		return self._bits_to_bv(bits)

	def _l(self, s: str):
		self.lines.append(f"{self.ii} {s}")
		ii = self.ii
		self.ii += 1
		return ii

	def walk_bv_constant(self, formula):
		self._l(f"const {self._sort(formula)} {formula.bv_bin_str()}")
