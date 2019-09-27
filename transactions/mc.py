#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, tempfile, time
from typing import Optional
from pysmt.shortcuts import Symbol, BVType, BV, BVAdd, Not, Equals, Implies, BOOL, substitute
from pysmt.walkers import DagWalker

from .module import Module, State
from .engine import Spec, Transaction
from .yosys import parse_yosys_btor
from .utils import equal

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

	def in_cycle(self, ii: int, expr):
		return Implies(Equals(self.cycle, BV(ii, 16)), expr)

	def proof_transaction(self, tran: Transaction):
		cycles = len(tran.proto)
		self.unroll(cycles)

		# reset needs to be disabled
		if self.mod.reset is not None:
			self.solver.add_assume(Not(self.solver.get_symbol_by_name(self.mod.reset)))

		# TODO: renaming is currently broken
		# we need to rename the spec symbols as they might collide with
		# the symbols in the circuit
		#rename_table = {
		#	sym: Symbol("spec_" + sym.symbol_name(), sym.symbol_type())
		#	for sym in tran.args + tran.ret_args }

		# semantics as pure function calculated during initialization
		def rename(symbols):
			return {sym.symbol_name(): sym for sym in symbols}
		args = rename(tran.args)
		for arg in args.values():
			self.solver.comment(f"{tran.name} <- {arg}")
			self.solver.state(arg, next=arg)
		sem_out = tran.semantics(**args)
		ret_args = rename(tran.ret_args)
		for name, sym in ret_args.items():
			self.solver.comment(f"{tran.name} -> {name}")
			self.solver.state(sym, next=sym, init=sem_out[name])

		# unroll transaction
		for ii, m in enumerate(tran.proto.mappings):
			for signal_name, expr in m.items():
				assert not self.mod.is_state(signal_name), f"protocols may only read/write from io: {signal_name}"
				signal = self.solver.get_symbol_by_name(signal_name)
				#expr = substitute(expr, rename_table)

				if self.mod.is_output(signal_name):
					self.solver.add_assert(self.in_cycle(ii, equal(signal, expr)))
				else:
					# if the signal is an input, we just apply the constraint for this cycle
					assert self.mod.is_input(signal_name)
					self.solver.add_assume(self.in_cycle(ii, equal(signal, expr)))

		valid, delta = self.solver.check(cycles - 1)
		assert valid, f"found counter example to transaction {tran.name}"
		print(f"Verified {tran.name} in {delta:.02} sec")
		self.solver.reset()

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
		# load symbols form parser
		for name, data in rr['symbols'].items():
			typ, ii = data
			if typ[0] == 'bv' and typ[1] == 1: typ = BOOL
			elif typ[0] == 'bv': typ = BVType(typ[1])
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

	def _smt2btor(self, formula):
		converter = Smt2ToBtor2(sym_name_to_nid=self._name_to_ii, line=self._l)
		return converter.walk(formula)

	def get_symbol_by_name(self, name):
		ii = self._name_to_ii[name]
		return self._ii_to_sym[ii]

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
		self.comment(f"assume: {formula}")
		const = self._smt2btor(formula)
		return self._l(f"constraint {const}")

	def add_assert(self, formula):
		self.comment(f"assert: {formula}")
		good = self._smt2btor(formula)
		bad = self._l(f"not {self._bv(1)} {good}")
		return self._l(f"bad {bad}")

	def check(self, k_max):
		start = time.time()
		filename = tempfile.mkstemp()[1]
		# remove outputs
		header = [ll for ll in self.header.split('\n') if 'output' not in ll]
		with open(filename, 'w') as ff:
			print('\n'.join(header + self.lines), file=ff)
		r = subprocess.run([self.bin, filename, '-kmax', str(k_max)], stdout=subprocess.PIPE, check=True)
		msg = r.stdout.decode('utf-8')
		success = 'sat' not in msg.split('\n')[0]
		if not success:
			print("Check failed!")
			print(msg)
		delta = time.time() - start
		return success, delta

class Smt2ToBtor2(DagWalker):
	def __init__(self, sym_name_to_nid: dict, line, env=None):
		self.sym_name_to_nid = sym_name_to_nid
		self._l = line
		super().__init__(env)


	def _sort(self, typ):
		if typ.is_bool_type(): bits = 1
		elif typ.is_bv_type(): bits = typ.width
		else: raise RuntimeError(f"unsupported type {typ}")
		return self._l(f"sort bitvec {bits}")

	def walk_bv_add(self, formula, args, **kwargs): return self.walk_binop("add", formula, args, **kwargs)
	def walk_bv_sub(self, formula, args, **kwargs): return self.walk_binop("sub", formula, args, **kwargs)
	def walk_bv_or(self, formula, args, **kwargs): return self.walk_binop("or", formula, args, **kwargs)
	def walk_bv_and(self, formula, args, **kwargs): return self.walk_binop("and", formula, args, **kwargs)
	def walk_bv_xor(self, formula, args, **kwargs): return self.walk_binop("xor", formula, args, **kwargs)
	def walk_bv_lshl(self, formula, args, **kwargs): return self.walk_binop("sll", formula, args, **kwargs)
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
		hi = formula.bv_extract_start()
		lo = formula.bv_extract_end()
		return self._l(f"slice {self._sort(formula.get_type())} {args[0]} {hi} {lo}")

	def walk_bv_constant(self, formula, **kwargs):
		return self._l(f"const {self._sort(formula.get_type())} {formula.bv_bin_str()}")

	def walk_bool_constant(self, formula, **kwargs):
		op = "one" if formula.constant_value() else "zero"
		return self._l(f"{op} {self._sort(formula.get_type())}")

	def walk_symbol(self, formula, **kwargs):
		name = formula.symbol_name()
		assert name in self.sym_name_to_nid, f"unknown symbol {formula}. {list(self.sym_name_to_nid.keys())}"
		return self.sym_name_to_nid[name]