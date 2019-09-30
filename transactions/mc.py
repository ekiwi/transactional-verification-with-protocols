#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, os, tempfile, time, itertools
from typing import Optional
from pysmt.shortcuts import Symbol, BVType, BV, BVAdd, Not, Equals, Implies, BOOL, ArrayType, Select
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
		self.solver.add_assert(Not(Equals(self.cycle, BV(cycles+1, 16))))

	def in_cycle(self, ii: int, expr):
		return Implies(Equals(self.cycle, BV(ii, 16)), expr)

	def get_circuit_state(self):
		""" placeholder for state['test'] for use in formulas """
		def symbols(names): return {name: self.solver.get_symbol_by_name(name) for name in names}
		state =  symbols([s.name for s in self.mod.state])
		return state

	def map_arch_state(self, suffix: str, cycle: int):
			arch_state = {name: Symbol(name + suffix, tpe) for name, tpe in self.spec.arch_state.items()}
			mapped_expr = self.spec.mapping(state=self.get_circuit_state(), **arch_state)
			for sym in arch_state.values():
				self.solver.fun(sym)
			self.solver.add(conjunction(*self.spec.mapping(state=state, **arch_state)))
			return arch_state

	def proof_transaction(self, tran: Transaction, assume_invariances=False):
		cycles = len(tran.proto)
		self.unroll(cycles)



		# assume invariances hold at the beginning of the transaction
		if assume_invariances:
			for inv in self.spec.invariances:
				self.solver.add_assume(self.in_cycle(0, inv(self.get_circuit_state())))

		# reset needs to be disabled
		if self.mod.reset is not None:
			self.solver.add_assume(Not(self.solver.get_symbol_by_name(self.mod.reset)))

		# TODO: renaming is currently broken
		# we need to rename the spec symbols as they might collide with
		# the symbols in the circuit
		#rename_table = {
		#	sym: Symbol("spec_" + sym.symbol_name(), sym.symbol_type())
		#	for sym in tran.args + tran.ret_args }

		# declare architectural states and bind them to the initialization of the circuit state
		arch_state = {name: Symbol(name, tpe) for name, tpe in self.spec.arch_state.items()}
		arch_state_n = {name: Symbol(name + "_n", tpe) for name, tpe in self.spec.arch_state.items()}
		# TODO: we could assign an initial value to the arch state that is derived from the initial circuit state
		for sym in arch_state.values(): self.solver.state(sym, next=sym)
		# connect initial circuit and arch state
		mapping_assumptions = self.spec.mapping(state=self.get_circuit_state(), **arch_state)
		for a in mapping_assumptions: self.solver.add_assume(self.in_cycle(0, a))

		# semantics as pure function calculated during initialization
		def rename(symbols):
			return {sym.symbol_name(): sym for sym in symbols}
		args = rename(tran.args)
		for arg in args.values():
			self.solver.comment(f"{tran.name} <- {arg}")
			self.solver.state(arg, next=arg)
		sem_out = tran.semantics(**args, **arch_state)
		ret_args = rename(tran.ret_args)
		for name, sym in itertools.chain(ret_args.items(), arch_state_n.items()):
			self.solver.comment(f"{tran.name} -> {name}")
			self.solver.state(sym, next=sym, init=sem_out[name])

		# TODO: remove assumption

		# 1. with no write, things are easy (< 1s)
		#self.solver.add_assume(self.in_cycle(0, Not(args['rd_enable'])))

		# 2. write to address 0, is ok (< 3.7s)
		#self.solver.add_assume(self.in_cycle(0, args['rd_enable']))
		#self.solver.add_assume(self.in_cycle(0, equal(args['rd_addr'], BV(0, 5))))

		# 3. write to address 1 -> counter example ((after 3.3s)
		#self.solver.add_assume(self.in_cycle(0, args['rd_enable']))
		#self.solver.add_assume(self.in_cycle(0, equal(args['rd_addr'], BV(1, 5))))
		#self.solver.watch("watch_memory_31_9", Select(self.solver.get_symbol_by_name("memory"), BV(31, 9)))
		#self.solver.watch("watch_regs_n_1_5", Select(self.solver.get_symbol_by_name("regs_n"), BV(1, 5)))
		#self.solver.watch_ii("watch_wr_en", BVType(1), 54)
		#self.solver.watch_ii("watch_wr_en_final", BVType(1), 96)
		#self.solver.watch_ii("watch_waddr", BVType(9), 84)
		#self.solver.watch_ii("watch_wdata", BVType(2), 86)
		# after write/read masking etc
		#self.solver.watch_ii("watch_wdata_final", BVType(2), 94)

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

		# verify arch states after transaction
		mapping_assertions = self.spec.mapping(state=self.get_circuit_state(), **arch_state_n)
		for a in mapping_assertions:
			self.solver.add_assert(self.in_cycle(cycles, a))

		valid, delta = self.solver.check(cycles)
		assert valid, f"found counter example to transaction {tran.name}"
		print(f"Verified {tran.name} in {delta:.02} sec")
		self.solver.reset()

	def proof_transactions(self):
		for trans in self.spec.transactions:
			self.proof_transaction(trans, True)

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
			typ, ii = data
			if typ[0] == 'bv' and typ[1] == 1: typ = BOOL
			elif typ[0] == 'bv': typ = BVType(typ[1])
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

	def check(self, k):
		start = time.time()
		filename = tempfile.mkstemp()[1]
		print(filename)
		# remove outputs
		header = [ll for ll in self.header.split('\n') if 'output' not in ll]
		with open(filename, 'w') as ff:
			print('\n'.join(header + self.lines), file=ff)
		r = subprocess.run([self.bin, filename, '-kmax', str(k), '-kmin', str(k)], stdout=subprocess.PIPE, check=True)
		msg = r.stdout.decode('utf-8')
		success = 'sat' not in msg.split('\n')[0]
		delta = time.time() - start
		if not success:
			print(f"Check failed after {delta} sec!")
			print(msg)
		return success, delta

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
	def walk_bv_or(self, formula, args, **kwargs): return self.walk_binop("or", formula, args, **kwargs)
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