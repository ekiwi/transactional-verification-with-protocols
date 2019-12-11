#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# SMT2 Lib based backend for BoundedCheck
import functools
import subprocess, tempfile, os, re
from pysmt.shortcuts import Symbol, FunctionType, BOOL, Function, Ite, get_free_variables, Not, Type, substitute
from pysmt.smtlib.script import smtcmd, SmtLibCommand
from itertools import chain
import time
from .utils import *
from .bounded import BoundedCheckData, CheckFailure, CheckSuccess, Model, AssumptionFailure
from .module import Module
from typing import Tuple, List, Optional
import pysmt.simplifier

class SMT2ProofEngine:
	def __init__(self, outdir=None, simplify:bool=False):
		self.name = 'smt2'
		self.outdir = outdir
		self.simplify = simplify
		if self.simplify:
			print("WARN: running with unproven simplifications.")
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)

	def check(self, check: BoundedCheckData, mod: Module, verify_assumptions=True):
		start = time.time()
		solver = Solver(header=mod.smt2_src, do_simplify=self.simplify)

		# derive function names for module unrolling
		state_t = Type(mod.name + "_s")
		transition_fun = Symbol(mod.name + "_t", FunctionType(BOOL, [state_t, state_t]))

		# unroll for N cycles
		states = [Symbol(f"s{ii}", state_t) for ii in range(check.cycles + 1)]
		# declare states
		for st in states:
			solver.fun(st)
		# assert transition function on successive states
		assert len(states) > 1, f"{states}"
		for ii in range((len(states) - 1)):
			solver.add(Function(transition_fun, [states[ii], states[ii + 1]]))

		# declare constants
		for sym in check.constants:
			solver.fun(sym)

		# compute functions
		for sym, expr in check.functions:
			solver.fun(sym)
			solver.comment(f"Function: {sym} = {expr}")
			solver.add(equal(sym, expr))

		# assert initialization functions in first state if requested
		if check.initialize:
			init_fun = Symbol(mod.name + "_i", FunctionType(BOOL, [state_t]))
			solver.comment(f"Initialize State")
			solver.add(Function(init_fun, [states[0]]))

		# map module i/o and state to cycle dependent function
		symbols = [Symbol(name, tpe) for name, tpe in chain(mod.inputs.items(), mod.outputs.items(), mod.state.items())]
		for submodule in mod.submodules.values():
			symbols += [Symbol(submodule.io_prefix + name, tpe) for name, tpe in
						chain(submodule.inputs.items(), submodule.outputs.items())]
		# TODO: compute mappings lazily as not all of them will be used
		def map_sym(symbol: Symbol, state):
			tpe = symbol.symbol_type()
			is_bool = tpe.is_bv_type() and tpe.width == 1
			ft = FunctionType(BOOL if is_bool else tpe, [state_t])
			if tpe.is_array_type():	fn = mod.name + "_m " + symbol.symbol_name()
			else:                   fn = mod.name + "_n " + symbol.symbol_name()
			if is_bool:	return Ite(Function(Symbol(fn, ft), [state]), BV(1,1), BV(0,1))
			else:       return Function(Symbol(fn, ft), [state])
		mappings = [{ sym: map_sym(sym, state) for sym in symbols } for state in states]
		def in_cycle(ii, ee):
			return substitute(ee, mappings[ii])

		# check if assumptions are cycle dependent
		symbol_set = set(symbols)
		is_cycle_dep = lambda expr: set(get_free_variables(expr)) & symbol_set != set()
		cycle_dependent = [aa for aa in check.assumptions if is_cycle_dep(aa)]
		cycle_independent = [aa for aa in check.assumptions if not is_cycle_dep(aa)]
		solver.comment("Invariant Assumptions")
		for aa in cycle_independent:
			solver.add(aa)

		# add invariant assumptions to steps
		assumptions = [step.assumptions + cycle_dependent for step in check.steps]
		assertions  = [step.assertions for step in check.steps]


		# check each step
		assertion_symbols = []
		assert_to_cycle = []
		assert_to_expr = []
		for ii, (assums, asserts) in enumerate(zip(assumptions, assertions)):
			solver.comment(f"-------------------")
			solver.comment(f"- Cycle {ii}")
			solver.comment(f"-------------------")
			solver.comment("Assumptions")
			for aa in assums:
				solver.add(in_cycle(ii, aa))
			solver.comment("Assertions")
			for aa in asserts:
				asym = Symbol(f"b{len(assertion_symbols)}")
				solver.fun(asym)
				solver.add(in_cycle(ii, equal(asym, aa)))
				assertion_symbols.append(asym)
				assert_to_cycle.append(ii)
				assert_to_expr.append(aa)

		# remember functions (or symbolic constants)
		funs = check.constants + [sym for sym,_ in check.functions]

		# run solver
		if self.outdir is not None:	filename = os.path.join(self.outdir, f"{check.name}.smt2")
		else:                                  filename = None
		valid, solver_times, assert_ii = solver.solve(filename=filename, vc=assertion_symbols, verify_assumptions=verify_assumptions)

		total_time = time.time() - start

		if valid:
			return CheckSuccess(sum(solver_times), total_time)
		else:
			if verify_assumptions and assert_ii == -2:
				return AssumptionFailure(sum(solver_times), total_time)
			cycle = assert_to_cycle[assert_ii]
			assert_expr = assert_to_expr[assert_ii]
			model = self._generate_model(mod.name, assertion_symbols, assert_ii, cycle, filename, mappings, funs, solver)
			return CheckFailure(sum(solver_times), total_time, cycle, assert_ii, assert_expr, model, solver_times[0])

	def _generate_model(self, mod_name, assertion_symbols, assert_ii, cycle, filename, mappings, funs, solver) -> Model:
		ff = os.path.splitext(filename)[0] + f"_b{assert_ii}_model.smt2"

		# only include one failing check
		vc = assertion_symbols[:assert_ii + 1]

		# add symbols for all signals we want to read
		reads = list(funs)
		for ii in range(cycle + 1):
			solver.comment(f"----------------------------")
			solver.comment(f"- Cycle {ii} Signal Reads")
			solver.comment(f"----------------------------")
			for sym, expr in mappings[ii].items():
				# skip memories for now
				if sym.symbol_type().is_array_type():
					continue
				name = f"{sym.symbol_name()}_cyc{ii}_read"
				read_sym = Symbol(name, sym.symbol_type())
				solver.fun(read_sym)
				solver.add(equal(read_sym, expr))
				reads.append(read_sym)

		# query solver for values
		values, delta = solver.get_model(vc=vc, cycle=cycle, reads=reads, filename=ff)

		# organize values in model
		signals = [sym for sym in mappings[0].keys() if not sym.symbol_type().is_array_type()]
		indices = {sym.symbol_name(): ii for ii, sym in enumerate(signals)}

		data = []
		for ii in range(cycle + 1):
			data.append([None] * len(indices))
			for sym, expr in mappings[ii].items():
				# skip memories for now
				if sym.symbol_type().is_array_type():
					continue
				name = f"{sym.symbol_name()}_cyc{ii}_read"
				data[ii][indices[sym.symbol_name()]] = values[name]

		constants = {name: values[name] for name in (sym.symbol_name() for sym in funs)}

		model = Model(name=mod_name, cycles=cycle+1, indices=indices, signals=signals, data=data, constants=constants, creation_time=delta)

		return model

sat = "sat"
unsat = "unsat"

class Solver:
	def __init__(self, header, logic='QF_AUFBV', bin='yices-smt2', do_simplify:bool=False):
		self.header = header
		self.logic = logic
		self.bin = bin
		if do_simplify:
			simpl = Simplifier()
			self.simplify = lambda f: simpl.simplify(f)
		else:
			self.simplify = lambda f: f
		subprocess.run(['which', bin], check=True, stdout=subprocess.PIPE)
		self.assertions = []
		self.funs: List[Tuple[Symbol, Optional[SmtExpr]]] = []

	def add(self, *assertions):
		self.assertions += [a for a in (self.simplify(a) for a in  assertions) if a != TRUE()]

	def comment(self, s: str):
		self.assertions.append(str(s))

	def get_funs(self) -> List[Symbol]:
		return [sym for sym, _ in self.funs]

	def fun(self, function: Symbol, expr: Optional[SmtSort] = None):
		self.funs.append((function, expr))

	def check_sat(self, filename, assertions, funs=None, get_cmds=None):
		stdout, delta = _check_sat(solver=self.bin, header=self.header, filename=filename, funs=funs, assertions=assertions, get_cmds=get_cmds)
		assert 'error' not in stdout, f"SMT solver call failed on {filename}: {stdout}"
		return stdout, delta

	def _check_vc(self, vc, filename):
		vc_validity = Not(conjunction(*vc))
		return self.check_sat(funs=self.funs, assertions=self.assertions + [vc_validity], filename=filename)

	def _check_vc_is_sat(self, vc, filename, sat_time):
		stdout, delta = self._check_vc(vc=vc, filename=filename)
		sat_time.append(delta)
		return stdout == sat

	def _check_vc_is_unsat(self, vc, filename, sat_time):
		stdout, delta = self._check_vc(vc=vc, filename=filename)
		sat_time.append(delta)
		return stdout == unsat

	def _verify_assumptions(self, filename, sat_time):
		ff = os.path.splitext(filename)[0] + "_verify_assumptions.smt2"
		stdout, delta = self.check_sat(funs=self.funs, assertions=self.assertions, filename=filename)
		sat_time.append(delta)
		# if there is no satisfying assignment, then the assumptions are contradictory
		return stdout == sat

	def solve(self, vc, filename=None, verify_assumptions=False) -> Tuple[bool, List[float], int]:
		# if there is no vc, the check always passes
		if len(vc) == 0:
			return True, [0.0], -1

		filename = default(filename, tempfile.mkstemp()[1])

		if verify_assumptions:
			sat_time = []
			success = self._verify_assumptions(filename=filename, sat_time=sat_time)
			if not success:
				return success, sat_time, -2

		sat_time = []
		success = self._check_vc_is_unsat(vc, filename=filename, sat_time=sat_time)

		bad_prop = -1
		if not success:
			# binary search for first failing property
			good = -1
			fail = len(vc) - 1
			while fail - good > 1:
				assert fail > good
				ii = good + (fail - good) // 2
				ff = os.path.splitext(filename)[0] + f"_b{ii}.smt2"
				ii_fail = self._check_vc_is_sat(vc[:ii+1], filename=ff, sat_time=sat_time)
				if ii_fail: fail = ii
				else:       good = ii
			bad_prop = fail

		return success, sat_time, bad_prop

	def get_model(self, vc: list, cycle: int, reads: list, filename):
		""" call this after a failing solver call  and only hand it the vc you are interested in """
		# get values
		get_cmds = [SmtLibCommand(smtcmd.GET_VALUE, [vv]) for vv in reads]

		# run SMT solver
		vc_validity = Not(conjunction(*vc))
		out, sat_time = self.check_sat(funs=self.funs, assertions=self.assertions + [vc_validity], filename=filename, get_cmds=get_cmds)
		lines = out.split('\n')
		assert lines[0] == 'sat', f"model generation is only supported for satisfiable queries. Expected `sat` got `{lines[0]}`"

		# parse model
		start = time.time()
		values = self._parse_model(lines[1:])
		for rr in reads: assert rr.symbol_name() in values, f"{rr} is missing from the values returned by the solver"
		delta = time.time() - start
		return values, delta + sat_time


	def _parse_model(self, lines):
		suffix = r'\)\)'
		bv_bool = '(#b[01]+|false|true)'
		re_read = re.compile(f'\(\(([a-zA-Z_0-9@\.]+)\s+' + bv_bool + suffix)

		def parse_value(vv):
			if vv == 'true': return 1
			if vv == 'false': return 0
			assert len(vv) > 2
			return int(vv[2:], 2)

		values = {}
		for line in lines:
			if line.strip() == 'sat': continue
			m = re_read.match(line)
			assert m is not None, f"Failed to parse line: {line}"
			name, value = m.groups()
			values[name] = parse_value(value)

		return values


def _write_scrip(header, filename, funs: List[Tuple[Symbol, Optional[SmtExpr]]], assertions, cmds: list):
	with open(filename, 'w') as ff:
		print("(set-logic QF_AUFBV)", file=ff)
		print("; smt script generated using yosys + a custom python script", file=ff)
		print(file=ff)
		print("; yosys generated:", file=ff)
		print(header, file=ff)
		print("; custom cmds", file=ff)
		for symbol, expr in funs:
			if expr is None:
				SmtLibCommand(smtcmd.DECLARE_FUN, [symbol]).serialize(outstream=ff, daggify=False)
			else:
				SmtLibCommand(smtcmd.DEFINE_FUN, [symbol, expr]).serialize(outstream=ff, daggify=False)
			print("", file=ff)
		for a in assertions:
			if isinstance(a, str):
				print(f"; {a}", file=ff)
			else:
				SmtLibCommand(smtcmd.ASSERT, [a]).serialize(outstream=ff, daggify=False)
				print("", file=ff)
		for cmd in cmds:
			cmd.serialize(outstream=ff)
			print("", file=ff)

#@cache_to_disk(1)
def _check_sat(solver, header, filename, funs, assertions, get_cmds=None):
	funs = [] if funs is None else funs
	get_cmds = [] if get_cmds is None else get_cmds
	start = time.time()
	cmds = [SmtLibCommand(smtcmd.CHECK_SAT, [])] + get_cmds
	_write_scrip(header=header, filename=filename, funs=funs, assertions=assertions, cmds=cmds)
	r = subprocess.run([solver, filename], stdout=subprocess.PIPE, check=True)
	stdout = r.stdout.decode('utf-8').strip()
	delta = time.time() - start
	return stdout, delta


# stand alone solver functions for use in verification midend
# TODO: using an interactive solver + pipes could speed this up a bit!
_solve = Solver(header='')
def is_valid(e) -> bool:
	f = tempfile.NamedTemporaryFile()
	funs = list(get_free_variables(e))
	out, delta = _solve.check_sat(filename=f.name, assertions=[Not(e)], funs=[(f,None) for f in funs])
	return out == 'unsat'

def is_unsat(e) -> bool:
	f = tempfile.NamedTemporaryFile()
	asserts = e if isinstance(e, list) else [e]
	funs = list(functools.reduce(lambda a,b: a|b,  (get_free_variables(a) for a in asserts)))
	out, delta = _solve.check_sat(filename=f.name, assertions=asserts, funs=[(f,None) for f in funs])
	return out == 'unsat'

class Simplifier(pysmt.simplifier.Simplifier):
	""" Custom simplifications to make it easier to read generated SMT2 """
	def __init__(self, env=None):
		super().__init__(env=env)

	def walk_equals(self, formula, args, **kwargs):
		"""
			For simplicity, all signals are modelled  as BV<N> in the frontend.
			However, yosys treats 1-bit signals as bool typed.
			This leads to a frequent pattern where we want to say `signal = 1`, which
			gets expressed as `(= (ite signal, #b1, #b0) #b1)`.
			This transform turns that into `(signal)`
		"""
		# recognize the ite(expr, #b1, #b0) pattern used to convert to bv
		is_bool_to_bv = lambda: args[0].is_ite() and args[0].args()[1] == BV(1,1) and args[0].args()[2] == BV(0,1)
		if args[1].is_bv_constant() and is_bool_to_bv():
			if args[1] == BV(1,1): return args[0].args()[0]
			if args[1] == BV(0,1): return Not(args[0].args()[0])
			assert False, "Should not get here"
		else:
			return super().walk_equals(formula, args, **kwargs)