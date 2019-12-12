#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# SMT2 Lib based backend for BoundedCheck
from __future__ import annotations
import functools
import subprocess, tempfile, os, re
from pysmt.shortcuts import Symbol, FunctionType, BOOL, Function, Ite, get_free_variables, Not, Type, substitute
from pysmt.smtlib.script import smtcmd, SmtLibCommand
from itertools import chain
import time
from .utils import *
from .bounded import BoundedCheckData, CheckFailure, CheckSuccess, Model, AssumptionFailure
from .module import Module
from typing import Tuple, List, Optional, Callable
import pysmt.simplifier
from dataclasses import dataclass

class SMT2ProofEngine:
	def __init__(self, outdir=None, simplify:bool=False):
		self.name = 'smt2'
		self.outdir = outdir
		self.simplify = simplify
		if self.simplify:
			print("WARN: running with unproven simplifications.")
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)

	def states(self, check: BoundedCheckData, solver: Solver, mod_name: str, signal_symbols: List[Symbol], map_sym) -> Tuple[Symbol, Callable[[Symbol], dict]]:
		# derive function names for module unrolling
		state_t = Type(mod_name + "_s")
		transition_fun = Symbol(mod_name + "_t", FunctionType(BOOL, [state_t, state_t]))

		# early exit in case there are no custom states
		if len(check.states) == 0: return transition_fun, lambda s: {}

		# create functions to represent custom state
		custom_state_funs = [Symbol(state.name + "_fun", FunctionType(state.tpe, [state_t])) for state in check.states]
		for ff in custom_state_funs: solver.fun(ff)

		# create mappings for all signals and state referred to inside a state_next function
		state_symbol = Symbol("state", state_t)
		signal_mappings = {sym: map_sym(sym, state_symbol) for sym in signal_symbols}
		state_mappings = {Symbol(state.name, state.tpe): Function(ff, [state_symbol])
						  for state, ff in zip(check.states, custom_state_funs)}
		sn_map = {**signal_mappings, **state_mappings}

		# create next functions
		custom_state_next_funs = [Symbol(state.name + "_next_fun", FunctionType(state.tpe, [state_t])) for state in check.states]
		for state, next_fun in zip(check.states, custom_state_next_funs):
			solver.fun_def(next_fun, [state_symbol], substitute(state.next, sn_map))

		# create a custom transition function
		custom_tran_fun = Symbol("transition", FunctionType(BOOL, [state_t, state_t]))
		next_state_sym = Symbol("next_state", state_t)
		tran_exprs  = [Function(transition_fun, [state_symbol, next_state_sym])]
		tran_exprs += [equal(Function(f_n, [state_symbol]), Function(f, [next_state_sym]))
					   for f_n,f in zip(custom_state_next_funs, custom_state_funs)]
		solver.fun_def(custom_tran_fun, [state_symbol, next_state_sym], reduce(And, tran_exprs))

		def get_mapping(state: Symbol):
			return {Symbol(st.name, st.tpe): Function(ff, [state]) for st,ff in zip(check.states, custom_state_funs)}

		return custom_tran_fun, get_mapping

	def check(self, check: BoundedCheckData, mod: Module, verify_assumptions=True):
		start = time.time()
		solver = Solver(header=mod.smt2_src, do_simplify=self.simplify)
		state_t = Type(mod.name + "_s")

		def map_sym(symbol: Symbol, state_sym):
			tpe = symbol.symbol_type()
			is_bool_ = tpe.is_bv_type() and tpe.width == 1
			ft = FunctionType(BOOL if is_bool_ else tpe, [state_t])
			if tpe.is_array_type():	fn = mod.name + "_m " + symbol.symbol_name()
			else:                   fn = mod.name + "_n " + symbol.symbol_name()
			if is_bool_:	return Ite(Function(Symbol(fn, ft), [state_sym]), BV(1,1), BV(0,1))
			else:       return Function(Symbol(fn, ft), [state_sym])

		# create a list of signals in the module (this includes I/O and state)
		signal_symbols = [Symbol(name, tpe) for name, tpe in chain(mod.inputs.items(), mod.outputs.items(), mod.state.items())]
		for submodule in mod.submodules.values():
			signal_symbols += [Symbol(submodule.io_prefix + name, tpe) for name, tpe in
						chain(submodule.inputs.items(), submodule.outputs.items())]

		# deal with any custom states
		transition_fun, get_state_mapping = self.states(check=check, solver=solver, mod_name=mod.name,
														signal_symbols=signal_symbols, map_sym=map_sym)

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
		# TODO: compute mappings lazily as not all of them will be used
		mappings = [{**{ sym: map_sym(sym, state) for sym in signal_symbols }, **get_state_mapping(state)}
					for state in states]
		# mapping that refers to "state" symbol
		state_symbol = Symbol("state", state_t)
		invariant_map = {**{ sym: map_sym(sym, state_symbol) for sym in signal_symbols }, **get_state_mapping(state_symbol)}
		def in_cycle(ii, ee):
			return substitute(ee, mappings[ii])

		# custom function for "invariant" assumptions
		assume_fun = Symbol("assumptions_hold", FunctionType(BOOL, [state_t]))
		solver.comment("Invariant Assumptions")
		for state in states: solver.add(Function(assume_fun, [state]))
		assumptions = [substitute(aa, invariant_map) for aa in check.assumptions]
		solver.fun_def(assume_fun, [state_symbol], conjunction(*assumptions))

		# check each step
		assertion_symbols = []
		assert_to_cycle = []
		assert_to_expr = []
		for ii, step in enumerate(check.steps):
			solver.comment(f"-------------------")
			solver.comment(f"- Transition {ii} -> {ii+1}")
			solver.comment(f"-------------------")
			if len(check.states) > 0 and ii == 0:
				solver.comment("State Initialization")
				for state in check.states:
					if state.init is not None:
						solver.add(in_cycle(ii, equal(Symbol(state.name, state.tpe), state.init)))
			solver.comment("Assumptions")
			for aa in step.assumptions:
				solver.add(in_cycle(ii, aa))
			solver.comment("Assertions")
			for aa in check.asserts + step.assertions:
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

@dataclass
class FunctionDefinition:
	symbol: Symbol
	args: List[Symbol]
	expr: SmtExpr

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
		self.funs: List[Symbol] = []
		self.fun_defs: List[FunctionDefinition] = []


	def add(self, *assertions):
		self.assertions += [a for a in (self.simplify(a) for a in  assertions) if a != TRUE()]

	def comment(self, s: str):
		self.assertions.append(str(s))

	def fun(self, function: Symbol):
		self.funs.append(function)

	def fun_def(self, function: Symbol, args: List[Symbol], expr: SmtExpr):
		fun_tpe = function.symbol_type()
		assert fun_tpe.is_function_type(), f"Symbol is not a function symbol: {function}"
		assert fun_tpe.return_type == expr.get_type(), f"Return types don't match: {function} vs {expr}"
		assert len(args) == len(fun_tpe.param_types), f"{len(args)} != {len(fun_tpe.param_types)}, {args} vs {fun_tpe.param_types}"
		arg_types = tuple([a.symbol_type() for a in args])
		assert arg_types == fun_tpe.param_types, f"In {function}, types don't match: {arg_types} vs {fun_tpe.param_types}"
		fd = FunctionDefinition(symbol=function, args=args, expr=self.simplify(expr))
		self.fun_defs.append(fd)

	def check_sat(self, filename, assertions, funs: List[Symbol], fun_defs: List[FunctionDefinition], get_cmds=None):
		assert isinstance(funs, list) and isinstance(fun_defs, list)
		get_cmds = default(get_cmds, [])
		stdout, delta = _check_sat(solver=self.bin, header=self.header, filename=filename, funs=funs, fun_defs=fun_defs, assertions=assertions, get_cmds=get_cmds)
		assert 'error' not in stdout, f"SMT solver call failed on {filename}: {stdout}"
		return stdout, delta

	def _check_vc(self, vc, filename):
		vc_validity = Not(conjunction(*vc))
		return self.check_sat(funs=self.funs, fun_defs=self.fun_defs, assertions=self.assertions + [vc_validity], filename=filename)

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
		stdout, delta = self.check_sat(funs=self.funs, fun_defs=self.fun_defs, assertions=self.assertions, filename=filename)
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
		out, sat_time = self.check_sat(funs=self.funs, fun_defs=self.fun_defs, assertions=self.assertions + [vc_validity], filename=filename, get_cmds=get_cmds)
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


def _write_scrip(header, filename, funs: List[Symbol], fun_defs: List[FunctionDefinition], assertions, cmds: list):
	with open(filename, 'w') as ff:
		print("(set-logic QF_AUFBV)", file=ff)
		print("; smt script generated using yosys + a custom python script", file=ff)
		print(file=ff)
		print("; yosys generated:", file=ff)
		print(header, file=ff)
		print("; custom cmds", file=ff)
		for symbol in funs:
			SmtLibCommand(smtcmd.DECLARE_FUN, [symbol]).serialize(outstream=ff, daggify=False)
			print("", file=ff)
		for fd in fun_defs:
			#       NAME                     PARAMS_LIST    RTYPE               EXPR
			args = [fd.symbol.symbol_name(), fd.args,       fd.expr.get_type(), fd.expr]
			SmtLibCommand(smtcmd.DEFINE_FUN, args).serialize(outstream=ff, daggify=False)
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
def _check_sat(solver, header, filename, funs: List[Symbol], fun_defs: List[FunctionDefinition], assertions: list, get_cmds: list):
	start = time.time()
	cmds = [SmtLibCommand(smtcmd.CHECK_SAT, [])] + get_cmds
	_write_scrip(header=header, filename=filename, funs=funs, fun_defs=fun_defs, assertions=assertions, cmds=cmds)
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
	out, delta = _solve.check_sat(filename=f.name, assertions=[Not(e)], funs=funs, fun_defs=[])
	return out == 'unsat'

def is_unsat(e) -> bool:
	f = tempfile.NamedTemporaryFile()
	asserts = e if isinstance(e, list) else [e]
	funs = list(functools.reduce(lambda a,b: a|b,  (get_free_variables(a) for a in asserts)))
	out, delta = _solve.check_sat(filename=f.name, assertions=asserts, funs=funs, fun_defs=[])
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