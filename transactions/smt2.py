#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# SMT2 Lib based backend for BoundedCheck

import subprocess, tempfile, os, itertools
from pysmt.shortcuts import *
from pysmt.smtlib.script import SmtLibScript, smtcmd
import time
from .utils import *
from .verifier import BoundedCheck
from .module import Module

class SMT2ProofEngine:
	def __init__(self, outdir=None):
		self.verbose = True
		self.outdir = outdir
		if self.outdir is not None:
			assert os.path.isdir(self.outdir)

	def check(self, check: BoundedCheck, mod: Module):
		solver = Solver(header=mod.smt2_src)

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
			solver.add(equal(sym, expr))

		# assert initialization functions in first state if requested
		if check.initialize:
			init_fun = Symbol(mod.name + "_i", FunctionType(BOOL, [state_t]))
			solver.add(Function(init_fun, [states[0]]))

		# add invariant assumptions to steps
		assumptions = [step.assumptions + check.assumptions for step in check.steps]
		assertions  = [step.assertions for step in check.steps]

		# map module i/o and state to cycle dependant function
		symbols = [Symbol(s.name, s.tpe) for s in itertools.chain(mod.inputs.values(), mod.outputs.values(), mod.state.values())]
		# TODO: compute mappings lazily as not all of them will be used
		def map_sym(symbol: Symbol, state):
			ft = FunctionType(symbol.symbol_type(), [state_t])
			if symbol.symbol_type().is_array_type():
				fn = mod.name + "_m " + symbol.symbol_name()
			else:
				fn = mod.name + "_n " + symbol.symbol_name()
			return Function(Symbol(fn, ft), [state])
		mappings = [{ sym: map_sym(sym, state) for sym in symbols } for state in states]
		def in_cycle(ii, ee):
			return substitute(ee, mappings[ii])

		# check each step
		for ii, (assums, asserts) in enumerate(zip(assumptions, assertions)):
			for aa in assums:
				solver.add(in_cycle(ii, aa))
			for aa in asserts:
				solver.add(in_cycle(ii, Not(aa)))

		# run solver
		if self.outdir is not None:	filename = os.path.join(self.outdir, f"{check.name}.smt2")
		else:                                  filename = None
		valid, delta = solver.solve(filename=filename)
		if self.verbose:
			if valid:
				print(f"✔️ {check.name} ({delta:.2f} sec)")
			else:
				print(f"❌ {check.name} ({delta:.2f} sec)")

		assert valid, f"found counter example to check {check.name}"
		return valid





sat = "sat"
unsat = "unsat"

class Solver:
	def __init__(self, header, logic='QF_AUFBV', bin='yices-smt2'):
		self.header = header
		self.logic = logic
		self.bin = bin
		subprocess.run(['which', bin], check=True, stdout=subprocess.PIPE)
		self.assertions = []
		self.funs = []

	def add(self, *assertions):
		self.assertions += assertions

	def fun(self, function):
		self.funs.append(function)

	def _write_scrip(self, filename, script):
		with open(filename, 'w') as ff:
			print("(set-logic QF_AUFBV)", file=ff)
			print("; smt script generated using yosys + a custom python script", file=ff)
			print(file=ff)
			print("; yosys generated:", file=ff)
			print(self.header, file=ff)
			print("; custom cmds", file=ff)
			script.serialize(outstream=ff, daggify=False)

	def _check_sat(self, script, filename):
		script.add(smtcmd.CHECK_SAT, [])
		self._write_scrip(filename=filename, script=script)
		script.commands.pop() # remove check sat
		r = subprocess.run([self.bin, filename], stdout=subprocess.PIPE, check=True)
		return r.stdout.decode('utf-8').strip()

	def solve(self, filename=None):
		filename = default(filename, tempfile.mkstemp()[1])

		# generate script
		script = SmtLibScript()
		for f in self.funs:
			script.add(smtcmd.DECLARE_FUN, [f])
		for a in self.assertions:
			script.add(smtcmd.ASSERT, [a])

		start = time.time()
		r = self._check_sat(script=script, filename=filename)
		delta = time.time() - start
		return r == unsat, delta