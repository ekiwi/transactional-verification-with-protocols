#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess, tempfile
from pysmt.shortcuts import *
from pysmt.smtlib.script import SmtLibScript, smtcmd
import time
from .utils import *


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

	def reset(self):
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


	def solve(self, filename=None, get_model=True, get_values=None, case_split=None, print_time=False):
		case_split = default(case_split, list())
		filename = default(filename, tempfile.mkstemp()[1])

		# generate script
		script = SmtLibScript()
		for f in self.funs:
			script.add(smtcmd.DECLARE_FUN, [f])

		if len(case_split) > 0:
			# TODO: tghis check only works for unconstrained variables!
			# check for completeness
			script.add(smtcmd.ASSERT, [Not(disjunction(*case_split))])
			r = self._check_sat(script=script, filename=filename)
			if r == sat:
				constraints = '\n'.join(str(c) for c in case_split)
				raise RuntimeError(f"Incomplete case splitting:\n{constraints}")
			script.commands.pop()

			cases = case_split
		else:
			cases = [Bool(True)]

		for a in self.assertions:
			script.add(smtcmd.ASSERT, [a])


		#print(cases)

		assert len(cases) > 0, "0 cases are trivially unsat"
		detected_sat = False
		for case_constraint in cases:
			# add constraint
			script.add(smtcmd.ASSERT, [case_constraint])

			if len(case_split) > 0:
				print(f"assuming: {case_constraint}")

			# check this case
			start = time.time()
			r = self._check_sat(script=script, filename=filename)
			delta = time.time() - start
			if print_time:
				print(f"Check with {self.bin} returned {r} and took {delta}")
			# if it failes (i.e. we get sat, emit a counter example)
			if r == sat:
				detected_sat = True
				break

			# remove constraints
			script.commands.pop()



		# if all cases are unsat -> return unsat
		if not detected_sat:
			return unsat, None

		# if no model requested
		if not get_model:
			return sat, None

		# get model
		script.add(smtcmd.CHECK_SAT, [])
		if get_values is None:
			script.add(smtcmd.GET_MODEL, [])
		else:
			for vv in get_values:
				script.add(smtcmd.GET_VALUE, [vv])
		start = time.time()
		self._write_scrip(filename=filename, script=script)
		r = subprocess.run([self.bin, filename], stdout=subprocess.PIPE, check=True).stdout.decode('utf-8')
		delta = time.time() - start
		if print_time:
			print(f"Generating a CEX with {self.bin} took {delta}")
		return sat, r
