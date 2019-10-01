#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import List, Tuple, Dict, Optional, Set
import itertools
from pysmt.shortcuts import *
from .module import Module
from .utils import *
from .spec import Transaction, Spec

class CheckStep:
	def __init__(self, cycle):
		self.cycle =  cycle
		self.assertions = []
		self.assumptions = []

class BoundedCheck:
	def __init__(self, name: str, verifier: "Verifier", cycles: int):
		self.name = name
		self._mod = verifier.mod
		self._engine = verifier.engine
		self.steps= [CheckStep(ii) for ii in range(cycles + 1)]
		self.constants = []
		self.functions = []
		self.assumptions = []
		self._sym_names: Set[str] = set(self._mod.signals.keys())
		self._active = False
	@property
	def cycles(self):
		assert self._active
		return len(self.steps) - 1

	def assume_at(self, cycle, expr):
		assert self._active
		assert self.cycles >= cycle >= 0
		self.steps[cycle].assumptions.append(expr)

	def assume_always(self, expr):
		assert self._active
		self.assumptions.append(expr)

	def assert_at(self, cycle, expr):
		assert self._active
		assert self.cycles >= cycle >= 0
		self.steps[cycle].assertions.append(expr)

	def constant(self, symbol):
		assert self._active
		name = symbol.symbol_name()
		assert name not in self._sym_names, f"symbol {symbol} already exists!"
		self._sym_names.add(name)
		self.constants.append(symbol)

	def function(self, symbol, expr):
		assert self._active
		name = symbol.symbol_name()
		assert name not in self._sym_names, f"symbol {symbol} already exists!"
		self._sym_names.add(name)
		self.functions.append((symbol, expr))

	def __enter__(self):
		self._active = True
		return self

	def __exit__(self, exc_type, exc_val, exc_tb):
		if exc_type is not None: return
		self._engine.check(self, mod=self._mod)

class Verifier:
	def __init__(self, mod: Module, spec: Spec, engine):
		self.mod = mod
		self.spec = spec
		self.engine = engine
		self.verbose = True

	def do_transaction(self, tran: Transaction, check: BoundedCheck, assume_invariances=False, no_asserts=False):
		assert check.cycles == len(tran.proto), f"need to fully unroll transaction! {check.cycles} vs {len(tran.proto)}"

		# assume invariances hold at the beginning of the transaction
		if assume_invariances:
			for inv in self.spec.invariances:
				check.assume_at(0, inv(self.mod))

		# assume reset is inactive during the transaction
		if self.mod.reset is not None:
			check.assume_always(Not(self.mod[self.mod.reset]))

		# declare transaction args
		for arg in tran.args:
			check.constant(arg)

		# apply cycle behavior
		for ii, m in enumerate(tran.proto.mappings):
			for signal_name, expr in m.items():
				assert not self.mod.is_state(signal_name), f"protocols may only read/write from io: {signal_name}"

				if self.mod.is_output(signal_name):
					if not no_asserts:
						check.assert_at(ii, equal(self.mod[signal_name], expr))
				else:
					# if the signal is an input, we just apply the constraint for this cycle
					assert self.mod.is_input(signal_name)
					check.assume_at(ii, equal(self.mod[signal_name], expr))

	def proof_transaction(self, tran: Transaction):
		cycles = len(tran.proto)
		with BoundedCheck(f"transaction {tran.name} is correct", self, cycles=cycles) as check:
			# instantiate unrolled transaction
			self.do_transaction(tran=tran, assume_invariances=True, check=check)

			# declare architectural states and bind them to the initialization of the circuit state
			arch_state = {name: Symbol(name, tpe) for name, tpe in self.spec.arch_state.items()}
			arch_state_n = {name: Symbol(name + "_n", tpe) for name, tpe in self.spec.arch_state.items()}
			# TODO: we could assign an initial value to the arch state that is derived from the initial circuit state
			for sym in arch_state.values():
				check.constant(sym)
			# connect initial circuit and arch state
			mapping_assumptions = self.spec.mapping(self.mod, **arch_state)
			for a in mapping_assumptions:
				check.assume_at(0, a)

			# semantics as pure function calculated during initialization
			def rename(symbols):
				return {sym.symbol_name(): sym for sym in symbols}
			args = rename(tran.args)
			# arg constants were already declared during unrolling
			sem_out = tran.semantics(**args, **arch_state)
			ret_args = rename(tran.ret_args)
			for name, sym in itertools.chain(ret_args.items(), arch_state_n.items()):
				check.function(sym, sem_out[name])

			# verify arch states after transaction
			mapping_assertions = self.spec.mapping(self.mod, **arch_state_n)
			for a in mapping_assertions:
				check.assert_at(cycles, a)

	def proof_transactions(self):
		for trans in self.spec.transactions:
			self.proof_transaction(trans)

	def proof_invariance(self, invariance):
		# TODO: take strengthening invariances into account
		with BoundedCheck("invariance holds after reset", self, cycles=1) as check:
			check.assume_at(0, self.mod[self.mod.reset])
			# invariance should hold after reset
			check.assert_at(1, invariance(self.mod))

		with BoundedCheck("invariance is inductive over idle period", self, cycles=1) as check:
			print("TODO: specify IDLE as regular transaction!")

		for tran in self.spec.transactions:
			cycles = len(tran.proto)
			with BoundedCheck(f"invariance is inductive over {tran.name} transaction", self, cycles=cycles) as check:
				self.do_transaction(tran=tran, check=check, assume_invariances=False, no_asserts=True)
				# assume this particular invariance
				check.assume_at(0, invariance(self.mod))
				# invariance should hold after transaction
				check.assert_at(cycles, invariance(self.mod))

	def proof_invariances(self):
		# TODO: take invariance dependence into account
		for inv in self.spec.invariances:
			self.proof_invariance(inv)

	def proof_all(self):
		self.proof_invariances()
		self.proof_transactions()
