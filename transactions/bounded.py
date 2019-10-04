#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import Set

class CheckStep:
	def __init__(self, cycle):
		self.cycle =  cycle
		self.assertions = []
		self.assumptions = []

class CheckResult:
	def __init__(self, solver_time: float, total_time: float):
		self.solver_time = solver_time
		self.total_time = total_time
	def __str__(self): return f"{self.total_time:.3f} sec, {self.solver_time:.3f} sec to solve"
	def __repr__(self): return str(self)

class CheckFailure(CheckResult):
	def __init__(self, solver_time: float, total_time: float, cycle: int , assert_ii: int, assert_expr, model = None, model_time: float = 0.0):
		super().__init__(solver_time, total_time)
		self.cycle = cycle
		self.assert_ii = assert_ii
		self.assert_expr = assert_expr
		self.model = model
		self.model_time = model_time
	def __str__(self):
		return f"Fail! b{self.assert_ii} `{self.assert_expr}` @ cycle {self.cycle}. After: {super().__str__()}."

class CheckSuccess(CheckResult):
	def __init__(self, solver_time: float, total_time: float):
		super().__init__(solver_time, total_time)
	def __str__(self):
		return f"Success! After: {super().__str__()}."

class BoundedCheck:
	def __init__(self, name: str, verifier: "Verifier", cycles: int):
		self.name = name
		self._mod = verifier.mod
		self._engine = verifier.engine
		self.steps= [CheckStep(ii) for ii in range(cycles + 1)]
		self.constants = []
		self.functions = []
		self.assumptions = []
		self.initialize = False
		self._sym_names: Set[str] = set(self._mod.signals.keys())
		self._active = False
		self.verbose = True
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

	def initialize_state(self):
		assert self._active
		self.initialize = True

	def __enter__(self):
		self._active = True
		return self

	def __exit__(self, exc_type, exc_val, exc_tb):
		if exc_type is not None: return
		res = self._engine.check(self, mod=self._mod)
		assert isinstance(res, CheckResult), f"Unexpected result type: {type(res)}"
		success = isinstance(res, CheckSuccess)
		if self.verbose:
			timing = f"{res.total_time:.3f} sec, {res.solver_time:.3f} sec to solve"
			valid = "✔" if success else "❌"
			print(f"{valid}️ {self.name} ({timing})")

		assert success, f"found counter example to check {self.name}\n{res}"
		return success