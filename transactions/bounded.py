#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import Set, Dict, List, Optional

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
	def __init__(self, solver_time: float, total_time: float, cycle: int , assert_ii: int, assert_expr, model = None):
		super().__init__(solver_time, total_time)
		self.cycle = cycle
		self.assert_ii = assert_ii
		self.assert_expr = assert_expr
		self.model = model
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

		if not success:
			res.model.to_vcd('test.vcd')

		assert success, f"found counter example to check {self.name}\n{res}"
		return success

from vcd import VCDWriter

def get_size(typ):
	if typ.is_bool_type(): return 1
	elif typ.is_bv_type(): return typ.width
	else: raise RuntimeError(f"unsupported type {typ}")

class Model:
	def __init__(self, name: str, cycles: int, signals: list, indices: Dict[str, int], data: List[List[Optional[int]]], creation_time: float = 0.0):
		assert len(data) > 0, "empty data"
		assert len(data) == cycles
		self.name = name
		self.cycles = cycles
		self.signals = signals
		self.indices = indices
		self.data = data
		self.creation_time = creation_time

	def to_vcd(self, filename):
		with open(filename, 'w') as ff:
			with VCDWriter(ff, timescale='1 ns', date='today') as writer:
				vars = {}
				for sym in self.signals:
					name = sym.symbol_name()
					scope = '.'.join([self.name] + name.split('.')[:-1])
					ii = self.indices[name]
					vv = writer.register_var(scope=scope, name=name.split('.')[-1], var_type='wire',
											 size=get_size(sym.symbol_type()),
											 init=self.data[0][ii])
					vars[ii] = vv
				for cycle in range(1, len(self.data)):
					past, now = self.data[cycle-1], self.data[cycle]
					assert len(now) == len(past)
					for signal in range(len(now)):
						if past[signal] != now[signal]:
							writer.change(var=vars[signal], timestamp=cycle, value=now[signal])

				writer.close(len(self.data))
