#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

ALU_RESULT_ADD  = BV(0, 2)
ALU_RESULT_SR   = BV(1, 2)
ALU_RESULT_LT   = BV(2, 2)
ALU_RESULT_BOOL = BV(3, 2)

class AluSpec(Spec):
	def __init__(self, bits=32):
		self.bits = bits
		transactions = [self.Add, self.Sub]
		super().__init__(transactions=[tt() for tt in transactions])

	def BaseProtocol(self, a, b, c, ctrl=None):
		bits = a.bv_width()
		assert b.bv_width() == bits
		assert c.bv_width() == bits
		basic = Map('i_en', Bool(False)) + (BitSerial('i_rs1', a) | BitSerial('i_op_b', b) | BitSerial('o_rd', c) | Map('i_en', Bool(True)) * bits)
		if ctrl is not None:
			assert len(ctrl) == 1
			return basic | ((ctrl * bits) >> 1)
		return basic

	def Op(self, name, BVOperation, ctrl):
		a = Symbol('a', BVType(self.bits))
		b = Symbol('b', BVType(self.bits))
		c = Symbol('c', BVType(self.bits))
		semantics = lambda a, b: {'c': BVOperation(a, b)}
		protocol = self.BaseProtocol(a, b, c, ctrl=ctrl)
		return Transaction(name=f"{name}<{self.bits}>", args=[a, b], ret_args=[c], semantics=semantics, proto=protocol)

	def Add(self):
		ctrl = Map('i_sub', Bool(False)) | Map('i_rd_sel', ALU_RESULT_ADD)
		return self.Op('Add', BVAdd, ctrl)

	def Sub(self):
		ctrl = Map('i_sub', Bool(True)) | Map('i_rd_sel', ALU_RESULT_ADD)
		return self.Op('Sub', BVSub, ctrl)

src = [os.path.join('serv', 'rtl', name + '.v') for name in ['serv_alu', 'ser_lt', 'ser_shift', 'ser_add', 'shift_reg']]

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('serv_alu', src, reset='i_rst')
	spec = AluSpec()

	reset_env()
	print(f"Trying to proof {mod.name}")
	print(mod)
	solver = Solver(mod.smt2_src)
	engine = ProofEngine(mod=mod,spec=spec, solver=solver, outdir="smt2")
	engine.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
