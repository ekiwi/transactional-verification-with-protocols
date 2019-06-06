#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class AluSpec(Spec):
	def __init__(self, bits=32):
		transactions = [self.Add]
		super().__init__(transactions=[tt(bits) for tt in transactions])

	def BaseProtocol(self, a, b, c, ctrl=None):
		bits = a.bv_width()
		assert b.bv_width() == bits
		assert c.bv_width() == bits
		basic = Map('i_en', Bool(False)) + (BitSerial('i_rs1', a) | BitSerial('i_op_b', b) | BitSerial('o_rd', c) | Map('i_en', Bool(True)) * bits)
		if ctrl is not None:
			assert len(ctrl) == 1
			return basic | ((ctrl * bits) >> 1)
		return basic

	def Add(self, bits):
		a = Symbol('a', BVType(bits))
		b = Symbol('b', BVType(bits))
		c = Symbol('c', BVType(bits))

		def semantics(a, b):
			c = BVAdd(a, b)
			return {'c': c}

		ctrl = Map('i_sub', Bool(False)) | Map('i_rd_sel', BV(0, 2))
		protocol = self.BaseProtocol(a, b, c, ctrl=ctrl)

		return Transaction(name=f"Add<{bits}>", args=[a, b], ret_args=[c], semantics=semantics, proto=protocol)

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
