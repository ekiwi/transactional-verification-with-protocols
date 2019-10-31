#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
from functools import reduce

class RegfileSpec(Spec):
	def __init__(self):
		# architectural state
		regs = Symbol('regs', ArrayType(BVType(5), BVType(32)))

		# build transaction
		rs1_addr = Symbol('rs1_addr', BVType(5))
		rs2_addr = Symbol('rs2_addr', BVType(5))
		rd_enable = Symbol('rd_enable')
		rd_addr = Symbol('rd_addr', BVType(5))
		rd_data = Symbol('rd_data', BVType(32))
		args = [rs1_addr, rs2_addr, rd_enable, rd_addr, rd_data]
		rs1_data = Symbol('rs1_data', BVType(32))
		rs2_data = Symbol('rs2_data', BVType(32))
		ret = [rs1_data, rs2_data]

		protocol = (
			(Map('o_ready', Bool(False)) * 2 + Map('o_ready', Bool(True)) + Map('o_ready', Bool(False)) * 32) |
			(Map('i_go', Bool(True)) + Map('i_go', Bool(False)) * 34) |
			(Repeat('i_rs1_addr', rs1_addr, 32) >> 1) |
			(Repeat('i_rs2_addr', rs2_addr, 32) >> 1) |
			(Repeat('i_rd_addr', rd_addr, 32) >> 3)   |
			(Map('i_rd_en', Bool(False)) * 3 + Repeat('i_rd_en', rd_enable, 32))   |
			(BitSerial('o_rs1', rs1_data) >> 3)       |
			(BitSerial('o_rs2', rs2_data) >> 3)       |
			(BitSerial('i_rd', rd_data) >> 3)
		)
		assert len(protocol) == 35

		def is_zero(expr):
			return Equals(expr, BV(0, expr.bv_width()))
		do_write = And(rd_enable, Not(Equals(rd_addr, BV(0, 5))))
		semantics = {
			'rs1_data': Ite(is_zero(rs1_addr), BV(0, 32), Select(regs, rs1_addr)),
			'rs2_data': Ite(is_zero(rs2_addr), BV(0, 32), Select(regs, rs2_addr)),
			'regs': Ite(do_write, Store(regs, rd_addr, rd_data), regs)

		}

		idle = Transaction(name="idle", proto=Map('i_go', Bool(False)) | Map('i_rd_en', Bool(False)) | Map('o_ready', Bool(False)))
		transactions = [idle, Transaction(name="rw", args=args, ret_args=ret, semantics=semantics, proto=protocol)]

		# TODO: infer
		x0_inv = conjunction(*[Equals(Select(Symbol('memory', ArrayType(BVType(9), BVType(2))), BV(j, 9)), BV(0,2)) for j in range(16)])
		inv = [
			Not(Symbol('o_ready')),	Not(Symbol('t')), Equals(Symbol('wcnt', BVType(5)), BV(0, 5)),
			x0_inv]
		super().__init__(
			state=[regs],
			mapping=mapping,
			transactions=transactions,
			invariances=inv)





regfile_v = os.path.join('fork', 'rtl', 'serv_regfile.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	# map regs to memory
	mem = Symbol('memory', ArrayType(BVType(9), BVType(2)))
	regs = Symbol('regs', ArrayType(BVType(5), BVType(32)))
	mappings = [
		StateMapping(
			arch=Select(regs, BV(ii, 5)),
			impl=reduce(BVConcat, (Select(mem, BV(ii * 16 + jj, 9)) for jj in reversed(range(16))))
		)
	for ii in range(1, 32) ]

	# invariances
	x0_inv = conjunction(
		*[Equals(Select(Symbol('memory', ArrayType(BVType(9), BVType(2))), BV(j, 9)), BV(0, 2)) for j in range(16)])
	invariances = [
		Not(Symbol('o_ready')),
		Not(Symbol('t')),
		Equals(Symbol('wcnt', BVType(5)), BV(0, 5)),
		x0_inv]

	prob = VerificationProblem(spec=RegfileSpec(), implementation='serv_regfile', invariances=invariances, mappings=mappings)

	mod = Module.load('serv_regfile', [regfile_v], reset=HighActiveReset('i_rst'))

	#ee = SMT2ProofEngine(outdir='../smt2')
	ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
