#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
from typing import List
from functools import reduce

ALU_RESULT_ADD  = BV(0, 2)
ALU_RESULT_SR   = BV(1, 2)
ALU_RESULT_LT   = BV(2, 2)
ALU_RESULT_BOOL = BV(3, 2)

BOOL_OP_XOR = BV(0, 2)
BOOL_OP_OR  = BV(2, 2)
BOOL_OP_AND = BV(3, 2)

def flatten(ll: List[list]) -> list:
	return reduce(lambda a, b: a + b, ll)

class AluSpec(Spec):
	def __init__(self, bits=32):
		self.bits = bits
		transactions = [self.Idle(), self.Add(), self.Sub(), self.Bitwise(), self.LeftShiftBy(1)]
		inv = [lambda state: Bool(True)]
		super().__init__(transactions=flatten(transactions), invariances=inv)

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

	def Idle(self) -> List[Transaction]:
		return [Transaction(name="idle", args=[], ret_args=[], semantics=lambda : None, proto=Protocol([{}]))]

	def Add(self) -> List[Transaction]:
		ctrl = Map('i_sub', Bool(False)) | Map('i_rd_sel', ALU_RESULT_ADD)
		return [self.Op('Add', BVAdd, ctrl)]

	def Sub(self) -> List[Transaction]:
		ctrl = Map('i_sub', Bool(True)) | Map('i_rd_sel', ALU_RESULT_ADD)
		return [self.Op('Sub', BVSub, ctrl)]

	def Bitwise(self) -> List[Transaction]:
		ops = [
			('Or',  BVOr,  BOOL_OP_OR),
			('Xor', BVXor, BOOL_OP_XOR),
			('And', BVAnd, BOOL_OP_AND),
		]
		return [self.Op(name, bvop, ctrl = Map('i_rd_sel', ALU_RESULT_BOOL) | Map('i_bool_op', op))
			for name, bvop, op in ops]

	def LeftShiftBy(self, shift_amount) -> List[Transaction]:
		assert self.bits == 32
		assert shift_amount & 0x1f == shift_amount, f"{shift_amount}"

		shift_right = Bool(False)
		a = Symbol('a', BVType(self.bits))
		b = BV(shift_amount, 5)
		c = Symbol('c', BVType(self.bits))

		semantics = lambda a: {'c': BVLShl(a, BVZExt(b, 32-5))}

		start = Map('i_en', Bool(False))
		# TODO: any constraints on `o_sh_done` ?
		load_shmat = BitSerial('i_op_b', b)  | (Map('i_init', Bool(True)) | Map('i_en', Bool(True)) | Map('i_shamt_en', Bool(True))  | Map('i_sh_right', shift_right)) * 5
		# TODO: add padding
		shift_delay = 32 - shift_amount
		shift_ctl    = (Map('i_init', Bool(False)) | Map('i_sh_right', shift_right) | Map('i_shamt_en', Bool(False)) | Map('i_rd_sel', ALU_RESULT_SR)) * (32 + shift_delay)
		shift_en     = Map('i_en', Bool(False)) * shift_delay +  Map('i_en', Bool(True)) * 32
		shift_arg    = BitSerial('i_buf', a) + BitSerial('i_buf', a, max_bits=shift_delay)
		shift_done   = Map('o_sh_done', Bool(False)) * shift_delay + Map('o_sh_done', Bool(True)) + Map('o_sh_done', Bool(False)) * 32
		shift_result = BitSerial('o_rd', c) >> (shift_delay)
		shift_proto  = shift_arg | shift_done | shift_result | shift_ctl | shift_en

		protocol = start + load_shmat + shift_proto
		return [Transaction(name=f"Shift<{self.bits}, {shift_amount}>", args=[a], ret_args=[c], semantics=semantics, proto=protocol)]

	def Shifts(self) -> List[Transaction]:
		assert self.bits == 32
		print("TODO: SRL & SRA")

		shift_right = Bool(False)

		a = Symbol('a', BVType(self.bits))
		b = Symbol('b', BVType(5))
		c = Symbol('c', BVType(self.bits))

		# reset ALU
		phase_idle = Map('i_en', Bool(False))
		# load shift amount
		phase_init = (
			(Map('i_shmat_en', Bool(True)) * 5)  |
			BitSerial('i_op_b', b)               |
			(Map('i_sh_right', shift_right) * 5)
		)



src = [os.path.join('fork', 'rtl', name + '.v') for name in ['serv_alu', 'ser_lt', 'ser_shift', 'ser_add', 'shift_reg']]

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('serv_alu', src, reset=HighActiveReset('i_rst'), ignore_wires=False)
	spec = AluSpec()

	print(f"Trying to proof {mod.name}")
	#print(mod)

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, spec, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
