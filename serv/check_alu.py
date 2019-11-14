#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

ALU_RESULT_ADD  = BV(0, 2)
ALU_RESULT_SR   = BV(1, 2)
ALU_RESULT_LT   = BV(2, 2)
ALU_RESULT_BOOL = BV(3, 2)

BOOL_OP_XOR = BV(0, 2)
BOOL_OP_OR  = BV(2, 2)
BOOL_OP_AND = BV(3, 2)

a   = Symbol('a', BVType(32))
b   = Symbol('b', BVType(32))
res = Symbol('res', BVType(32))

def protocol(ctrl_inputs=None):
	ctrl_inputs = {} if ctrl_inputs is None else ctrl_inputs
	return Protocol(
		[Transition(inputs={'i_en': BV(0,1)})] +
		[Transition(inputs={'i_rs1': BVExtract(a, ii, ii), 'i_op_b': BVExtract(b, ii, ii),
							'i_en': BV(1,1), **ctrl_inputs},
					outputs={'o_rd': BVExtract(res, ii, ii)})
		for ii in range(32)]
	)

def make_op(name, BVOperation, ctrl) -> Transaction:
	return Transaction(name=name, proto=protocol(ctrl), semantics={'res': BVOperation(a,b)},
					   args={'a': BVType(32), 'b': BVType(32)}, ret_args={'res': BVType(32)})

alu_spec = Spec(transactions=[
	make_op("Add", BVAdd, {'i_sub': BV(0,1), 'i_rd_sel': ALU_RESULT_ADD}),
	make_op("Sub", BVSub, {'i_sub': BV(1,1), 'i_rd_sel': ALU_RESULT_ADD}),
	make_op("Or",  BVOr,  {'i_bool_op': BOOL_OP_OR,  'i_rd_sel': ALU_RESULT_BOOL}),
	make_op("Xor", BVXor, {'i_bool_op': BOOL_OP_XOR, 'i_rd_sel': ALU_RESULT_BOOL}),
	make_op("And", BVAnd, {'i_bool_op': BOOL_OP_AND, 'i_rd_sel': ALU_RESULT_BOOL}),
	# TODO: potentially special case IDLE
	Transaction("Idle"),
])

# TODO: fix shifts

# def LeftShiftBy(self, shift_amount) -> List[Transaction]:
# 	assert self.bits == 32
# 	assert shift_amount & 0x1f == shift_amount, f"{shift_amount}"
#
# 	shift_right = Bool(False)
# 	a = Symbol('a', BVType(self.bits))
# 	b = BV(shift_amount, 5)
# 	c = Symbol('c', BVType(self.bits))
#
# 	semantics = lambda a: {'c': BVLShl(a, BVZExt(b, 32-5))}
#
# 	start = Map('i_en', Bool(False))
# 	# TODO: any constraints on `o_sh_done` ?
# 	load_shmat = BitSerial('i_op_b', b)  | (Map('i_init', Bool(True)) | Map('i_en', Bool(True)) | Map('i_shamt_en', Bool(True))  | Map('i_sh_right', shift_right)) * 5
# 	# TODO: add padding
# 	shift_delay = 32 - shift_amount
# 	shift_ctl    = (Map('i_init', Bool(False)) | Map('i_sh_right', shift_right) | Map('i_shamt_en', Bool(False)) | Map('i_rd_sel', ALU_RESULT_SR)) * (32 + shift_delay)
# 	shift_en     = Map('i_en', Bool(False)) * shift_delay +  Map('i_en', Bool(True)) * 32
# 	shift_arg    = BitSerial('i_buf', a) + BitSerial('i_buf', a, max_bits=shift_delay)
# 	shift_done   = Map('o_sh_done', Bool(False)) * shift_delay + Map('o_sh_done', Bool(True)) + Map('o_sh_done', Bool(False)) * 32
# 	shift_result = BitSerial('o_rd', c) >> (shift_delay)
# 	shift_proto  = shift_arg | shift_done | shift_result | shift_ctl | shift_en
#
# 	protocol = start + load_shmat + shift_proto
# 	return [Transaction(name=f"Shift<{self.bits}, {shift_amount}>", args=[a], ret_args=[c], semantics=semantics, proto=protocol)]

# def Shifts(self) -> List[Transaction]:
# 	assert self.bits == 32
# 	print("TODO: SRL & SRA")
#
# 	shift_right = Bool(False)
#
# 	a = Symbol('a', BVType(self.bits))
# 	b = Symbol('b', BVType(5))
# 	c = Symbol('c', BVType(self.bits))
#
# 	# reset ALU
# 	phase_idle = Map('i_en', Bool(False))
# 	# load shift amount
# 	phase_init = (
# 		(Map('i_shmat_en', Bool(True)) * 5)  |
# 		BitSerial('i_op_b', b)               |
# 		(Map('i_sh_right', shift_right) * 5)
# 	)



src = [os.path.join('fork', 'rtl', name + '.v') for name in ['serv_alu', 'ser_lt', 'ser_shift', 'ser_add', 'shift_reg']]

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('serv_alu', src, ignore_wires=False)
	prob = VerificationProblem(alu_spec, "serv_alu")
	print(f"Trying to proof {mod.name}")
	#print(mod)

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
