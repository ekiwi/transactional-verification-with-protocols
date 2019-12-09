#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import Symbol, BVType, Equals, BV, BVMul, BVConcat
from transactions import *
from functools import reduce

mod = Module.load('picorv32_pcpi_mul', ['picorv32.v'], high_active_reset=False)

rs1_data = Symbol('rs1_data', BVType(32))
rs2_data = Symbol('rs2_data', BVType(32))
rd_data = Symbol('rd_data', BVType(32))

##############################
p = ProtocolBuilder(mod)
p['pcpi_valid'] = 1

funct3 = 0b000 # MUL
# TODO: accurately model don't cares
funct7 = 0b0000001 # 7
opcode = 0b0110011 # 7
p['pcpi_insn'] = (funct7 << 25) | (funct3 << 12) | opcode
p['pcpi_rs1'] = rs1_data
p['pcpi_rs2'] = rs2_data

p['pcpi_wr'].expect(0)
p['pcpi_ready'].expect(0)
#p['pcpi_wait'].expect(0)

p.step()

p['pcpi_valid'] = 0
p['pcpi_insn'] = DontCare
p['pcpi_rs1'] = DontCare
p['pcpi_rs2'] = DontCare

p['pcpi_ready'].wait(1, max=34)

p['pcpi_wr'].expect(1)
p['pcpi_rd'].expect(rd_data)
##############################

protocol = p.finish()
semantics = { 'rd_data': BVMul(rs1_data, rs2_data) }
args={'rs1_data': BVType(32), 'rs2_data': BVType(32)}
ret_args={'rd_data': BVType(32)}

spec = Spec(
	transactions=[Transaction(f"MUL", proto=protocol, semantics=semantics, args=args, ret_args=ret_args)],
	idle=ProtocolBuilder(mod).inputs(pcpi_valid=0).finish()
)

invariances = [
	Equals(Symbol('pcpi_wr', BVType(1)), BV(0,1)),
	Equals(Symbol('pcpi_ready', BVType(1)), BV(0,1)),
	Equals(Symbol('instr_mul', BVType(1)), BV(0,1)),
	Equals(Symbol('instr_mulh', BVType(1)), BV(0,1)),
	Equals(Symbol('instr_mulhsu', BVType(1)), BV(0,1)),
	Equals(Symbol('instr_mulhu', BVType(1)), BV(0,1)),
	Equals(Symbol('mul_finish', BVType(1)), BV(0,1)),
	Equals(Symbol('mul_waiting', BVType(1)), BV(1,1)),
]
mappings = []

def main() -> int:
	prob = VerificationProblem(spec=spec, implementation='picorv32_pcpi_mul',
							   invariances=invariances, mappings=mappings)

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	Verifier(mod, prob, ee).proof_all()
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
