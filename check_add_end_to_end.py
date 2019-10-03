#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

# experiment to see what happens if we give it a single instruction

class ServTop(Spec):
	def __init__(self, bits):

		########## Architectural State: register file
		regs = ArrayType(BVType(5), BVType(32))  # ArraySignal('x', 5, 32)
		map_regs_to_mem = True
		def mapping(mod: Module, regs):
			asserts = []
			memory = mod['memory']
			for ii in range(1, 32):
				reg = Select(regs, BV(ii, 5))
				if map_regs_to_mem:
					iis = [Select(memory, BV(ii * 16 + jj, 9)) for jj in reversed(range(16))]
					asserts.append(Equals(reg, reduce(BVConcat, iis)))
				else:
					for jj in range(16):
						a = Select(memory, BV(ii * 16 + jj, 9))
						b = BVExtract(reg, start=jj * 2, end=jj * 2 + 1)
						asserts.append(Equals(a, b))
			return asserts

		#### Add Instruction
		funct7 = BV(0, 7)
		rs2 = Symbol('rs2', BVType(5))
		rs1 = Symbol('rs1', BVType(1))
		funct3 = BV(0, 3)
		rd = Symbol('rd', BVType(1))
		opcode = BV(0b0110011, 7)

		instruction = cat(funct7, rs2, rs1, funct3, rd, opcode)


		protocol = (Map('i_timer_irq', Bool(False)) | Map('i_ibus_rdt', instruction) | Map('i_ibus_ack', True)) * 3


		def semantics(rs1, rs2, rd, regs):
			a = Select(regs, rs1)
			b = Select(regs, rs2)
			c = BVAdd(a, b)
			regs_n = Store(regs, rd, c)
			return {'regs': regs_n}

		def x0_inv(state):
			m = state['memory']
			return conjunction(*[Equals(Select(m, BV(j, 9)), BV(0,2)) for j in range(16)])
		inv = [lambda state: Equals(state['wcnt'], BV(0, 5)), x0_inv]

		transactions = [Transaction(name=f"e2e_add", args=[rs1, rs2, rd], ret_args=[], semantics=semantics, proto=protocol)]

		super().__init__(transactions=transactions, arch_state={'regs': regs}, mapping=mapping, invariances=inv)

src = [os.path.join('serv', 'rtl', name + '.v') for name in ['serv_alu', 'ser_lt', 'ser_shift', 'ser_add', 'shift_reg', 'serv_bufreg', 'serv_csr', 'serv_ctrl', 'serv_decode', 'serv_mem_if', 'serv_top']]

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('serv_top', src, reset='i_rst', ignore_wires=False)
	spec = ServTop()

	print(f"Trying to proof {mod.name}")
	#print(mod)
	#ee = SMT2ProofEngine(outdir='smt2')
	ee = MCProofEngine(outdir="btor2")
	veri = Verifier(mod, spec, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
