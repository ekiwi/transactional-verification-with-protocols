#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from functools import reduce
from pysmt.shortcuts import *
from transactions import *

# experiment to see what happens if we give it a single instruction

class ServTop(Spec):
	def __init__(self):

		########## Architectural State: register file
		regs = ArrayType(BVType(5), BVType(32))  # ArraySignal('x', 5, 32)
		map_regs_to_mem = True
		def mapping(mod: Module, regs):
			asserts = []
			memory = mod['regfile.memory']
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
		rs2 = Symbol('spec_rs2', BVType(5))
		rs1 = Symbol('spec_rs1', BVType(5))
		funct3 = BV(0, 3)
		rd = Symbol('spec_rd', BVType(5))
		opcode = BV(0b0110011, 7)

		instruction = cat(funct7, rs2, rs1, funct3, rd, opcode)

		# protocol
		first_cycle = Map('i_ibus_rdt', instruction) | Map('i_ibus_ack', Bool(True)) | Map('o_ibus_cyc', Bool(True))
		middle = Map('i_ibus_ack', Bool(False)) | Map('o_ibus_cyc', Bool(False))
		last_cycle = Map('i_ibus_ack', Bool(False)) | Map('o_ibus_cyc', Bool(True))
		always = Map('i_timer_irq', Bool(False)) | Map('i_dbus_ack', Bool(False))

		protocol = (first_cycle + (middle * 34) + last_cycle) | (always * 36)
		assert len(protocol) == 36


		def semantics(spec_rs1, spec_rs2, spec_rd, regs):
			a = Ite(Equals(spec_rs1, BV(0, 5)), BV(0,32), Select(regs, spec_rs1))
			b = Ite(Equals(spec_rs2, BV(0, 5)), BV(0,32), Select(regs, spec_rs2))
			c = BVAdd(a, b)
			regs_n = Ite(Equals(spec_rd, BV(0, 5)), regs, Store(regs, spec_rd, c))
			return {'regs': regs_n}

		def x0_inv(state):
			m = state['regfile.memory']
			return conjunction(*[Equals(Select(m, BV(j, 9)), BV(0,2)) for j in range(16)])
		inv = [
			lambda state: Iff(state['regfile.o_ready'], Bool(False)),
			lambda state: Iff(state['regfile.t'],Bool(False)),
			lambda state: Equals(state['decode.state'], BV(0, 2)),
			lambda state: Equals(state['decode.cnt'], BV(0, 5)),
			lambda state: Iff(state['decode.pending_irq'], Bool(False)),
			lambda state: Iff(state['decode.stage_one_done'], Bool(False)),
			lambda state: Iff(state['decode.o_ctrl_jump'], Bool(False)),
			lambda state: Equals(state['decode.o_cnt_r'], BV(1, 4)),
			lambda state: Iff(state['ctrl.en_pc_r'], Bool(True)),
			lambda state: Equals(state['regfile.wcnt'], BV(0, 5)),
			x0_inv]

		transactions = [Transaction(name=f"e2e_add", args=[rs1, rs2, rd], ret_args=[], semantics=semantics, proto=protocol)]

		super().__init__(transactions=transactions, arch_state={'regs': regs}, mapping=mapping, invariances=inv)

src = [os.path.join('serv', 'rtl', name + '.v') for name in ['serv_alu', 'ser_lt', 'ser_shift', 'ser_add', 'shift_reg', 'serv_bufreg', 'serv_csr', 'serv_ctrl', 'serv_decode', 'serv_regfile', 'serv_mem_if', 'serv_top']]

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
