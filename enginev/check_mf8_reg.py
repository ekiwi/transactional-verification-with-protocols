#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from enginev.common import *

class RegfileSpec(Spec):
	def __init__(self):
		# 32 8-bit registers
		regs = ArrayType(BVType(5), BVType(8))
		z = BVType(16)

		# two read port memory by writing to two single port memories
		def mapping(mod: Module, regs, z):
			return [Equals(regs, mod[mem]) for mem in ['RAMD', 'RAMR']] + [Equals(z, mod['Z'])]

		# transaction arguments (in/out)
		rd_addr = Symbol('rd_addr', BVType(5))
		rd_data = Symbol('rd_data', BVType(8))
		rr_addr = Symbol('rr_addr', BVType(5))
		rr_data = Symbol('rr_data', BVType(8))
		write_en = Symbol('write_en')
		write_data = Symbol('write_data', BVType(8))
		z_reg = Symbol('z_reg', BVType(16))

		args = [rd_addr, rr_addr, write_en, write_data]
		ret_args = [rd_data, rr_data, z_reg]

		first_cycle = Map('Rd_Addr', rd_addr) | Map('Rr_Addr', rr_addr)
		second_cycle = Map('Wr', write_en) | Map('Data_In', write_data) | Map('Rd_Data', rd_data) | Map('Rr_Data', rr_data)
		protocol = first_cycle + second_cycle

		def semantics(rd_addr, rr_addr, write_en, write_data, regs, z):
			regs_n = Ite(write_en, Store(regs, rd_addr, write_data), regs)
			rd_data = Select(regs_n, rd_addr)
			rr_data = Select(regs_n, rr_addr)
			write_z_lsb = And(write_en, Equals(rd_addr, BV(30, 5)))
			write_z_msb = And(write_en, Equals(rd_addr, BV(31, 5)))
			z_n = Ite(write_z_lsb,
					  BVConcat(BVExtract(z, 8, 15), write_data),
				  Ite(write_z_msb,
					  BVConcat(write_data, BVExtract(z, 0, 7)),
					  z))
			return {'regs': regs_n, 'z': z_n, 'rd_data': rd_data, 'rr_data': rr_data, 'z_reg': z_n}

		idle = Transaction(name="idle", semantics=lambda regs, z: {'regs': regs, 'z': z}, proto=Map('Wr', Bool(False)))

		transactions = [idle, Transaction(name="rw", args=args, ret_args=ret_args, semantics=semantics, proto=protocol)]

		# TODO: invariances
		inv = []
		super().__init__(arch_state={'regs': regs, 'z': z}, mapping=mapping, transactions=transactions, invariances=inv)

def main() -> int:
	mod = Module.load('mf8_reg', sources, reset=LowActiveReset('Reset'))
	spec = RegfileSpec()

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
