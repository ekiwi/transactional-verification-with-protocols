#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class AdderSpec(Spec):
	def __init__(self, bits):
		a = Symbol('spec_a', BVType(bits))
		b = Symbol('spec_b', BVType(bits))
		c = Symbol('spec_c', BVType(bits))
		carry = Symbol('spec_carry', BVType(1))
		protocol = Map('clr', Bool(True)) + (BitSerial('a', a) | BitSerial('b', b) | BitSerial('q', c) |
											 Repeat('clr', Bool(False), bits))
		protocol.mappings[-1]['o_v'] = carry

		def semantics(spec_a, spec_b):
			c = BVAdd(spec_a, spec_b)
			carry = BVExtract(BVAdd(BVZExt(spec_a, 1), BVZExt(spec_b, 1)), bits, bits)
			return {'spec_c': c, 'spec_carry': carry}

		transactions = [Transaction(name=f"add{bits}", args=[a,b], ret_args=[c,carry], semantics=semantics, proto=protocol)]

		super().__init__(transactions=transactions)

add_v = os.path.join('serv', 'rtl', 'ser_add.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('ser_add', [add_v], reset='rst')
	spec = AdderSpec(32)

	reset_env()
	print(f"Trying to proof {mod.name}")
	#print(mod)
	#solver = Solver(mod.smt2_src)
	#engine = ProofEngine(mod=mod,spec=spec, solver=solver, outdir="smt2")
	ee = MCProofEngine(outdir="btor2")
	veri = Verifier(mod, spec, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
