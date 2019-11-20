#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class AdderSpec(Spec):
	def __init__(self, bits):
		args = {'spec_a': BVType(bits), 'spec_b': BVType(bits)}
		ret_args = {'spec_c': BVType(bits), 'spec_carry': BVType(1)}

		tt  = [Transition(inputs={'clr': BV(1,1)})]
		tt += [Transition(inputs={'clr': BV(0,1),
								  'a': BVExtract(Symbol('spec_a', BVType(bits)), ii, ii),
								  'b': BVExtract(Symbol('spec_b', BVType(bits)), ii, ii),},
						  outputs={'q': BVExtract(Symbol('spec_c', BVType(bits)), ii, ii)})
			   for ii in range(bits)]
		tt[-1].outputs['o_v'] = Symbol('spec_carry', BVType(1))
		a = Symbol('spec_a', BVType(bits))
		b = Symbol('spec_b', BVType(bits))
		semantics = {'spec_c': BVAdd(a, b), 'spec_carry': BVExtract(BVAdd(BVZExt(a, 1), BVZExt(b, 1)), bits, bits)}
		transactions = [Transaction(name=f"add{bits}", args=args, ret_args=ret_args, semantics=semantics, proto=Protocol(tt))]
		super().__init__(transactions=transactions)

add_v = os.path.join('fork', 'rtl', 'ser_add.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('ser_add', [add_v])
	spec = AdderSpec(8)
	prob = VerificationProblem(spec=spec, implementation='ser_add')

	#protocol_to_wavedrom_file("adder.json", spec.transactions[0].proto)

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
