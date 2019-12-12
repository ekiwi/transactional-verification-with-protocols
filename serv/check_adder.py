#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class AdderSpec(Spec):
	def __init__(self, bits):
		args = {'a': BVType(bits), 'b': BVType(bits)}
		ret_args = {'c': BVType(bits), 'carry': BVType(1)}
		a,     b = [Symbol(f"ser_add.add{bits}.{name}", tpe) for name,tpe in args.items()]
		c, carry = [Symbol(f"ser_add.add{bits}.{name}", tpe) for name, tpe in ret_args.items()]


		tt  = [Transition(inputs={'clr': BV(1,1)})]
		tt += [Transition(inputs={'clr': BV(0,1),
								  'a': BVExtract(a, ii, ii),
								  'b': BVExtract(b, ii, ii),},
						  outputs={'q': BVExtract(c, ii, ii)})
			   for ii in range(bits)]
		tt[-1].outputs['o_v'] = carry
		semantics = {'c': BVAdd(a, b), 'carry': BVExtract(BVAdd(BVZExt(a, 1), BVZExt(b, 1)), bits, bits)}
		transactions = [Transaction(name=f"add{bits}", args=args, ret_args=ret_args, semantics=semantics, proto=LegacyProtocol(tt))]
		super().__init__(transactions=transactions, idle=None)

add_v = os.path.join('fork', 'rtl', 'ser_add.v')

def main() -> int:
	version = require_yosys()
	print(f"Using yosys {version}")

	mod = Module.load('ser_add', [add_v])
	spec = AdderSpec(32)
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
