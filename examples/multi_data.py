#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
from functools import reduce


data_in = Symbol('data_in', BVType(32))
data_out = Symbol('data_out', BVType(32))

##############################
p = ProtocolBuilder()
p.start = 1
p.inp = data_in
p.done.expect(0)
p.step()

p.start = 0
p.inp = DontCare

p.step(BVExtract(data_in, 1, 0))
p.out.expect(data_out)
##############################

protocol = p.finish()
semantics = { 'data_out': data_in }
args={'data_in': BVType(32)}
ret_args={'data_out': BVType(32)}

spec = Spec(
	transactions=[Transaction(f"Delay", proto=protocol, semantics=semantics, args=args, ret_args=ret_args)],
	idle=Transition(inputs={'start': BV(0,1)}, outputs={'done': BV(0,1)}),
)


invariances = [
	Equals(Symbol('running', BVType(1)), BV(0,1)),
]
mappings = []

def main() -> int:

	prob = VerificationProblem(spec=spec, implementation='multi0',
							   invariances=invariances, mappings=mappings)
	mod = Module.load('multi0', ['multi0.v'])

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
