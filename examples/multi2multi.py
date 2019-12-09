#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import Symbol, BVType, Equals, BV
from transactions import *
from functools import reduce

mod = Module.load('multi2multi', ['multi0.v', 'multi2multi.v'])

data_in = Symbol('data_in', BVType(64))
data_out = Symbol('data_out', BVType(64))

##############################
p = ProtocolBuilder(mod)
p['start'] = 1
p['inp'] = data_in
p['done'].expect(0)
p.step()

p['start'] = 0
p['inp'] = DontCare

p['done'].wait(1, max=4)
p['out'].expect(data_out)
##############################

protocol = p.finish()
semantics = { 'data_out': data_in }
args={'data_in': BVType(64)}
ret_args={'data_out': BVType(64)}

spec = Spec(
	transactions=[Transaction(f"Delay", proto=protocol, semantics=semantics, args=args, ret_args=ret_args)],
	idle=ProtocolBuilder(mod).inputs(start=0).outputs(done=0).finish()
)

invariances = [
	Equals(Symbol('both_running', BVType(1)), BV(0,1)),
	Equals(Symbol('lsb_unit.running', BVType(1)), BV(0,1)),
	Equals(Symbol('msb_unit.running', BVType(1)), BV(0,1)),
]
mappings = []

def main() -> int:
	prob = VerificationProblem(spec=spec, implementation='multi2multi',
							   invariances=invariances, mappings=mappings)

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	Verifier(mod, prob, ee).proof_all()
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
