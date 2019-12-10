#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
from functools import reduce

mod = Module.load('multi_data', ['multi_data.v'])


data_in = Symbol('multi_data.Delay.data_in', BVType(32))
data_out = Symbol('multi_data.Delay.data_out', BVType(32))

##############################
p = ProtocolBuilder(mod)
p['start'] = 1
p['inp'] = data_in
p['done'].expect(0)
p.step()

p['start'] = 0
p['inp'] = DontCare

# TODO: Data dependent delays will NOT be supported in the CAV'20 version.
#       For now we need to fall back to non deterministic modelling.
#p.step(BVExtract(data_in, 1, 0))
p['done'].wait(1, max=4)
p['out'].expect(data_out)
##############################

protocol = p.finish()
semantics = { 'data_out': data_in }
args={'data_in': BVType(32)}
ret_args={'data_out': BVType(32)}

spec = Spec(
	transactions=[Transaction(f"Delay", proto=protocol, semantics=semantics, args=args, ret_args=ret_args)],
	idle=LegacyProtocol([Transition(inputs={'start': BV(0,1)}, outputs={'done': BV(0,1)})]),
)


invariances = [
	Equals(Symbol('running', BVType(1)), BV(0,1)),
]
mappings = []

def main() -> int:

	prob = VerificationProblem(spec=spec, implementation='multi_data',
							   invariances=invariances, mappings=mappings)


	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
