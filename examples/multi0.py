#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
from functools import reduce


data_in = Symbol('data_in', BVType(32))
data_out = Symbol('data_out', BVType(32))

idle =  Transition(inputs={'start': BV(0,1)}, outputs={'done': BV(0,1)})
def protocol(delay=0):
	start = Transition(inputs={'start': BV(1,1), 'in': data_in}, outputs={'done': BV(0,1)})
	done = Transition(inputs={'start': BV(0, 1)}, outputs={'done': BV(1, 1), 'out': data_out})
	return Protocol([start] + [idle] * delay + [done])

semantics = { 'data_out': data_in }

spec = Spec(
	transactions=[
		Transaction("Idle", proto=Protocol([idle])),
		Transaction("Delay1", proto=protocol(delay=1), semantics=semantics,	args={'data_in': BVType(32)}, ret_args={'data_out': BVType(32)}
		)
	]
)

invariances = [
	Equals(Symbol('running', BVType(1)), BV(0,1)),
	# TODO: remove
	Equals(Symbol('delay', BVType(4)), BV(1,4))
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
