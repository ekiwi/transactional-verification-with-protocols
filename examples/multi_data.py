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
	done = Transition(inputs={'start': BV(0, 1)}, outputs={'out': data_out})
	# delay length depends on input data
	guard = Equals(BVExtract(data_in, start=0, end=1), BV(delay,2))
	return Protocol([start] + [idle] * delay + [done], guard=guard)

semantics = { 'data_out': data_in }
args={'data_in': BVType(32)}
ret_args={'data_out': BVType(32)}

spec = Spec(
	transactions=[Transaction("Idle", proto=[Protocol([idle])]),
	Transaction(f"Delay", proto=[protocol(delay=ii)  for ii in range(4)],
				semantics=semantics, args=args, ret_args=ret_args)
	 ]
)

invariances = [
	Equals(Symbol('running', BVType(1)), BV(0,1)),
]
mappings = []

def main() -> int:
	for pp in spec.transactions[1].proto:
		protocol_constraints(pp)


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
