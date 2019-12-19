#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import Symbol, BVType, Equals, BV
from transactions import *
from functools import reduce

mod = Module.load('multi0keep', ['multi0keep.v'])

data_in = Symbol('multi0keep.Delay.data_in', BVType(32))
data_out = Symbol('multi0keep.Delay.data_out', BVType(32))
data = Symbol('multi0keep.data', BVType(32))

##############################
p = ProtocolBuilder(mod)
p['start'] = 1
p['inp'] = data_in
p['done'].expect(0)
p.step()

p['start'] = 0
p['inp'] = DontCare

p['done'].wait(1, max=3)
# while p['done'] != 1:
#   p.step()
#
p['out'].expect(data_out)
##############################

protocol = p.finish()
semantics = { 'data_out': data_in, 'data': data_in }
args={'data_in': BVType(32)}
ret_args={'data_out': BVType(32)}

read_protocol = ProtocolBuilder(mod).inputs(start=0).outputs(done=0, out=Symbol('multi0keep.Read.data_out', BVType(32))).finish()

spec = Spec(state={'data': BVType(32)}, transactions=[
	Transaction(f"Delay", proto=protocol, semantics=semantics, args=args, ret_args=ret_args),
	Transaction(f"Read", proto=read_protocol, semantics={'data_out': data}, args={}, ret_args=ret_args)]
)

invariances = [
	Equals(Symbol('running', BVType(1)), BV(0,1)),
]
mappings = [StateMapping(data, Symbol('buffer', BVType(32)))]

def main() -> int:
	prob = VerificationProblem(spec=spec, implementation='multi0keep',
							   invariances=invariances, mappings=mappings)

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	Verifier(mod, prob, ee).proof_all()
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
