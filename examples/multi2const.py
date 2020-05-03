#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from pysmt.shortcuts import Symbol, BVType, Equals, BV
from transactions import *
from examples.multi0 import spec as multi0_spec

toplevel = 'multi2const'
src = ['multi0.v', 'multi2const.v']
mod = Module.load(toplevel, src)

data_in = Symbol('multi2const.Delay.dat_in', BVType(64))
data_out = Symbol('multi2const.Delay.dat_out', BVType(64))

##############################
p = ProtocolBuilder(mod)
p['start'] = 1
p['inp'] = data_in
p.step()

p['start'] = 0
p['inp'] = DontCare
for _ in range(3):
	p.step()

p['out'].expect(data_out)
##############################

protocol = p.finish()
semantics = { 'dat_out': data_in }
args={'dat_in': BVType(64)}
ret_args={'dat_out': BVType(64)}

spec = Spec(
	transactions=[Transaction(f"Delay", proto=protocol, semantics=semantics, args=args, ret_args=ret_args)],
	idle=ProtocolBuilder(mod).inputs(start=0).finish()
)

invariances = [
# TODO: currently the way all of this is implemented, we do not need any invariances
#	Equals(Symbol('running', BVType(1)), BV(0,1)),
#	Equals(Symbol('lsb_unit.running', BVType(1)), BV(0,1)),
#	Equals(Symbol('msb_unit.running', BVType(1)), BV(0,1)),
]

no_abstraction_check = VerificationProblem(
	spec=spec, implementation='multi2const', invariances=invariances, mappings=[])

abstracted_check = VerificationProblem(
	spec=spec, implementation='multi2const', invariances=[], mappings=[],
	submodules={'lsb_unit': multi0_spec, 'msb_unit': multi0_spec})

# currently we need to tell the Module.load command which submodules to blackbox
abs_mod = Module.load(toplevel, src, blackbox=list(abstracted_check.submodules.keys()))

def main() -> int:

	ee = SMT2ProofEngine(outdir='../smt2', simplify=True)
	#ee = MCProofEngine(outdir="../btor2")

	#print("Verifying flattened implementation")
	#Verifier(mod, no_abstraction_check, ee).proof_all()

	print("Verifying implementation with submodules replaced by their spec")
	Verifier(abs_mod, abstracted_check, ee).proof_all()
	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
