#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
import math

# TODO: what is the best way of modeling this FIFO?


def gen_spec(data_width: int, depth: int, e: int = 0) -> Spec:
	data_t = BVType(data_width)
	addr_bits = int(math.ceil(math.log2(depth)))
	mem_t = ArrayType(BVType(addr_bits), data_t)
	mem = Symbol('mem', mem_t)

	push = Transaction("Push", args={'data': data_t},
   		proto=Protocol([Transition(inputs={'push': BV(1,1), 'data_in': Symbol('data', data_t)}, outputs={'full': BV(0,1)})]),
		semantics={'mem': }
	)

	spec = Spec(

	)




def load_implementation(data_width: int, depth: int, e: int = 0) -> Module:
	src = ['tacas2020/shift_register_fifo.v']


def main() -> int:
	mod = load_implementation(data_width=32, depth=8)
	prob = VerificationProblem(spec=gen_spec(data_width=32, depth=8), implementation='shift_register_fifo')

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
