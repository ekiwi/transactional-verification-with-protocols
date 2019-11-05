#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *


ptw_spec = Spec(transactions=[
	Transaction("Idle"),
])

src = [os.path.join('rtl', 'PTW.v')]

def main() -> int:
	mod = Module.load('PTW', src, reset=HighActiveReset('reset'), ignore_wires=False)
	prob = VerificationProblem(ptw_spec, "PTW")

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
