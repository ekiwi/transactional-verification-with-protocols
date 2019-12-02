#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *
from functools import reduce

regs = Symbol('regs', ArrayType(BVType(5), BVType(32)))
memory = Symbol('memory', ArrayType(BVType(9), BVType(2)))
rs1_addr = Symbol('rs1_addr', BVType(5))
rs2_addr = Symbol('rs2_addr', BVType(5))
rd_enable = Symbol('rd_enable', BVType(1))
rd_addr = Symbol('rd_addr', BVType(5))
rd_data = Symbol('rd_data', BVType(32))
rs1_data = Symbol('rs1_data', BVType(32))
rs2_data = Symbol('rs2_data', BVType(32))

protocol = LegacyProtocol(
	[Transition(inputs={'i_go': BV(1,1), 'i_rd_en': BV(0,1)}, outputs={'o_ready': BV(0,1)})] +
	[Transition(inputs={'i_go': BV(0,1), 'i_rd_en': BV(0,1),
						'i_rs1_addr': rs1_addr, 'i_rs2_addr': rs2_addr},
				outputs={'o_ready': BV(0,1)})] +
	[Transition(inputs={'i_go': BV(0,1), 'i_rd_en': BV(0,1),
						'i_rs1_addr': rs1_addr, 'i_rs2_addr': rs2_addr},
				outputs={'o_ready': BV(1,1)})] +
	[Transition(inputs={'i_go': BV(0,1), 'i_rd_en': rd_enable,
						'i_rs1_addr': rs1_addr, 'i_rs2_addr': rs2_addr, 'i_rd_addr': rd_addr,
						'i_rd': BVExtract(rd_data, ii, ii)},
				outputs={'o_ready': BV(0,1),
						 'o_rs1': BVExtract(rs1_data, ii, ii),
						 'o_rs2': BVExtract(rs2_data, ii, ii)})
	 for ii in range(32)]
)


is_zero = lambda expr: Equals(expr, BV(0, expr.bv_width()))
do_write = And(Equals(rd_enable, BV(1,1)), Not(Equals(rd_addr, BV(0, 5))))
semantics = {
	'rs1_data': Ite(is_zero(rs1_addr), BV(0, 32), Select(regs, rs1_addr)),
	'rs2_data': Ite(is_zero(rs2_addr), BV(0, 32), Select(regs, rs2_addr)),
	'regs': Ite(do_write, Store(regs, rd_addr, rd_data), regs)
}

regfile_spec = Spec(
	state = {'regs': ArrayType(BVType(5), BVType(32))},
	transactions=[
		Transaction("RW", proto=protocol, semantics=semantics,
					args={'rs1_addr': BVType(5), 'rs2_addr': BVType(5), 'rd_addr': BVType(5),
						  'rd_enable': BVType(1), 'rd_data': BVType(32)},
					ret_args={'rs1_data': BVType(32), 'rs2_data': BVType(32)}
		)
	],
	idle=LegacyProtocol([Transition(
			inputs={'i_go': BV(0,1), 'i_rd_en': BV(0,1)},
			outputs={'o_ready': BV(0,1)} # cool test: comment out this line and the invariance that decode.state == 0 won't hold when verifying serv-top
		)])
)

invariances = [
	conjunction(*[Equals(Select(Symbol('memory', ArrayType(BVType(9), BVType(2))), BV(j, 9)), BV(0,2)) for j in range(16)]),
	Equals(Symbol('o_ready', BVType(1)), BV(0,1)),
	Equals(Symbol('t', BVType(1)), BV(0,1)),
	Equals(Symbol('wcnt', BVType(5)), BV(0,5))
]

mappings = [
	StateMapping(
		arch=Select(regs, BV(ii, 5)),
		impl=reduce(BVConcat, (Select(memory, BV(ii * 16 + jj, 9)) for jj in reversed(range(16))))
	)
for ii in range(1, 32) ]


regfile_v = os.path.join('fork', 'rtl', 'serv_regfile.v')

def main() -> int:
	version = require_yosys()

	#protocol_to_wavedrom_file("regfile_rw.json", regfile_spec.transactions[1].proto)

	prob = VerificationProblem(spec=regfile_spec, implementation='serv_regfile',
							   invariances=invariances, mappings=mappings)
	mod = Module.load('serv_regfile', [regfile_v])

	#ee = SMT2ProofEngine(outdir='../smt2')
	ee = MCProofEngine(outdir="../btor2")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
