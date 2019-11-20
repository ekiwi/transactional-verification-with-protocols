#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from functools import reduce
from collections import defaultdict
from pysmt.shortcuts import *
from transactions import *
from serv.check_regfile import regfile_spec
from serv.check_alu import alu_spec

regs = Symbol('regs', ArrayType(BVType(5), BVType(32)))

# build instruction
funct7 = BV(0, 7)
rs2 = Symbol('rs2', BVType(5))
rs1 = Symbol('rs1', BVType(5))
funct3 = BV(0, 3)
rd = Symbol('rd', BVType(5))
opcode = BV(0b0110011, 7)


instruction = cat(funct7, rs2, rs1, funct3, rd, opcode)

# toplevel spec

# we assume that no interrupt or data bus transaction will be incoming
always = { 'i_timer_irq': BV(0, 1), 'i_dbus_ack': BV(0,1) }
protocol = Protocol(
	[Transition(inputs={'i_ibus_rdt': instruction, 'i_ibus_ack': BV(1,1), **always}, outputs={'o_ibus_cyc': BV(1,1)})] +
	[Transition(inputs={'i_ibus_ack': BV(0,1), **always}, outputs={'o_ibus_cyc': BV(0,1)})] * 34 +
	[Transition(inputs={'i_ibus_ack': BV(0,1), **always}, outputs={'o_ibus_cyc': BV(1,1)})]
)

# semantics of the add instruction
a = Ite(Equals(rs1, BV(0, 5)), BV(0, 32), Select(regs, rs1))
b = Ite(Equals(rs2, BV(0, 5)), BV(0, 32), Select(regs, rs2))
c = BVAdd(a, b)
regs_n = Ite(Equals(rd, BV(0, 5)), regs, Store(regs, rd, c))
semantics = {'regs': regs_n}

serv_spec = Spec(state={'regs': regs.symbol_type()}, transactions=[
	Transaction("Add", args={'rs1': BVType(5), 'rs2': BVType(5), 'rd': BVType(5)}, semantics=semantics, proto=protocol),
	Transaction("Idle", proto=Protocol([Transition(inputs={'i_ibus_ack': BV(0,1), **always})]))
])

# common invariances
other_inv = [
	Equals(Symbol('decode.state', BVType(2)), BV(0, 2)),
	Equals(Symbol('decode.cnt', BVType(5)), BV(0, 5)),
	Equals(Symbol('decode.pending_irq', BVType(1)), BV(0,1)),
	Equals(Symbol('decode.stage_one_done', BVType(1)), BV(0,1)),
	Equals(Symbol('decode.o_ctrl_jump', BVType(1)), BV(0,1)),
	Equals(Symbol('decode.o_cnt_r', BVType(4)), BV(1, 4)),
	Equals(Symbol('ctrl.en_pc_r', BVType(1)), BV(1,1)),
]

# experiment to see what happens if we give it a single instruction
memory = Symbol('regfile.memory', ArrayType(BVType(9), BVType(2)))
regfile_inv = [
	conjunction(*[Equals(Select(memory, BV(j, 9)), BV(0,2)) for j in range(16)]),
	Equals(Symbol('regfile.o_ready', BVType(1)), BV(0,1)),
	Equals(Symbol('regfile.t', BVType(1)), BV(0,1)),
	Equals(Symbol('regfile.wcnt', BVType(5)), BV(0,5)),
]
e2e_mappings = [
	StateMapping(
		arch=Select(regs, BV(ii, 5)),
		impl=reduce(BVConcat, (Select(memory, BV(ii * 16 + jj, 9)) for jj in reversed(range(16))))
	)
for ii in range(1, 32) ]

no_abstraction_check = VerificationProblem(
	spec=serv_spec,
	implementation='serv_top',
	invariances=regfile_inv + other_inv,
	mappings=e2e_mappings
)

# the other possibility is to replace the alu and the regfile with their spec when checking
abs_mappings = [StateMapping(arch=regs, impl=Symbol('regfile.regs', regs.symbol_type()))]
abstract_refile_and_alu_check = VerificationProblem(
	spec=serv_spec,
	implementation='serv_top',
	invariances=other_inv,
	mappings=abs_mappings,
	submodules={'regfile': regfile_spec, 'alu': alu_spec}
)

src = [os.path.join('fork', 'rtl', name + '.v') for name in ['serv_alu', 'ser_lt', 'ser_shift', 'ser_add', 'shift_reg', 'serv_bufreg', 'serv_csr', 'serv_ctrl', 'serv_decode', 'serv_regfile', 'serv_mem_if', 'serv_top']]


def generate_wavedro():
	protocol_to_wavedrom_file("serv_add.json", serv_spec.transactions[0].proto)
	import json
	alu_idle, alu_add = alu_spec.transactions[-1], alu_spec.transactions[0]
	tt = trace_to_wavedrom([alu_idle, alu_idle, alu_add, alu_idle])
	with open('alu_trace.json', 'w') as ff:
		json.dump(tt, ff, indent=2)

	reg_idle, reg_rw = regfile_spec.transactions[0], regfile_spec.transactions[-1]
	traces = {'alu': [alu_idle, alu_idle, alu_add, alu_idle], 'regfile': [reg_rw, reg_idle]}
	serv_add = serv_spec.transactions[0]
	tt = composition_to_wavedrom('serv', serv_add, traces)
	with open('serv_trace.json', 'w') as ff:
		json.dump(tt, ff, indent=2)

def main() -> int:

	# select verification problem
	#prob = no_abstraction_check
	prob = abstract_refile_and_alu_check


	# select proof engine
	ee = SMT2ProofEngine(outdir='../smt2')
	# ee = MCProofEngine(outdir="../btor2")

	#
	mod = Module.load(prob.implementation, src,
					  ignore_wires=False,
					  blackbox=list(prob.submodules.keys()))
	print(f"Trying to proof {mod.name}")
	veri = Verifier(mod, prob, ee)
	veri.proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
