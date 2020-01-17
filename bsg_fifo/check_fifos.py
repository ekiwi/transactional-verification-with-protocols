#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Mostly copied from ../mann/check_fifos.py"""

import math
import time
from pysmt.shortcuts import *
from transactions import *

NAMES = ("bsg_two_fifo")

def load(name: str, fixed: bool, depth=8, width=32):
	# assert name in NAMES
	ff = "_fixed" if fixed else ""
	src = [
		f'{name}{ff}.v',
		'bsg_defines.v',
		'bsg_dff_en.v',
		'bsg_mem_1r1w.v',
		'bsg_mem_1r1w_synth.v',
	]
	if name == "bsg_two_fifo":
		assert depth == 2, "bsg_two_fifo must have depth 2"
		return Module.load(name, src, params={'width_p': width, 'allow_enq_deq_on_full_p': 1})
	else:
		raise NotImplementedError()


def verification_problem(dut: Module, depth=8, width=32) -> VerificationProblem:
	# architectural state: memory to store values + count to keep track of how many values are valid
	addr_bits = int(math.log2(depth))
	assert depth == 2**addr_bits, f"Only power of two depths are supported, not: {depth}"
	mem = Symbol(f'{dut.name}.mem', ArrayType(BVType(addr_bits), BVType(width)))
	count = Symbol(f'{dut.name}.count', BVType(addr_bits+1))
	read = Symbol(f'{dut.name}.read', BVType(addr_bits))

	state = {'mem': mem.symbol_type(), 'count': count.symbol_type(), 'read': read.symbol_type()}

	not_full = BVULT(count, BV(depth,addr_bits+1))
	empty = Equals(count, BV(0, addr_bits+1))

	# push
	push_data = Symbol(f'{dut.name}.Push.push_data', BVType(width))
	read_plus_count = BVAdd(read, BVExtract(count, start=0, end=addr_bits-1))
	push_sem = {
		'mem': Store(mem, read_plus_count, push_data), # mem[read + count] := push_data
		'count': BVAdd(count, BV(1,addr_bits+1))       # count := count + 1
	}
	push_proto = ProtocolBuilder(dut).inputs(v_i=1, yumi_i=0, data_i=push_data).outputs(full_o=0).finish()

	# pop
	pop_data = Symbol(f'{dut.name}.Pop.pop_data', BVType(width))
	pop_sem = {
		'pop_data': Select(mem, read),             # pop_data := mem[read]
		'count': BVSub(count, BV(1, addr_bits+1)), # count := count - 1
		'read': BVAdd(read, BV(1, addr_bits)),     # read := read + 1
	}
	pop_proto = ProtocolBuilder(dut).inputs(yumi_i=1, v_i=0).outputs(empty_o=0, data_o=pop_data).finish()

	# push pop
	pushpop_in = Symbol(f'{dut.name}.PushPop.in', BVType(width))
	pushpop_out = Symbol(f'{dut.name}.PushPop.out', BVType(width))
	pushpop_sem = {
		'out': Ite(empty, pushpop_in, Select(mem, read)), # out = empty? in : mem[read] # but actually empty is always false!
		'mem': Store(mem, read_plus_count, pushpop_in),   # mem[read + count] := in
		'read': BVAdd(read, BV(1, addr_bits)),            # read := read + 1
	}
	pushpop_proto = ProtocolBuilder(dut).inputs(yumi_i=1, v_i=1, data_i=pushpop_in).outputs(data_o=pushpop_out, empty_o=0).finish()

	# Idle
	idle_proto = ProtocolBuilder(dut).inputs(yumi_i=0, v_i=0).outputs().finish()

	sp = Spec(state=state,
		transactions=[
			Transaction("Idle", idle_proto),
			Transaction("Push", push_proto, push_sem, args={'push_data': BVType(width)}, guard=not_full),
			Transaction("Pop", pop_proto, pop_sem, ret_args={'pop_data': BVType(width)}, guard=Not(empty)),
			Transaction("PushPop", pushpop_proto, pushpop_sem, args={'in': BVType(width)}, ret_args={'out': BVType(width)},
						guard=And(Not(empty), TRUE())),
						# see the shift_register_top.v source code: assume(!(empty & pop)), assume(!(full & push))
						# the shift register cannot be transparent :(, however, PushPop actually works on a full FIFO!
		],
	)

	if dut.name.startswith('bsg_two'):
		mappings = [
			StateMapping(Select(mem, BVZero(width)), Symbol("dff.data_r", width))
		]
		invariances = [
		]
	else:
		raise NotImplementedError()
	return VerificationProblem(spec=sp, implementation=dut.name, invariances=invariances, mappings=mappings)


def verify(name: str, fixed: bool, ee, depth: int, width: int):
	ff = " (fixed)" if fixed else ""
	print(f"Verifying {name}{ff} for DEPTH={depth}, WIDTH={width}")

	start = time.time()
	mod = load(name, fixed, depth, width)
	load_time = time.time() - start
	print(f"- {load_time:.3f} sec to load and parse verilog sources")

	start = time.time()
	prob = verification_problem(mod, depth=depth, width=width)
	prob_time = time.time() - start
	print(f"- {prob_time:.3f} to create the verification problem")

	start = time.time()
	if fixed:
		Verifier(mod, prob, ee).proof_all()
	else:
		try:
			Verifier(mod, prob, ee).proof_all()
		except AssertionError:
			pass
	verif_time = time.time() - start
	print(f"- {verif_time:.3f} (end-to-end) to run the verification")

	# ugly part of using PySMT
	reset_env()
	print()


def main() -> int:

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")

	# duts = NAMES
	width = 32
	# for depth in [8, 16, 32, 64, 128]:
	# for name in duts:
	for fixed in [False, True]:
		verify('bsg_two_fifo', fixed, ee, depth=2, width=width)

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())

