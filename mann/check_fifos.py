#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import time

from pysmt.shortcuts import *
from transactions import *
import math

def load(name: str, fixed: bool, depth=8, width=32):
	assert name in {'shift_register_fifo', 'circular_pointer_fifo'}
	ff = "_fixed" if fixed else ""
	src = [f'tacas2020/{name}{ff}.v', 'tacas2020/FF.v']
	return Module.load(name, src, params={'WIDTH': width, 'DEPTH': depth})

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
	push_proto = ProtocolBuilder(dut).inputs(push=1, pop=0, data_in=push_data).outputs(full=0).finish()

	# pop
	pop_data = Symbol(f'{dut.name}.Pop.pop_data', BVType(width))
	pop_sem = {
		'pop_data': Select(mem, read),             # pop_data := mem[read]
		'count': BVSub(count, BV(1, addr_bits+1)), # count := count - 1
		'read': BVAdd(read, BV(1, addr_bits)),     # read := read + 1
	}
	pop_proto = ProtocolBuilder(dut).inputs(pop=1, push=0).outputs(empty=0, data_out=pop_data).finish()

	# push pop
	pushpop_in = Symbol(f'{dut.name}.PushPop.in', BVType(width))
	pushpop_out = Symbol(f'{dut.name}.PushPop.out', BVType(width))
	pushpop_sem = {
		'out': Ite(empty, pushpop_in, Select(mem, read)), # out = empty? in : mem[read] # but actually empty is always false!
		'mem': Store(mem, read_plus_count, pushpop_in),   # mem[read + count] := in
		'read': BVAdd(read, BV(1, addr_bits)),            # read := read + 1
	}
	pushpop_proto = ProtocolBuilder(dut).inputs(pop=1, push=1, data_in=pushpop_in).outputs(data_out=pushpop_out, empty=0).finish()

	# Idle
	idle_proto = ProtocolBuilder(dut).inputs(pop=0, push=0).outputs().finish()

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

	if dut.name.startswith('shift'):
		mappings = [StateMapping(count, Symbol('count', BVType(addr_bits+1)))] + [
			StateMapping(
				Select(mem, BVAdd(read, BV(ii, addr_bits))), Symbol(f'regs[{ii}].reg_inst.Q', BVType(width)),
				guard=BVUGT(count, BV(ii, addr_bits+1)))
			for ii in range(depth)
		]

		invariances = [
			BVULT(Symbol('count', BVType(addr_bits+1)), BV(depth+1, addr_bits+1))
		]
	else:
		assert dut.name.startswith('circular')
		rdPtr = Symbol('ff_rdPtr.Q', BVType(addr_bits + 1))
		wrPtr = Symbol('ff_wrPtr.Q', BVType(addr_bits + 1))
		cnt   = Symbol('cnt', BVType(addr_bits+1))

		mappings = [
			StateMapping(count, cnt),
			StateMapping(read, BVExtract(rdPtr, start=0, end=addr_bits-1)),
			# this might be more performant (definitely easier to write), but results in harder to read CEXs
		    #StateMapping(mem, Symbol('entries', mem.symbol_type()))
		] + [
			# easier to read CEX
			StateMapping(Select(mem, BV(ii, addr_bits)), Select(Symbol('entries', mem.symbol_type()), BV(ii, addr_bits))) for ii in range(depth)
		]


		invariances = [
			BVULT(cnt, BV(depth+1, addr_bits+1)),
			BVULT(rdPtr, BV(depth, addr_bits + 1)),
			BVULT(wrPtr, BV(depth, addr_bits + 1)),
			# more complicated invariance because wrPtr, rdPtr and cnt together contain redundant information
			# if(cnt ==0): assert(rdPtr == wrPtr)
			# elif(wrPtr > rPtr): assert(cnt == wrPtr - rdPtr)
			# else:               assert(cnt == depth + wrPtr - rdPtr)
			Ite(Equals(cnt, BV(0, addr_bits+1)), Equals(rdPtr, wrPtr), Equals(cnt,
				Ite(BVUGT(wrPtr, rdPtr), BVSub(wrPtr, rdPtr),
					BVAdd(BV(depth, addr_bits+1), BVSub(wrPtr, rdPtr)))))
		]


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

	verify('shift_register_fifo', True, ee, 8, 8)

	print("Skipping benchmark")
	return 0

	duts = ['shift_register_fifo', 'circular_pointer_fifo']
	width = 32
	for depth in [8, 16, 32, 64, 128]:
		for name in duts:
			for fixed in [False, True]:
				verify(name, fixed, ee, depth=depth, width=width)

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
