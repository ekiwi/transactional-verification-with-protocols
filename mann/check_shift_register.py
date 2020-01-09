#!/usr/bin/env python3
# -*- coding: utf-8 -*-


from pysmt.shortcuts import *
from transactions import *
import math

shift_fifo = Module.load('shift_register_fifo', ['tacas2020/shift_register_fifo_fixed.v', 'tacas2020/FF.v'])

def verification_problem(dut: Module, depth=8, width=8) -> VerificationProblem:
	# architectural state: memory to store values + count to keep track of how many values are valid
	addr_bits = int(math.log2(depth))
	assert depth == 2**addr_bits, f"Only power of two depths are supported, not: {depth}"
	mem = Symbol(f'{dut.name}.mem', ArrayType(BVType(addr_bits), BVType(width)))
	count = Symbol(f'{dut.name}.count', BVType(addr_bits+1))
	read = Symbol(f'{dut.name}.read', BVType(addr_bits))
	state = {'mem': mem.symbol_type(), 'count': count.symbol_type(), 'read': read.symbol_type()}

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

	# read full (without pushing)
	# ... TODO

	not_full = BVULT(count, BV(depth,addr_bits+1))
	not_empty = Not(Equals(count, BV(0, addr_bits+1)))

	sp = Spec(state=state,
		transactions=[
			Transaction("Push", push_proto, push_sem, args={'push_data': BVType(width)}, guard=not_full),
			Transaction("Pop", pop_proto, pop_sem, ret_args={'pop_data': BVType(width)}, guard=not_empty),
		],
	)

	mappings = [StateMapping(count, Symbol('count', BVType(addr_bits+1)))] + [
		StateMapping(
			Select(mem, BVAdd(read, BV(ii, addr_bits))), Symbol(f'regs[{ii}].reg_inst.Q', BVType(width)),
			guard=BVUGT(count, BV(ii, addr_bits+1)))
		for ii in range(depth)
	]

	invariances = [
		BVULT(Symbol('count', BVType(addr_bits+1)), BV(depth+1, addr_bits+1))
	]

	return VerificationProblem(spec=sp, implementation=dut.name, invariances=invariances, mappings=mappings)




def main() -> int:
	prob = verification_problem(shift_fifo)

	ee = SMT2ProofEngine(outdir='../smt2')
	#ee = MCProofEngine(outdir="../btor2")
	Verifier(shift_fifo, prob, ee).proof_all()

	return 0

if __name__ == '__main__':
	import sys
	sys.exit(main())
