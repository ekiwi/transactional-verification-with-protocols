#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import z3
from functools import reduce


# helper functions
def tail(arg0: z3.BitVecRef, arg1: int):
	w = arg0.size()
	assert w > arg1 >= 0
	msb = w - arg1
	return z3.Extract(msb, low=0, a=arg0)

def head(arg0: z3.BitVecRef, arg1: int):
	w = arg0.size()
	assert w >= arg1 > 0
	msb = w - 1
	lsb = w - arg1
	return z3.Extract(high=msb, low=lsb, a=arg0)

def cat(*args):
	return z3.Concat(*args)


class MultiCycleTransaction:
	def __init__(self, name: str,inputs, outputs, sequence):
		self.name = name
		self.inputs = inputs
		self.outputs = outputs
		self.sequence = sequence


HavocCount = 0
def havoc(name: str, bits: int):
	global HavocCount
	nn = f"{name}_{HavocCount}"
	HavocCount += 1
	return z3.BitVec(nn, bits)
def state(name: str, default: z3.BitVecRef, value=None, do_havoc=False):
	if do_havoc:
		return havoc(name, default.size())
	elif value is None:
		return default
	else:
		assert default.sort() == value.sort()
		return value

# shift_reg
class ShiftReg:
	def __init__(self, LEN, data=None, do_havoc=False):
		self.LEN = LEN
		self.data = state('data', z3.BitVec('data', LEN), data, do_havoc)

	def next(self, en, d):
		outputs = {'q': tail(self.data, 1), 'par': head(self.data, self.LEN-1)}
		data_n = cat(d, outputs['par'])
		self.data = z3.If(en, data_n, self.data)
		return outputs

	def transaction(self):
		raise RuntimeError("TODO")


class SerAdd:
	def __init__(self, c_r=None, do_havoc=False):
		self.c_r = state('c_r', z3.BitVecVal(0, bv=1), c_r, do_havoc)
		self.inputs = {'a': 1, 'b': 1, 'clr': 1}

	def next(self, a, b, clr):
		axorb = a ^ b
		outputs = {
			'o_v': (axorb & self.c_r) | (a & b),
			'q': axorb ^ self.c_r
		}
		self.c_r = (~clr) & outputs['o_v']
		return outputs

	@staticmethod
	def Add(bits) -> MultiCycleTransaction:
		zero, one = z3.BitVecVal(0, 1), z3.BitVecVal(1,1)
		a, b = z3.BitVec('a', bits), z3.BitVec('b', bits)
		c = a + b
		sequence = [{'clr': one}] + [{
			'clr': zero,
			'a': z3.Extract(ii,ii, a),
			'b': z3.Extract(ii, ii, b),
			'q': z3.Extract(ii, ii, c)
		} for ii in range(bits)]

		inputs = {'a': a, 'b': b}
		outputs = {'c': c}

		return MultiCycleTransaction('Add', inputs=inputs, outputs=outputs, sequence=sequence)


# def clone(bv: z3.BitVecRef, suffix: str):
# 	assert len(suffix) > 0
# 	w = bv.size()
# 	return z3.BitVec(name=f"{bv}_{suffix}", bv=w)

def make_inputs(step, declarations):
	return { name: step.get(name, havoc(name, bits)) for name, bits in declarations.items() }
def check_outputs(step, outputs):
	return z3.And([step[name] == value for name, value in outputs.items() if name in step] + [z3.BoolVal(True)])
def record_values(s: z3.Solver, values, prefix=""):
	for name, value in values.items():
		lbl = z3.BitVec(prefix + "_" + name, value.size())
		s.add(lbl == value)

def check_transaction(ModuleClass, transcation: MultiCycleTransaction):
	print(f"Trying to verify transaction {transcation.name} on module {ModuleClass.__name__}")
	m = ModuleClass(do_havoc=True)

	equivalent = z3.BoolVal(True)

	print(f"Unrolling for {len(transcation.sequence)} cycles")

	s = z3.Solver()

	for ii, step in enumerate(transcation.sequence):
		iis = make_inputs(step, m.inputs)
		record_values(s, iis, f"step{ii}_in")
		oos = m.next(**iis)
		record_values(s, oos, f"step{ii}_out")
		print(ii)
		print(check_outputs(step, oos))
		print(m.c_r)
		print()
		equivalent = z3.And(equivalent, check_outputs(step, oos))


	print(equivalent)


	# s.add(z3.Not(equivalent))
	# is_sat = s.check()
	# print("(invalid)" if is_sat else "(valid)")
	# if is_sat:
	# 	print(s.model())





def main():
	check_transaction(SerAdd, SerAdd.Add(2))

	return 0




if __name__ == '__main__':
	import sys
	sys.exit(main())