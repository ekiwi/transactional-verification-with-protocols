#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
from dataclasses import dataclass
from typing import Dict, Union
import functools

class BitVector:
	def __init__(self):
		pass

	@staticmethod
	def random(bits):
		return 0

@dataclass
class VerilatorSignal:
	name: str
	typ: str
	dir: str

	def __le__(self, other):
		if isinstance(other, int):
			print(f"{self.name} <= int({other})")
		elif isinstance(other, bool):
			print(f"{self.name} <= bool({other})")
		else:
			assert False, f"Unexpected type: {other}"

class VerilatorModule:
	def __init__(self, signals: Dict[str, VerilatorSignal]):
		self.signals = signals

	def __getattr__(self, item) -> VerilatorSignal:
		assert isinstance(item, str), f"Expected string not {type(item)} ({item})"
		return self.signals[item]

def expect(expr):
	assert expr

def ensure(expr):
	assert expr

def cat(a, b):
	raise NotImplementedError("TODO")

#############################################################
def test_regfile(dut: VerilatorModule):
	rs1_addr = BitVector.random(5)
	rs2_addr = BitVector.random(5)
	rd_addr = BitVector.random(5)
	rd_en = BitVector.random(1)
	rd = BitVector.random(32)

	rs1 = read_reg(dut, rs1_addr)
	rs2 = read_reg(dut, rs2_addr)

	old_regs = [read_reg(dut, ii) for ii in range(32)]
	ensure(old_regs[0] == 0)

	regfile_rw(dut, rs1_addr, rs2_addr, rd_addr, rd_en, rd, rs1, rs2)

	for ii in range(32):
		if rd_en and ii != 0 and rd_addr == ii:
			expect(read_reg(dut, ii)) == rd
		else:
			expect(read_reg(dut, ii)) == old_regs[ii]


def read_reg(dut: VerilatorModule, ii: int):
	if ii == 0: return 0
	bits = [dut.memory[ii * 16 + jj] for jj in reversed(range(16))]
	return functools.reduce(cat, bits)

def regfile_rw(dut: VerilatorModule, rs1_addr, rs2_addr, rd_addr, rd_en, rd, rs1, rs2):
	dut.i_go <= 1
	dut.i_rd_en <= 0
	expect(dut.o_ready == 0)
	dut.step()

	dut.i_go <= 0
	dut.i_rs1_addr <= rs1_addr
	dut.i_rs2_addr <= rs2_addr
	expect(dut.o_ready == 0)
	dut.step()

	expect(dut.o_ready == 1)
	dut.step()

	for ii  in range(32):
		dut.i_rd_en <= rd_en
		dut.i_rd_addr <= rd_addr
		dut.i_rd <= rd[ii]

		expect(dut.o_rs1 == rs1[ii])
		expect(dut.o_rs2 == rs2[ii])
		expect(dut.o_ready == 0)

if __name__ == '__main__':
	src = os.path.join('..', 'fork', 'rtl', 'serv_regfile.v')
	dut = VerilatorModule.load('serv_regfile', src)
	test_regfile(dut)