"""
Tests serv's shift instructions by applying appropriate inputs to the ALU module.
"""
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer

PERIOD = 62 # derived by examining waveform
TIMESTEP = "ns" # fs/ps/ns/us/ms/sec/None

def test_sll(dut):
    log = dut._log
    log.info("Running test")
    # In an sll (as demonstrated by instructions 28 and 7C of I-SLL-01.fst), o_rd is held 0 for the duration of the
    # instruction's execution, while o_sh_done is asserted after the passage of 63 cycles after i_en is first raised
    # (presumably in the manner of a stall). o_rd will then mirror the value of the shifter's o_q.
    cocotb.fork(Clock(dut.clk, PERIOD, TIMESTEP).start())

