"""
Tests serv's shift instructions by applying appropriate inputs to the ALU module.
"""
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
def test_sll(dut):
    log = dut._log
    log.info("Running test!")
    for cycle in range(10):
        dut.clk = 0
        yield Timer(1, units='ns')
        dut.clk = 1
        yield Timer(1, units='ns')
    log.info("Running test!")
