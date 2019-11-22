"""
Tests serv's shift instructions by applying appropriate inputs to the ALU module.
"""
from dataclasses import dataclass
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

PERIOD = 62 # derived by examining waveform
TIMESTEP = "ns" # fs/ps/ns/us/ms/sec/None

@dataclass
class Params:
    val: int
    shamt: int

@cocotb.coroutine
def create_sll_test(dut, params: Params):
    log = dut._log
    log.info(f"Testing {params.val} << {params.shamt}")
    # In an sll (as demonstrated by instructions 28 and 7C of I-SLL-01.fst), o_rd is held 0 for the duration of the
    # instruction's execution. o_rd will then mirror the value of the shifter's o_q.
    # Instruction 7C (1 << 1) takes 63 cycles between i_en and o_sh_done
    # Instruction 80 (1 << 15) takes 49 cycles
    # Instruction 84 (1 << 31) takes 33 cycles
    # => The number of cycles a shift takes = 64 - shamt
    cocotb.fork(Clock(dut.clk, PERIOD, TIMESTEP).start())
    dut.i_rst <= 1
    yield RisingEdge(dut.clk)
    # Maps clock cycle to dict of signal name to new value
    transitions = {
        0: {
            "i_rst": 0,
            # Set i_rd_sel for shifts one cycle before i_en
            "i_rd_sel": 0b01
        },
        1: {
            # For left shifts, hold i_sh_signed and i_sh_right low
            "i_sh_signed": 0,
            "i_sh_right": 0,
            # Assert i_en and i_init for 32 cycles
            "i_en": 1,
            "i_init": 1,
            # Assert i_shamt_en for 5 cycles
            "i_shamt_en": 1
        },
        6: {"i_shamt_en": 0},
        33: {"i_en": 0, "i_init": 0}
    }
    for i in range(128): # TODO when to stop?
        signals = transitions.get(i, {})
        for signal_name, signal_val in signals.items():
            # hack to mimic async assign
            log.info(f"Assigning {signal_val} to {signal_name}")
            getattr(dut, signal_name) <= signal_val

@cocotb.test()
def test_sll(dut):
    # tuples of (val, shamt)
    tests = [
        Params(0, 1),
        # Params(0, 15),
        # Params(0, 31),
        # Params(0, 0),
        # Params(1, 1),
        # Params(1, 15),
        # Params(1, 31),
        # Params(1, 0)
    ]
    for params in tests:
        yield create_sll_test(dut, params)
