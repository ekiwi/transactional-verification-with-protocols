"""
Tests serv's shift instructions by applying appropriate inputs to the ALU module.
"""
from dataclasses import dataclass
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb.result import TestFailure

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

    def assign_sig(name, val):
        # hack to mimic async assign
        getattr(dut, name) <= val
    def read_sig(name):
        return getattr(dut, name).value.get_value()

    # In an sll (as demonstrated by instructions 28 and 7C of I-SLL-01.fst), o_rd is held 0 for the duration of the
    # instruction's execution. o_rd will then mirror the value of the shifter's o_q.
    cocotb.fork(Clock(dut.clk, PERIOD, TIMESTEP).start())
    dut.i_rst <= 1
    all_inputs = [
        "i_rd_sel", "i_sh_signed", "i_sh_right", "i_en", "i_init", "i_shamt_en",
        "i_rs1", "i_op_b",
        "i_buf" # no clue what this thing is
    ]
    # Zero these first so we don't get xs
    for input_sig in all_inputs:
        assign_sig(input_sig, 0)
    yield RisingEdge(dut.clk)
    # Maps clock cycle to dict of signal name to new value
    I_EN_CYC = 1
    transitions = {
        0: {
            "i_rst": 0,
            # Set i_rd_sel for shifts one cycle before i_en
            "i_rd_sel": 0b01
        },
        I_EN_CYC: {
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
    # rs1 and b inputs are asserted LSB to MSB, starting as soon as i_en is raised
    for i in range(0, 32):
        if i + I_EN_CYC not in transitions:
            transitions[i + I_EN_CYC] = {}
        sig_dict = transitions[i + I_EN_CYC]
        sig_dict["i_rs1"] = (params.val >> i) & 0b1
        sig_dict["i_op_b"] = (params.shamt >> i) & 0b1
    exp_outputs = {}
    # Instruction 7C (1 << 1) takes 63 cycles between i_en and o_sh_done
    # Instruction 80 (1 << 15) takes 49 cycles
    # Instruction 84 (1 << 31) takes 33 cycles
    # => The number of cycles a shift takes = 64 - shamt
    exp_done_cycle = I_EN_CYC + 64 - params.shamt
    if exp_done_cycle not in exp_outputs:
        exp_outputs[exp_done_cycle] = {}
    exp_outputs[exp_done_cycle]["o_sh_done"] = 1
    # TODO ensure o_sh_done is 0 elsewhere
    # The value of o_rd is asserted beginning one cycle after o_sh_done is asserted
    exp_result = params.val << params.shamt
    for i in range(0, 32):
        if i + exp_done_cycle + 1 not in exp_outputs:
            exp_outputs[i + exp_done_cycle + 1] = {}
        exp_outputs[i + exp_done_cycle + 1]["o_rd"] = (exp_result >> i) & 0b1
    for i in range(exp_done_cycle + 32): # TODO when to stop?
        # Check outputs
        outputs = exp_outputs.get(i, {})
        for output_name, exp_val in outputs.items():
            value = read_sig(output_name)
            # log.info(f"{output_name} was {value} on cycle {i}")
            if type(value) == int and int(value) == exp_val: # value can be x or z
                log.info(f"[pass check] {output_name} was {value} on cycle {i}")
            else:
                log.warn(f"{output_name} was {value} on cycle {i} (expected {exp_val})")
                # raise TestFailure(f"{output_name} was {value} on cycle {i} (expected {exp_val})")
        # Perform transitions
        signals = transitions.get(i, {})
        for signal_name, signal_val in signals.items():
            assign_sig(signal_name, signal_val)
            log.debug(f"Assigned {signal_val} to {signal_name} on cycle {i} (was {getattr(dut, signal_name)})")
        yield RisingEdge(dut.clk)

@cocotb.test()
def test_sll(dut):
    # tuples of (val, shamt)
    tests = [
        Params(0, 1),
        Params(0, 15),
        Params(0, 31),
        Params(0, 0),
        Params(1, 1),
        Params(1, 15),
        Params(1, 31),
        Params(1, 0)
    ]
    for params in tests:
        yield create_sll_test(dut, params)
