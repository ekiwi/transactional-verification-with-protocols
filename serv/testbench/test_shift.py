"""
Tests serv's shift instructions by applying appropriate inputs to the ALU module.
"""
from collections import defaultdict
from dataclasses import dataclass
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb.result import TestFailure

PERIOD = 10 #62 # derived by examining waveform
TIMESTEP = "ns" # fs/ps/ns/us/ms/sec/None

def get_ith_msb(n, i):
    """
    Returns the ith bit from the left of the 32-bit number.
    >>> get_ith_msb(0x7fffffff, 0)
    0
    >>> get_ith_msb(0x7fffffff, 1)
    1
    """
    return (n >> (31 - i)) & 0b1

def sra(n, i):
    """
    Performs an arithmetic right shift.
    Even though >> is the arithmetic shift operator in Python, integers are wider than 32 bits, so
    for our purposes it functions a logical shift.
    """
    return ((n >> i) | (0xffffffff << (32 - i)) & (0xffffffff if get_ith_msb(n, 0) else 0x0))

@dataclass
class Params:
    val: int
    shamt: int


@cocotb.coroutine
def create_shift_test(dut, params: Params, right: bool, arithmetic=False):
    log = dut._log
    op_string = ">>" if arithmetic else (">>>" if right else "<<")
    log.info(f"Testing {params.val} {op_string} {params.shamt}")

    def assign_sig(name, val):
        # hack to mimic async assign
        getattr(dut, name) <= val
    def read_sig(name):
        return getattr(dut, name).value.get_value()

    # In an sll (as demonstrated by instructions 28 and 7C of I-SLL-01.fst), o_rd is held 0 for the duration of the
    # instruction's execution. o_rd will then mirror the value of the shifter's o_q.
    cocotb.fork(Clock(dut.clk, PERIOD, TIMESTEP).start())
    yield RisingEdge(dut.clk)
    dut.i_rst <= 1
    all_inputs = [
        "i_rd_sel", "i_sh_signed", "i_sh_right", "i_en", "i_init", "i_shamt_en",
        "i_rs1", "i_op_b",
        "i_buf" # shamt delayed by 32 cycles and change
    ]
    # Zero these first so we don't get Xs
    for input_sig in all_inputs:
        assign_sig(input_sig, 0)
    # Maps clock cycle to dict of signal name to new value
    I_EN_CYC = 1
    transitions = defaultdict(dict, {
        0: {
            "i_rst": 0,
            # Set i_rd_sel for shifts one cycle before i_en
            "i_rd_sel": 0b01
        },
        I_EN_CYC: {
            "i_sh_signed": int(arithmetic),
            "i_sh_right": int(right),
            # Assert i_en and i_init for 32 cycles
            "i_en": 1,
            "i_init": 1,
            # Assert i_shamt_en for 5 cycles
            "i_shamt_en": 1
        },
        I_EN_CYC + 5: {"i_shamt_en": 0},
        I_EN_CYC + 32: {"i_en": 0, "i_init": 0}
    })
    # rs1 and b inputs are asserted LSB to MSB, starting as soon as i_en is raised
    for i in range(32):
        sig_dict = transitions[i + I_EN_CYC]
        sig_dict["i_rs1"] = (params.val >> i) & 0b1
        sig_dict["i_op_b"] = (params.shamt >> i) & 0b1
    # As soon as I_LOAD goes low, the buf signal should begin transmitting the
    # value of rs1 (LSB first). Oddly enough, the LSB is also sign extended by one bit.
    transitions[I_EN_CYC + 32]["i_buf"] = params.val & 0b1
    for i in range(32):
        buf_dict_1 = transitions[i + I_EN_CYC + 33] # Offset by 1
        buf_dict_1["i_buf"] = (params.val >> i) & 0b1
        # The value is repeated again after the first instance.
        buf_dict_2 = transitions[i + I_EN_CYC + 65]
        buf_dict_2["i_buf"] = (params.val >> i) & 0b1

    exp_outputs = defaultdict(dict)
    if params.shamt == 0:
        exp_done_cycle = I_EN_CYC + 1
    elif right:
        # The discrepancy between right and left shift is likely because a left shift is
        # encoded as a negative right shift
        exp_done_cycle = I_EN_CYC + 32 + params.shamt
    else:
        # Instruction 7C (1 << 1) takes 63 cycles between i_en and o_sh_done
        # Instruction 80 (1 << 15) takes 49 cycles
        # Instruction 84 (1 << 31) takes 33 cycles
        # => The number of cycles a shift takes = 64 - shamt
        # If the shamt is 0, then done is asserted 1 cycle after i_en instead
        exp_done_cycle = I_EN_CYC + 64 - params.shamt
    exp_outputs[exp_done_cycle]["o_sh_done"] = 1
    # TODO ensure o_sh_done is 0 elsewhere
    # The value of o_rd is asserted beginning one cycle after o_sh_done is asserted
    # If shamt is 0, then it's asserted beginning... 32 cycles after o_sh_done?
    if arithmetic:
        exp_result = sra(params.val, params.shamt)
    elif right:
        exp_result = params.val >> params.shamt
    else:
        exp_result = params.val << params.shamt
    for i in range(32):
        cycle = i + exp_done_cycle + 1 if params.shamt != 0 else exp_done_cycle + i + 32
        exp_outputs[cycle]["o_rd"] = (exp_result >> i) & 0b1
    for i in range(exp_done_cycle + 64): # TODO when to stop?
        yield RisingEdge(dut.clk)
        # Perform transitions
        signals = transitions.get(i, {})
        for signal_name, signal_val in signals.items():
            assign_sig(signal_name, signal_val)
            # if signal_val > 0:
            #     log.info(f"Assigned {signal_val} to {signal_name} on cycle {i} (was {getattr(dut, signal_name)})")
        yield FallingEdge(dut.clk)
        # Check outputs
        outputs = exp_outputs.get(i, {})
        # value = getattr(dut, "o_sh_done").value
        # if value.is_resolvable:
        #     log.info(f"o_sh_done was {value} on cycle {i}")
        for output_name, exp_val in outputs.items():
            value = read_sig(output_name)
            # log.info(f"{output_name} was {value} on cycle {i}")
            # if type(value) == int and int(value) > 0:
                # log.warn(f"Output {output_name} was {value} on cycle {i}")
            if type(value) == int and int(value) == exp_val: # value can be x or z
                pass
                # log.info(f"[pass check] {output_name} was {value} on cycle {i}")
            else:
                # log.warn(f"{output_name} was {value} on cycle {i} (expected {exp_val})")
                raise TestFailure(f"{output_name} was {value} on cycle {i} (expected {exp_val})")

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
        yield create_shift_test(dut, params, right=False)

@cocotb.test()
def test_b_sll(dut):
    tests = [
        Params(0xbcdef110, 10),
        Params(0xdf344402, 15),
        Params(0x3949, 16),
        Params(0x94995, 0),
    ]
    for params in tests:
        yield create_shift_test(dut, params, right=False)

@cocotb.test()
def test_srl(dut):
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
        yield create_shift_test(dut, params, right=True)

@cocotb.test()
def test_b_srl(dut):
    tests = [
        Params(0xbcdef110, 10),
        Params(0xdf344402, 15),
        Params(0x3949, 16),
        Params(0x94995, 0),
        Params(0xffffffff, 0)
    ]
    for params in tests:
        yield create_shift_test(dut, params, right=True)

@cocotb.test()
def test_sra(dut):
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
        yield create_shift_test(dut, params, right=True, arithmetic=True)

@cocotb.test()
def test_b_sra(dut):
    tests = [
        Params(0xbcdef110, 10),
        Params(0xdf344402, 15),
        Params(0x3949, 16),
        Params(0x94995, 0),
        Params(0xffffffff, 0)
    ]
    for params in tests:
        yield create_shift_test(dut, params, right=True, arithmetic=True)