#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class SimplePipeSpec(Spec):
    INSTR_BIT_WIDTH = 8
    NOP_INSTR = BV(0, INSTR_BIT_WIDTH)

    def __init__(self):
        # In this simple example, we can just insert nops between instructions for now
        inst_wire = Symbol("spec_inst", BVType(SimplePipeSpec.INSTR_BIT_WIDTH))
        protocol = Protocol(
            [
                {"inst": inst_wire},
                # Insert nops to simulate pipeline flush
                {"inst": SimplePipeSpec.NOP_INSTR},
                {"inst": SimplePipeSpec.NOP_INSTR},
            ]
        )
        arch_state = {
            "r0": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
            "r1": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
            "r2": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
            "r3": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
        }
        def mapping(mod: Module, r0, r1, r2, r3):
            # Corresponds to ref-rel-var-map.json
            return [
                Or(Not(Equals(mod["reg_0_w_stage"], BV(0b10, 2))), Equals(mod["ex_alu_result"], r0)),
                Or(Not(Equals(mod["reg_0_w_stage"], BV(0b11, 2))), Equals(mod["ex_alu_result"], r0)),
                Or(Not(Equals(mod["reg_0_w_stage"], BV(0b01, 2))), Equals(mod["ex_wb_val"], r0)),
                Or(Not(Equals(mod["reg_0_w_stage"], BV(0b00, 2))), Equals(mod["registers[0]"], r0)),

                Or(Not(Equals(mod["reg_1_w_stage"], BV(0b10, 2))), Equals(mod["ex_alu_result"], r1)),
                Or(Not(Equals(mod["reg_1_w_stage"], BV(0b11, 2))), Equals(mod["ex_alu_result"], r1)),
                Or(Not(Equals(mod["reg_1_w_stage"], BV(0b01, 2))), Equals(mod["ex_wb_val"], r1)),
                Or(Not(Equals(mod["reg_1_w_stage"], BV(0b00, 2))), Equals(mod["registers[1]"], r1)),

                Or(Not(Equals(mod["reg_2_w_stage"], BV(0b10, 2))), Equals(mod["ex_alu_result"], r2)),
                Or(Not(Equals(mod["reg_2_w_stage"], BV(0b11, 2))), Equals(mod["ex_alu_result"], r2)),
                Or(Not(Equals(mod["reg_2_w_stage"], BV(0b01, 2))), Equals(mod["ex_wb_val"], r2)),
                Or(Not(Equals(mod["reg_2_w_stage"], BV(0b00, 2))), Equals(mod["registers[2]"], r2)),

                Or(Not(Equals(mod["reg_3_w_stage"], BV(0b10, 2))), Equals(mod["ex_alu_result"], r3)),
                Or(Not(Equals(mod["reg_3_w_stage"], BV(0b11, 2))), Equals(mod["ex_alu_result"], r3)),
                Or(Not(Equals(mod["reg_3_w_stage"], BV(0b01, 2))), Equals(mod["ex_wb_val"], r3)),
                Or(Not(Equals(mod["reg_3_w_stage"], BV(0b00, 2))), Equals(mod["registers[3]"], r3)),
            ]
        def semantics(inst, r0, r1, r2, r3):
            # Perhaps it would be better to specify an obj of input dicts + arch state or something?
            opcode = BVExtract(inst, 6, 7)
            rs1 = BVExtract(inst, 4, 5)
            rs2 = BVExtract(inst, 2, 3)
            rd = BVExtract(inst, 0, 1)
            rs1_val = Ite(
                Equals(rs1, BVZero(2)),
                r0,
                Ite(
                    Equals(rs1, BVOne(2)),
                    r1,
                    Ite(
                        Equals(rs1, BV(2, 2)),
                        r2,
                        r3
                    )
                )
            )
            rs2_val = Ite(
                Equals(rs2, BVZero(2)),
                r0,
                Ite(
                    Equals(rs2, BVOne(2)),
                    r1,
                    Ite(
                        Equals(rs2, BV(2, 2)),
                        r2,
                        r3
                    )
                )
            )
            return {
                "spec_dummy_read_rf": ...,
                "r0": ...,
                "r1": ...,
                "r2": ...,
                "r3": ...,
            }
        transactions = [Transaction(name="simple_pipe", args=[inst_wire], ret_args=[], semantics=semantics, proto=protocol)]
        super().__init__(arch_state=arch_state, mapping=mapping, transactions=transactions)

def prove(verilog_path, mod_name, spec_class, reset="rst"):
    version = require_yosys()
    print(f"Using yosys {version}")
    mod = Module.load(mod_name, [verilog_path], reset=reset)
    spec = spec_class()
    print(f"Trying to prove {mod.name}")
    ee = SMT2ProofEngine(outdir='smt2')
    # ee = MCProofEngine(outdir="btor2")
    Verifier(mod, spec, ee).proof_all()

def main():
    correct_v = os.path.join("simple_pipe.v")
    wrong_v = os.path.join("simple_pipe_wrong.v")
    prove(correct_v, "pipeline_v", SimplePipeSpec)
    prove(wrong_v, "pipeline_v", SimplePipeSpec)

if __name__ == '__main__':
    main()
