#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class SimplePipeSpec(Spec):
    INSTR_BIT_WIDTH = 8
    NOP_INSTR = BV(0, INSTR_BIT_WIDTH)

    def __init__(self):
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
        super().__init__(arch_state=arch_state, mapping=mapping, transactions=[self.op_add()])

    def op_add(self):
        # In this simple example, we can just insert nops between instructions for now
        opcode = Symbol("spec_opcode", BVType(2))
        rs1 = Symbol("spec_rs1", BVType(2))
        rs2 = Symbol("spec_rs2", BVType(2))
        rd = Symbol("spec_rd", BVType(2))
        protocol = Protocol(
            [
                {"inst": BVConcat(opcode, BVConcat(rs1, BVConcat(rs2, rd)))},
                # Insert nops to simulate pipeline flush
                {"inst": SimplePipeSpec.NOP_INSTR},
                {"inst": SimplePipeSpec.NOP_INSTR},
            ]
        )
        def semantics(spec_opcode, spec_rs1, spec_rs2, spec_rd, r0, r1, r2, r3):
            opcode = spec_opcode
            rs1 = spec_rs1
            rs2 = spec_rs2
            rd = spec_rd
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
            rd_val = BVAdd(rs1_val, rs2_val)
            is_nop = Equals(opcode, BVZero(2))
            return {
                "r0": rd_val if not is_nop and rd == BV(0, 2) else r0,
                "r1": rd_val if not is_nop and rd == BV(1, 2) else r1,
                "r2": rd_val if not is_nop and rd == BV(2, 2) else r2,
                "r3": rd_val if not is_nop and rd == BV(3, 2) else r3,
            }
        return Transaction(name="simple_pipe", args=[opcode, rs1, rs2, rd], ret_args=[], semantics=semantics, proto=protocol)

def prove(verilog_path, mod_name, spec_class, reset=HighActiveReset("rst")):
    version = require_yosys()
    print(f"Using yosys {version}")
    mod = Module.load(mod_name, [verilog_path], reset=reset)
    spec = spec_class()
    print(f"Trying to prove {mod.name}")
    ee = SMT2ProofEngine(outdir='../smt2')
    # ee = MCProofEngine(outdir="btor2")
    Verifier(mod, spec, ee).proof_all()

def main():
    correct_v = os.path.join("simple_pipe2.v")
    wrong_v = os.path.join("simple_pipe_wrong.v")
    prove(correct_v, "pipeline_v", SimplePipeSpec)
    prove(wrong_v, "pipeline_v", SimplePipeSpec)

if __name__ == '__main__':
    main()
