#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class SimplePipeSpec(Spec):
    INSTR_BIT_WIDTH = 8
    NOPCODE = BVZero(2)

    def __init__(self):
        # In this simple example, we can just insert nops between instructions for now
        inst_wire = Symbol("spec_inst", BVType(SimplePipeSpec.INSTR_BIT_WIDTH))
        dummy_rf_data_wire = Symbol("spec_dummy_rf_data", BVType(SimplePipeSpec.INSTR_BIT_WIDTH))
        dummy_read_rf_wire = Symbol("spec_dummy_read_rf", BVType(2))
        protocol = Protocol(
            # TODO insert nops somehow
            [
                {"inst": inst_wire, "dummy_read_rf": dummy_read_rf_wire, "dummy_rf_data": dummy_rf_data_wire}
            ]
        )
        arch_state = {
            "r0": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
            "r1": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
            "r2": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
            "r3": BVType(SimplePipeSpec.INSTR_BIT_WIDTH),
        }
        def mapping(mod: Module, r0, r1, r2, r3):
            return [

            ]
        def semantics(inst, dummy_read_rf, r0, r1, r2, r3):
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
        transactions = [Transaction(name="register", args=[in_wire], ret_args=[out_wire], semantics=semantics, proto=protocol)]
        super().__init__(arch_state=arch_state, mapping=mapping, transactions=transactions)

def prove(verilog_path, spec_class, reset="rst"):
    version = require_yosys()
    print(f"Using yosys {version}")
    mod = Module.load("register", [verilog_path], reset=reset)
    spec = spec_class()
    print(f"Trying to prove {mod.name}")
    ee = SMT2ProofEngine(outdir='smt2')
    # ee = MCProofEngine(outdir="btor2")
    Verifier(mod, spec, ee).proof_all()

def main():
    correct_v = os.path.join("simple_pipe.v")
    wrong_v = os.path.join("simple_pipe_wrong.v")
    prove(correct_v, SimplePipeSpec)
    prove(wrong_v, SimplePipeSpec)

if __name__ == '__main__':
    main()
