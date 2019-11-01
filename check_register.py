#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

class RegisterSpec(Spec):
    def __init__(self):
        in_wire = Symbol("spec_in", BVType(5))
        out_wire = Symbol("spec_out", BVType(5))
        mid_reg = BVType(5)
        protocol = Protocol([{"in": in_wire, "out": out_wire}])
        def mapping(mod: Module, mid_reg):
            """Describes the mapping of architectural state to actual verilog wires."""
            return [Equals(mod["r"], mid_reg)]
        def semantics(spec_in, mid_reg):
            return {"spec_out": mid_reg, "mid_reg": spec_in}
        transactions = [Transaction(name="register", args=[in_wire], ret_args=[out_wire], semantics=semantics, proto=protocol)]
        super().__init__(arch_state={"mid_reg": mid_reg}, mapping=mapping, transactions=transactions)

reg_v = os.path.join("register.v")

def main():
    version = require_yosys()
    print(f"Using yosys {version}")
    mod = Module.load("register", [reg_v], reset="rst")
    spec = RegisterSpec()
    print(f"Trying to prove {mod.name}")
    ee = SMT2ProofEngine(outdir='smt2')
    # ee = MCProofEngine(outdir="btor2")
    Verifier(mod, spec, ee).proof_all()

if __name__ == '__main__':
    main()
