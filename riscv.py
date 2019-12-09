#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# common riscv instruction semantics



# NOTES: on load/store instructions
# The question here is how do we encode the memory operation which is only visible as a b us transaction?
#
# Potential LOAD encoding:
# offset, rs1, width, rd
# addr := Zext(20, offset) + regs[rs1]
# data := read(addr)
# regs := regs[rd := data]
# => how do we map read(a0) -> r0 to the transaction graph?
#
#
# "desugared" load
# read_addr := Zext(20, offset) + regs[rs1]
# regs := regs[rd := read_data]
# In this case read_addr becomes a ret_arg, read_data becomes an arg.