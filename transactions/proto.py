#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from .spec import *
from pysmt.shortcuts import Symbol
from collections import defaultdict

# protocol processing algorithms


def protocol_constraints(proto: Protocol):
	""" compute i/o constraints of protocol (without semantics) """

	# NOTE: this replaces parts of `generate_inputs` in `verifier.py`

	# variable -> interval -> (cycle, signal_expr)
	var2inputs: Dict[SmtExpr, Dict[Tuple[int, int], List[Tuple[int, SmtExpr]]]] = defaultdict(lambda: defaultdict(list))

	# find constant and variable mapping on the protocol inputs
	for ii, tt in enumerate(proto.transitions):
		for signal_name, expr in tt.inputs.items():
			sig = Symbol(signal_name, module.inputs[signal_name])
			for (signal_msb, signal_lsb, (var_msb, var_lsb, var)) in FindVariableIntervals.find(expr):
				is_full = signal_lsb == 0 and signal_msb + 1 == sig.symbol_type().width
				if is_full:
					sig_expr = sig
				else:
					sig_expr = BVExtract(sig, start=signal_lsb, end=signal_msb)
				if var.is_symbol():
					var2inputs[var][(var_msb, var_lsb)].append((ii + offset, sig_expr))
				else:
					assert var_lsb == 0 and var_msb + 1 == var.get_type().width, f"Expect constants to be simplified!"
					# check that the input has the correct constant value in cycle ii+offset
					if assume_dont_assert_requirements:
						check.assume_at(ii + offset, Equals(sig_expr, var))
					else:
						check.assert_at(ii + offset, Equals(sig_expr, var))

	# make sure that all arguments of the transaction are defined in the protocol
	for name, tpe in tran.args.items():
		if Symbol(name, tpe) not in var2inputs:
			# TODO: uncomment
			#print(f"WARN: in transaction {tran.name}: argument {name} is not defined by the protocol. Will be random!")
			check.constant(Symbol(prefix + name, tpe))

	# declare protocol arguments and their restrictions
	for var, refs in var2inputs.items():
		# check that there are no overlapping intervals as they aren't supported yet
		covered_bits = set()
		for (msb, lsb) in refs.keys():
			for bit in range(lsb, msb + 1):
				assert bit not in covered_bits, f"Overlapping intervals on {var}[{bit}]"
				covered_bits.add(bit)

		# check that all bits are defined
		for bit in range(var.symbol_type().width):
			if bit not in covered_bits:
				# TODO: uncomment
				#print(f"WARN: in transaction {tran.name}: argument bit {var}[{bit}] is not defined by the protocol.")
				pass

		# generate input constant
		var_sym = Symbol(prefix + var.symbol_name(), var.symbol_type())
		check.constant(var_sym)

		# generate conditions for each interval
		for ((msb, lsb), mappings) in refs.items():
			assert len(mappings) > 0
			full_range = msb + 1 == var.symbol_type().width and lsb == 0

			# find (one of) the first references to this interval
			mappings_sorted_by_cycle = sorted(mappings, key=lambda ii: ii[0])
			start = mappings_sorted_by_cycle[0]

			# we bind the start mapping to a constant and then check every other mapping against the constant
			if full_range:
				constant = var_sym
			else:
				constant = BVExtract(var_sym, start=lsb, end=msb)

			# map the constant to the input variable symbol
			check.assume_at(start[0], Equals(constant, start[1]))
			for cycle, expr in mappings_sorted_by_cycle[1:]:
				if assume_dont_assert_requirements:
					check.assume_at(cycle, Equals(expr, constant))
				else:
					check.assert_at(cycle, Equals(expr, constant))


	pass