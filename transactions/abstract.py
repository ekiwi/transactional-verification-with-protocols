#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from .spec import Spec

def build_io_abstraction(spec: Spec):
	""" creates an abstract version of the module - derived form its spec - that can be used for compositional reasoning """

	# TODO: is it always ok to ignore achitectural state?
	#       the answer seems to be YES, as long as we do not support guards on the transactions

	# 1) collect protocols and turn them into a NFA

	# TODO: how can we reliably determine the unrestricted io?



	# 2) NFA -> DFA


