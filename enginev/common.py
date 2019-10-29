#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
from pysmt.shortcuts import *
from transactions import *

sources = [os.path.join('hdl', name + '.v') for name in ['addsub8', 'mf8_alu', 'mf8_core', 'mf8_reg']]
