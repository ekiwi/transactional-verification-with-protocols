#!/usr/bin/env bash

source venv/bin/activate
export PYTHONPATH=$PWD

echo "serv"
cd serv
./check_adder.py
./check_alu.py
./check_regfile.py
./check_add_end_to_end.py
cd ..

echo "engine-v"
cd enginev
./check_mf8_reg.py
cd ..
