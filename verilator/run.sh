#!/usr/bin/env bash
verilator --cc -Wno-fatal -Wno-width -O3 serv_top.v --trace --exe top.cpp
make -j -C obj_dir/ -f Vserv_top.mk Vserv_top
cat script | ./obj_dir/Vserv_top

