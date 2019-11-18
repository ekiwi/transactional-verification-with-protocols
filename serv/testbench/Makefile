VERILOG_DIR=../fork/rtl
VERILOG_SOURCES=$(VERILOG_DIR)/ser_shift.v $(VERILOG_DIR)/ser_add.v $(VERILOG_DIR)/shift_reg.v \
                $(VERILOG_DIR)/serv_params.vh $(VERILOG_DIR)/ser_lt.v $(VERILOG_DIR)/serv_alu.v

# TOPLEVEL is the name of the toplevel module in your Verilog or VHDL file:
TOPLEVEL=serv_alu
# MODULE is the name of the Python test file:
MODULE=test_shift

COMPILE_ARGS=-I $(VERILOG_DIR)

include $(shell cocotb-config --makefiles)/Makefile.inc
include $(shell cocotb-config --makefiles)/Makefile.sim