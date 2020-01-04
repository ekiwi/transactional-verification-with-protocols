module Core(
  input         clock,
  input         reset,
  input         io_host_fromhost_valid,
  input  [31:0] io_host_fromhost_bits,
  output [31:0] io_host_tohost,
  output        io_icache_req_valid,
  output [31:0] io_icache_req_bits_addr,
  input         io_icache_resp_valid,
  input  [31:0] io_icache_resp_bits_data,
  output        io_dcache_abort,
  output        io_dcache_req_valid,
  output [31:0] io_dcache_req_bits_addr,
  output [31:0] io_dcache_req_bits_data,
  output [3:0]  io_dcache_req_bits_mask,
  input         io_dcache_resp_valid,
  input  [31:0] io_dcache_resp_bits_data
);
  wire  dpath_clock; // @[Core.scala 35:21]
  wire  dpath_reset; // @[Core.scala 35:21]
  wire  dpath_io_host_fromhost_valid; // @[Core.scala 35:21]
  wire [31:0] dpath_io_host_fromhost_bits; // @[Core.scala 35:21]
  wire [31:0] dpath_io_host_tohost; // @[Core.scala 35:21]
  wire  dpath_io_icache_req_valid; // @[Core.scala 35:21]
  wire [31:0] dpath_io_icache_req_bits_addr; // @[Core.scala 35:21]
  wire  dpath_io_icache_resp_valid; // @[Core.scala 35:21]
  wire [31:0] dpath_io_icache_resp_bits_data; // @[Core.scala 35:21]
  wire  dpath_io_dcache_abort; // @[Core.scala 35:21]
  wire  dpath_io_dcache_req_valid; // @[Core.scala 35:21]
  wire [31:0] dpath_io_dcache_req_bits_addr; // @[Core.scala 35:21]
  wire [31:0] dpath_io_dcache_req_bits_data; // @[Core.scala 35:21]
  wire [3:0] dpath_io_dcache_req_bits_mask; // @[Core.scala 35:21]
  wire  dpath_io_dcache_resp_valid; // @[Core.scala 35:21]
  wire [31:0] dpath_io_dcache_resp_bits_data; // @[Core.scala 35:21]
  wire [31:0] dpath_io_ctrl_inst; // @[Core.scala 35:21]
  wire [1:0] dpath_io_ctrl_pc_sel; // @[Core.scala 35:21]
  wire  dpath_io_ctrl_inst_kill; // @[Core.scala 35:21]
  wire  dpath_io_ctrl_A_sel; // @[Core.scala 35:21]
  wire  dpath_io_ctrl_B_sel; // @[Core.scala 35:21]
  wire [2:0] dpath_io_ctrl_imm_sel; // @[Core.scala 35:21]
  wire [3:0] dpath_io_ctrl_alu_op; // @[Core.scala 35:21]
  wire [2:0] dpath_io_ctrl_br_type; // @[Core.scala 35:21]
  wire [1:0] dpath_io_ctrl_st_type; // @[Core.scala 35:21]
  wire [2:0] dpath_io_ctrl_ld_type; // @[Core.scala 35:21]
  wire [1:0] dpath_io_ctrl_wb_sel; // @[Core.scala 35:21]
  wire  dpath_io_ctrl_wb_en; // @[Core.scala 35:21]
  wire [2:0] dpath_io_ctrl_csr_cmd; // @[Core.scala 35:21]
  wire  dpath_io_ctrl_illegal; // @[Core.scala 35:21]
  wire [31:0] ctrl_io_inst; // @[Core.scala 36:21]
  wire [1:0] ctrl_io_pc_sel; // @[Core.scala 36:21]
  wire  ctrl_io_inst_kill; // @[Core.scala 36:21]
  wire  ctrl_io_A_sel; // @[Core.scala 36:21]
  wire  ctrl_io_B_sel; // @[Core.scala 36:21]
  wire [2:0] ctrl_io_imm_sel; // @[Core.scala 36:21]
  wire [3:0] ctrl_io_alu_op; // @[Core.scala 36:21]
  wire [2:0] ctrl_io_br_type; // @[Core.scala 36:21]
  wire [1:0] ctrl_io_st_type; // @[Core.scala 36:21]
  wire [2:0] ctrl_io_ld_type; // @[Core.scala 36:21]
  wire [1:0] ctrl_io_wb_sel; // @[Core.scala 36:21]
  wire  ctrl_io_wb_en; // @[Core.scala 36:21]
  wire [2:0] ctrl_io_csr_cmd; // @[Core.scala 36:21]
  wire  ctrl_io_illegal; // @[Core.scala 36:21]
  Datapath dpath ( // @[Core.scala 35:21]
    .clock(dpath_clock),
    .reset(dpath_reset),
    .io_host_fromhost_valid(dpath_io_host_fromhost_valid),
    .io_host_fromhost_bits(dpath_io_host_fromhost_bits),
    .io_host_tohost(dpath_io_host_tohost),
    .io_icache_req_valid(dpath_io_icache_req_valid),
    .io_icache_req_bits_addr(dpath_io_icache_req_bits_addr),
    .io_icache_resp_valid(dpath_io_icache_resp_valid),
    .io_icache_resp_bits_data(dpath_io_icache_resp_bits_data),
    .io_dcache_abort(dpath_io_dcache_abort),
    .io_dcache_req_valid(dpath_io_dcache_req_valid),
    .io_dcache_req_bits_addr(dpath_io_dcache_req_bits_addr),
    .io_dcache_req_bits_data(dpath_io_dcache_req_bits_data),
    .io_dcache_req_bits_mask(dpath_io_dcache_req_bits_mask),
    .io_dcache_resp_valid(dpath_io_dcache_resp_valid),
    .io_dcache_resp_bits_data(dpath_io_dcache_resp_bits_data),
    .io_ctrl_inst(dpath_io_ctrl_inst),
    .io_ctrl_pc_sel(dpath_io_ctrl_pc_sel),
    .io_ctrl_inst_kill(dpath_io_ctrl_inst_kill),
    .io_ctrl_A_sel(dpath_io_ctrl_A_sel),
    .io_ctrl_B_sel(dpath_io_ctrl_B_sel),
    .io_ctrl_imm_sel(dpath_io_ctrl_imm_sel),
    .io_ctrl_alu_op(dpath_io_ctrl_alu_op),
    .io_ctrl_br_type(dpath_io_ctrl_br_type),
    .io_ctrl_st_type(dpath_io_ctrl_st_type),
    .io_ctrl_ld_type(dpath_io_ctrl_ld_type),
    .io_ctrl_wb_sel(dpath_io_ctrl_wb_sel),
    .io_ctrl_wb_en(dpath_io_ctrl_wb_en),
    .io_ctrl_csr_cmd(dpath_io_ctrl_csr_cmd),
    .io_ctrl_illegal(dpath_io_ctrl_illegal)
  );
  Control ctrl ( // @[Core.scala 36:21]
    .io_inst(ctrl_io_inst),
    .io_pc_sel(ctrl_io_pc_sel),
    .io_inst_kill(ctrl_io_inst_kill),
    .io_A_sel(ctrl_io_A_sel),
    .io_B_sel(ctrl_io_B_sel),
    .io_imm_sel(ctrl_io_imm_sel),
    .io_alu_op(ctrl_io_alu_op),
    .io_br_type(ctrl_io_br_type),
    .io_st_type(ctrl_io_st_type),
    .io_ld_type(ctrl_io_ld_type),
    .io_wb_sel(ctrl_io_wb_sel),
    .io_wb_en(ctrl_io_wb_en),
    .io_csr_cmd(ctrl_io_csr_cmd),
    .io_illegal(ctrl_io_illegal)
  );
  assign io_host_tohost = dpath_io_host_tohost; // @[Core.scala 38:11]
  assign io_icache_req_valid = dpath_io_icache_req_valid; // @[Core.scala 39:19]
  assign io_icache_req_bits_addr = dpath_io_icache_req_bits_addr; // @[Core.scala 39:19]
  assign io_dcache_abort = dpath_io_dcache_abort; // @[Core.scala 40:19]
  assign io_dcache_req_valid = dpath_io_dcache_req_valid; // @[Core.scala 40:19]
  assign io_dcache_req_bits_addr = dpath_io_dcache_req_bits_addr; // @[Core.scala 40:19]
  assign io_dcache_req_bits_data = dpath_io_dcache_req_bits_data; // @[Core.scala 40:19]
  assign io_dcache_req_bits_mask = dpath_io_dcache_req_bits_mask; // @[Core.scala 40:19]
  assign dpath_clock = clock;
  assign dpath_reset = reset;
  assign dpath_io_host_fromhost_valid = io_host_fromhost_valid; // @[Core.scala 38:11]
  assign dpath_io_host_fromhost_bits = io_host_fromhost_bits; // @[Core.scala 38:11]
  assign dpath_io_icache_resp_valid = io_icache_resp_valid; // @[Core.scala 39:19]
  assign dpath_io_icache_resp_bits_data = io_icache_resp_bits_data; // @[Core.scala 39:19]
  assign dpath_io_dcache_resp_valid = io_dcache_resp_valid; // @[Core.scala 40:19]
  assign dpath_io_dcache_resp_bits_data = io_dcache_resp_bits_data; // @[Core.scala 40:19]
  assign dpath_io_ctrl_pc_sel = ctrl_io_pc_sel; // @[Core.scala 41:17]
  assign dpath_io_ctrl_inst_kill = ctrl_io_inst_kill; // @[Core.scala 41:17]
  assign dpath_io_ctrl_A_sel = ctrl_io_A_sel; // @[Core.scala 41:17]
  assign dpath_io_ctrl_B_sel = ctrl_io_B_sel; // @[Core.scala 41:17]
  assign dpath_io_ctrl_imm_sel = ctrl_io_imm_sel; // @[Core.scala 41:17]
  assign dpath_io_ctrl_alu_op = ctrl_io_alu_op; // @[Core.scala 41:17]
  assign dpath_io_ctrl_br_type = ctrl_io_br_type; // @[Core.scala 41:17]
  assign dpath_io_ctrl_st_type = ctrl_io_st_type; // @[Core.scala 41:17]
  assign dpath_io_ctrl_ld_type = ctrl_io_ld_type; // @[Core.scala 41:17]
  assign dpath_io_ctrl_wb_sel = ctrl_io_wb_sel; // @[Core.scala 41:17]
  assign dpath_io_ctrl_wb_en = ctrl_io_wb_en; // @[Core.scala 41:17]
  assign dpath_io_ctrl_csr_cmd = ctrl_io_csr_cmd; // @[Core.scala 41:17]
  assign dpath_io_ctrl_illegal = ctrl_io_illegal; // @[Core.scala 41:17]
  assign ctrl_io_inst = dpath_io_ctrl_inst; // @[Core.scala 41:17]
endmodule
