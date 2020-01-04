module Tile(
  input         clock,
  input         reset,
  input         io_host_fromhost_valid,
  input  [31:0] io_host_fromhost_bits,
  output [31:0] io_host_tohost,
  input         io_nasti_aw_ready,
  output        io_nasti_aw_valid,
  output [31:0] io_nasti_aw_bits_addr,
  output [7:0]  io_nasti_aw_bits_len,
  output [2:0]  io_nasti_aw_bits_size,
  output [1:0]  io_nasti_aw_bits_burst,
  output        io_nasti_aw_bits_lock,
  output [3:0]  io_nasti_aw_bits_cache,
  output [2:0]  io_nasti_aw_bits_prot,
  output [3:0]  io_nasti_aw_bits_qos,
  output [3:0]  io_nasti_aw_bits_region,
  output [4:0]  io_nasti_aw_bits_id,
  output        io_nasti_aw_bits_user,
  input         io_nasti_w_ready,
  output        io_nasti_w_valid,
  output [63:0] io_nasti_w_bits_data,
  output        io_nasti_w_bits_last,
  output [4:0]  io_nasti_w_bits_id,
  output [7:0]  io_nasti_w_bits_strb,
  output        io_nasti_w_bits_user,
  output        io_nasti_b_ready,
  input         io_nasti_b_valid,
  input  [1:0]  io_nasti_b_bits_resp,
  input  [4:0]  io_nasti_b_bits_id,
  input         io_nasti_b_bits_user,
  input         io_nasti_ar_ready,
  output        io_nasti_ar_valid,
  output [31:0] io_nasti_ar_bits_addr,
  output [7:0]  io_nasti_ar_bits_len,
  output [2:0]  io_nasti_ar_bits_size,
  output [1:0]  io_nasti_ar_bits_burst,
  output        io_nasti_ar_bits_lock,
  output [3:0]  io_nasti_ar_bits_cache,
  output [2:0]  io_nasti_ar_bits_prot,
  output [3:0]  io_nasti_ar_bits_qos,
  output [3:0]  io_nasti_ar_bits_region,
  output [4:0]  io_nasti_ar_bits_id,
  output        io_nasti_ar_bits_user,
  output        io_nasti_r_ready,
  input         io_nasti_r_valid,
  input  [1:0]  io_nasti_r_bits_resp,
  input  [63:0] io_nasti_r_bits_data,
  input         io_nasti_r_bits_last,
  input  [4:0]  io_nasti_r_bits_id,
  input         io_nasti_r_bits_user
);
  wire  core_clock; // @[Tile.scala 107:22]
  wire  core_reset; // @[Tile.scala 107:22]
  wire  core_io_host_fromhost_valid; // @[Tile.scala 107:22]
  wire [31:0] core_io_host_fromhost_bits; // @[Tile.scala 107:22]
  wire [31:0] core_io_host_tohost; // @[Tile.scala 107:22]
  wire  core_io_icache_req_valid; // @[Tile.scala 107:22]
  wire [31:0] core_io_icache_req_bits_addr; // @[Tile.scala 107:22]
  wire  core_io_icache_resp_valid; // @[Tile.scala 107:22]
  wire [31:0] core_io_icache_resp_bits_data; // @[Tile.scala 107:22]
  wire  core_io_dcache_abort; // @[Tile.scala 107:22]
  wire  core_io_dcache_req_valid; // @[Tile.scala 107:22]
  wire [31:0] core_io_dcache_req_bits_addr; // @[Tile.scala 107:22]
  wire [31:0] core_io_dcache_req_bits_data; // @[Tile.scala 107:22]
  wire [3:0] core_io_dcache_req_bits_mask; // @[Tile.scala 107:22]
  wire  core_io_dcache_resp_valid; // @[Tile.scala 107:22]
  wire [31:0] core_io_dcache_resp_bits_data; // @[Tile.scala 107:22]
  wire  icache_clock; // @[Tile.scala 108:22]
  wire  icache_reset; // @[Tile.scala 108:22]
  wire  icache_io_cpu_abort; // @[Tile.scala 108:22]
  wire  icache_io_cpu_req_valid; // @[Tile.scala 108:22]
  wire [31:0] icache_io_cpu_req_bits_addr; // @[Tile.scala 108:22]
  wire [31:0] icache_io_cpu_req_bits_data; // @[Tile.scala 108:22]
  wire [3:0] icache_io_cpu_req_bits_mask; // @[Tile.scala 108:22]
  wire  icache_io_cpu_resp_valid; // @[Tile.scala 108:22]
  wire [31:0] icache_io_cpu_resp_bits_data; // @[Tile.scala 108:22]
  wire  icache_io_nasti_aw_ready; // @[Tile.scala 108:22]
  wire  icache_io_nasti_aw_valid; // @[Tile.scala 108:22]
  wire [31:0] icache_io_nasti_aw_bits_addr; // @[Tile.scala 108:22]
  wire  icache_io_nasti_w_ready; // @[Tile.scala 108:22]
  wire  icache_io_nasti_w_valid; // @[Tile.scala 108:22]
  wire [63:0] icache_io_nasti_w_bits_data; // @[Tile.scala 108:22]
  wire  icache_io_nasti_w_bits_last; // @[Tile.scala 108:22]
  wire  icache_io_nasti_b_ready; // @[Tile.scala 108:22]
  wire  icache_io_nasti_b_valid; // @[Tile.scala 108:22]
  wire  icache_io_nasti_ar_ready; // @[Tile.scala 108:22]
  wire  icache_io_nasti_ar_valid; // @[Tile.scala 108:22]
  wire [31:0] icache_io_nasti_ar_bits_addr; // @[Tile.scala 108:22]
  wire  icache_io_nasti_r_ready; // @[Tile.scala 108:22]
  wire  icache_io_nasti_r_valid; // @[Tile.scala 108:22]
  wire [63:0] icache_io_nasti_r_bits_data; // @[Tile.scala 108:22]
  wire  dcache_clock; // @[Tile.scala 109:22]
  wire  dcache_reset; // @[Tile.scala 109:22]
  wire  dcache_io_cpu_abort; // @[Tile.scala 109:22]
  wire  dcache_io_cpu_req_valid; // @[Tile.scala 109:22]
  wire [31:0] dcache_io_cpu_req_bits_addr; // @[Tile.scala 109:22]
  wire [31:0] dcache_io_cpu_req_bits_data; // @[Tile.scala 109:22]
  wire [3:0] dcache_io_cpu_req_bits_mask; // @[Tile.scala 109:22]
  wire  dcache_io_cpu_resp_valid; // @[Tile.scala 109:22]
  wire [31:0] dcache_io_cpu_resp_bits_data; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_aw_ready; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_aw_valid; // @[Tile.scala 109:22]
  wire [31:0] dcache_io_nasti_aw_bits_addr; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_w_ready; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_w_valid; // @[Tile.scala 109:22]
  wire [63:0] dcache_io_nasti_w_bits_data; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_w_bits_last; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_b_ready; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_b_valid; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_ar_ready; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_ar_valid; // @[Tile.scala 109:22]
  wire [31:0] dcache_io_nasti_ar_bits_addr; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_r_ready; // @[Tile.scala 109:22]
  wire  dcache_io_nasti_r_valid; // @[Tile.scala 109:22]
  wire [63:0] dcache_io_nasti_r_bits_data; // @[Tile.scala 109:22]
  wire  arb_clock; // @[Tile.scala 110:22]
  wire  arb_reset; // @[Tile.scala 110:22]
  wire  arb_io_icache_ar_ready; // @[Tile.scala 110:22]
  wire  arb_io_icache_ar_valid; // @[Tile.scala 110:22]
  wire [31:0] arb_io_icache_ar_bits_addr; // @[Tile.scala 110:22]
  wire  arb_io_icache_r_ready; // @[Tile.scala 110:22]
  wire  arb_io_icache_r_valid; // @[Tile.scala 110:22]
  wire [63:0] arb_io_icache_r_bits_data; // @[Tile.scala 110:22]
  wire  arb_io_dcache_aw_ready; // @[Tile.scala 110:22]
  wire  arb_io_dcache_aw_valid; // @[Tile.scala 110:22]
  wire [31:0] arb_io_dcache_aw_bits_addr; // @[Tile.scala 110:22]
  wire  arb_io_dcache_w_ready; // @[Tile.scala 110:22]
  wire  arb_io_dcache_w_valid; // @[Tile.scala 110:22]
  wire [63:0] arb_io_dcache_w_bits_data; // @[Tile.scala 110:22]
  wire  arb_io_dcache_w_bits_last; // @[Tile.scala 110:22]
  wire  arb_io_dcache_b_ready; // @[Tile.scala 110:22]
  wire  arb_io_dcache_b_valid; // @[Tile.scala 110:22]
  wire  arb_io_dcache_ar_ready; // @[Tile.scala 110:22]
  wire  arb_io_dcache_ar_valid; // @[Tile.scala 110:22]
  wire [31:0] arb_io_dcache_ar_bits_addr; // @[Tile.scala 110:22]
  wire  arb_io_dcache_r_ready; // @[Tile.scala 110:22]
  wire  arb_io_dcache_r_valid; // @[Tile.scala 110:22]
  wire [63:0] arb_io_dcache_r_bits_data; // @[Tile.scala 110:22]
  wire  arb_io_nasti_aw_ready; // @[Tile.scala 110:22]
  wire  arb_io_nasti_aw_valid; // @[Tile.scala 110:22]
  wire [31:0] arb_io_nasti_aw_bits_addr; // @[Tile.scala 110:22]
  wire  arb_io_nasti_w_ready; // @[Tile.scala 110:22]
  wire  arb_io_nasti_w_valid; // @[Tile.scala 110:22]
  wire [63:0] arb_io_nasti_w_bits_data; // @[Tile.scala 110:22]
  wire  arb_io_nasti_w_bits_last; // @[Tile.scala 110:22]
  wire  arb_io_nasti_b_ready; // @[Tile.scala 110:22]
  wire  arb_io_nasti_b_valid; // @[Tile.scala 110:22]
  wire  arb_io_nasti_ar_ready; // @[Tile.scala 110:22]
  wire  arb_io_nasti_ar_valid; // @[Tile.scala 110:22]
  wire [31:0] arb_io_nasti_ar_bits_addr; // @[Tile.scala 110:22]
  wire  arb_io_nasti_r_ready; // @[Tile.scala 110:22]
  wire  arb_io_nasti_r_valid; // @[Tile.scala 110:22]
  wire [63:0] arb_io_nasti_r_bits_data; // @[Tile.scala 110:22]
  wire  arb_io_nasti_r_bits_last; // @[Tile.scala 110:22]
  Core core ( // @[Tile.scala 107:22]
    .clock(core_clock),
    .reset(core_reset),
    .io_host_fromhost_valid(core_io_host_fromhost_valid),
    .io_host_fromhost_bits(core_io_host_fromhost_bits),
    .io_host_tohost(core_io_host_tohost),
    .io_icache_req_valid(core_io_icache_req_valid),
    .io_icache_req_bits_addr(core_io_icache_req_bits_addr),
    .io_icache_resp_valid(core_io_icache_resp_valid),
    .io_icache_resp_bits_data(core_io_icache_resp_bits_data),
    .io_dcache_abort(core_io_dcache_abort),
    .io_dcache_req_valid(core_io_dcache_req_valid),
    .io_dcache_req_bits_addr(core_io_dcache_req_bits_addr),
    .io_dcache_req_bits_data(core_io_dcache_req_bits_data),
    .io_dcache_req_bits_mask(core_io_dcache_req_bits_mask),
    .io_dcache_resp_valid(core_io_dcache_resp_valid),
    .io_dcache_resp_bits_data(core_io_dcache_resp_bits_data)
  );
  Cache icache ( // @[Tile.scala 108:22]
    .clock(icache_clock),
    .reset(icache_reset),
    .io_cpu_abort(icache_io_cpu_abort),
    .io_cpu_req_valid(icache_io_cpu_req_valid),
    .io_cpu_req_bits_addr(icache_io_cpu_req_bits_addr),
    .io_cpu_req_bits_data(icache_io_cpu_req_bits_data),
    .io_cpu_req_bits_mask(icache_io_cpu_req_bits_mask),
    .io_cpu_resp_valid(icache_io_cpu_resp_valid),
    .io_cpu_resp_bits_data(icache_io_cpu_resp_bits_data),
    .io_nasti_aw_ready(icache_io_nasti_aw_ready),
    .io_nasti_aw_valid(icache_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(icache_io_nasti_aw_bits_addr),
    .io_nasti_w_ready(icache_io_nasti_w_ready),
    .io_nasti_w_valid(icache_io_nasti_w_valid),
    .io_nasti_w_bits_data(icache_io_nasti_w_bits_data),
    .io_nasti_w_bits_last(icache_io_nasti_w_bits_last),
    .io_nasti_b_ready(icache_io_nasti_b_ready),
    .io_nasti_b_valid(icache_io_nasti_b_valid),
    .io_nasti_ar_ready(icache_io_nasti_ar_ready),
    .io_nasti_ar_valid(icache_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(icache_io_nasti_ar_bits_addr),
    .io_nasti_r_ready(icache_io_nasti_r_ready),
    .io_nasti_r_valid(icache_io_nasti_r_valid),
    .io_nasti_r_bits_data(icache_io_nasti_r_bits_data)
  );
  Cache dcache ( // @[Tile.scala 109:22]
    .clock(dcache_clock),
    .reset(dcache_reset),
    .io_cpu_abort(dcache_io_cpu_abort),
    .io_cpu_req_valid(dcache_io_cpu_req_valid),
    .io_cpu_req_bits_addr(dcache_io_cpu_req_bits_addr),
    .io_cpu_req_bits_data(dcache_io_cpu_req_bits_data),
    .io_cpu_req_bits_mask(dcache_io_cpu_req_bits_mask),
    .io_cpu_resp_valid(dcache_io_cpu_resp_valid),
    .io_cpu_resp_bits_data(dcache_io_cpu_resp_bits_data),
    .io_nasti_aw_ready(dcache_io_nasti_aw_ready),
    .io_nasti_aw_valid(dcache_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(dcache_io_nasti_aw_bits_addr),
    .io_nasti_w_ready(dcache_io_nasti_w_ready),
    .io_nasti_w_valid(dcache_io_nasti_w_valid),
    .io_nasti_w_bits_data(dcache_io_nasti_w_bits_data),
    .io_nasti_w_bits_last(dcache_io_nasti_w_bits_last),
    .io_nasti_b_ready(dcache_io_nasti_b_ready),
    .io_nasti_b_valid(dcache_io_nasti_b_valid),
    .io_nasti_ar_ready(dcache_io_nasti_ar_ready),
    .io_nasti_ar_valid(dcache_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(dcache_io_nasti_ar_bits_addr),
    .io_nasti_r_ready(dcache_io_nasti_r_ready),
    .io_nasti_r_valid(dcache_io_nasti_r_valid),
    .io_nasti_r_bits_data(dcache_io_nasti_r_bits_data)
  );
  MemArbiter arb ( // @[Tile.scala 110:22]
    .clock(arb_clock),
    .reset(arb_reset),
    .io_icache_ar_ready(arb_io_icache_ar_ready),
    .io_icache_ar_valid(arb_io_icache_ar_valid),
    .io_icache_ar_bits_addr(arb_io_icache_ar_bits_addr),
    .io_icache_r_ready(arb_io_icache_r_ready),
    .io_icache_r_valid(arb_io_icache_r_valid),
    .io_icache_r_bits_data(arb_io_icache_r_bits_data),
    .io_dcache_aw_ready(arb_io_dcache_aw_ready),
    .io_dcache_aw_valid(arb_io_dcache_aw_valid),
    .io_dcache_aw_bits_addr(arb_io_dcache_aw_bits_addr),
    .io_dcache_w_ready(arb_io_dcache_w_ready),
    .io_dcache_w_valid(arb_io_dcache_w_valid),
    .io_dcache_w_bits_data(arb_io_dcache_w_bits_data),
    .io_dcache_w_bits_last(arb_io_dcache_w_bits_last),
    .io_dcache_b_ready(arb_io_dcache_b_ready),
    .io_dcache_b_valid(arb_io_dcache_b_valid),
    .io_dcache_ar_ready(arb_io_dcache_ar_ready),
    .io_dcache_ar_valid(arb_io_dcache_ar_valid),
    .io_dcache_ar_bits_addr(arb_io_dcache_ar_bits_addr),
    .io_dcache_r_ready(arb_io_dcache_r_ready),
    .io_dcache_r_valid(arb_io_dcache_r_valid),
    .io_dcache_r_bits_data(arb_io_dcache_r_bits_data),
    .io_nasti_aw_ready(arb_io_nasti_aw_ready),
    .io_nasti_aw_valid(arb_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(arb_io_nasti_aw_bits_addr),
    .io_nasti_w_ready(arb_io_nasti_w_ready),
    .io_nasti_w_valid(arb_io_nasti_w_valid),
    .io_nasti_w_bits_data(arb_io_nasti_w_bits_data),
    .io_nasti_w_bits_last(arb_io_nasti_w_bits_last),
    .io_nasti_b_ready(arb_io_nasti_b_ready),
    .io_nasti_b_valid(arb_io_nasti_b_valid),
    .io_nasti_ar_ready(arb_io_nasti_ar_ready),
    .io_nasti_ar_valid(arb_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(arb_io_nasti_ar_bits_addr),
    .io_nasti_r_ready(arb_io_nasti_r_ready),
    .io_nasti_r_valid(arb_io_nasti_r_valid),
    .io_nasti_r_bits_data(arb_io_nasti_r_bits_data),
    .io_nasti_r_bits_last(arb_io_nasti_r_bits_last)
  );
  assign io_host_tohost = core_io_host_tohost; // @[Tile.scala 112:11]
  assign io_nasti_aw_valid = arb_io_nasti_aw_valid; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_addr = arb_io_nasti_aw_bits_addr; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_len = 8'h1; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_size = 3'h3; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_burst = 2'h1; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_lock = 1'h0; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_cache = 4'h0; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_prot = 3'h0; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_qos = 4'h0; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_region = 4'h0; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_id = 5'h0; // @[Tile.scala 117:12]
  assign io_nasti_aw_bits_user = 1'h0; // @[Tile.scala 117:12]
  assign io_nasti_w_valid = arb_io_nasti_w_valid; // @[Tile.scala 117:12]
  assign io_nasti_w_bits_data = arb_io_nasti_w_bits_data; // @[Tile.scala 117:12]
  assign io_nasti_w_bits_last = arb_io_nasti_w_bits_last; // @[Tile.scala 117:12]
  assign io_nasti_w_bits_id = 5'h0; // @[Tile.scala 117:12]
  assign io_nasti_w_bits_strb = 8'hff; // @[Tile.scala 117:12]
  assign io_nasti_w_bits_user = 1'h0; // @[Tile.scala 117:12]
  assign io_nasti_b_ready = arb_io_nasti_b_ready; // @[Tile.scala 117:12]
  assign io_nasti_ar_valid = arb_io_nasti_ar_valid; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_addr = arb_io_nasti_ar_bits_addr; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_len = 8'h1; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_size = 3'h3; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_burst = 2'h1; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_lock = 1'h0; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_cache = 4'h0; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_prot = 3'h0; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_qos = 4'h0; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_region = 4'h0; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_id = 5'h0; // @[Tile.scala 117:12]
  assign io_nasti_ar_bits_user = 1'h0; // @[Tile.scala 117:12]
  assign io_nasti_r_ready = arb_io_nasti_r_ready; // @[Tile.scala 117:12]
  assign core_clock = clock;
  assign core_reset = reset;
  assign core_io_host_fromhost_valid = io_host_fromhost_valid; // @[Tile.scala 112:11]
  assign core_io_host_fromhost_bits = io_host_fromhost_bits; // @[Tile.scala 112:11]
  assign core_io_icache_resp_valid = icache_io_cpu_resp_valid; // @[Tile.scala 113:18]
  assign core_io_icache_resp_bits_data = icache_io_cpu_resp_bits_data; // @[Tile.scala 113:18]
  assign core_io_dcache_resp_valid = dcache_io_cpu_resp_valid; // @[Tile.scala 114:18]
  assign core_io_dcache_resp_bits_data = dcache_io_cpu_resp_bits_data; // @[Tile.scala 114:18]
  assign icache_clock = clock;
  assign icache_reset = reset;
  assign icache_io_cpu_abort = 1'h0; // @[Tile.scala 113:18]
  assign icache_io_cpu_req_valid = core_io_icache_req_valid; // @[Tile.scala 113:18]
  assign icache_io_cpu_req_bits_addr = core_io_icache_req_bits_addr; // @[Tile.scala 113:18]
  assign icache_io_cpu_req_bits_data = 32'h0; // @[Tile.scala 113:18]
  assign icache_io_cpu_req_bits_mask = 4'h0; // @[Tile.scala 113:18]
  assign icache_io_nasti_aw_ready = 1'h0; // @[Tile.scala 115:17]
  assign icache_io_nasti_w_ready = 1'h0; // @[Tile.scala 115:17]
  assign icache_io_nasti_b_valid = 1'h0; // @[Tile.scala 115:17]
  assign icache_io_nasti_ar_ready = arb_io_icache_ar_ready; // @[Tile.scala 115:17]
  assign icache_io_nasti_r_valid = arb_io_icache_r_valid; // @[Tile.scala 115:17]
  assign icache_io_nasti_r_bits_data = arb_io_icache_r_bits_data; // @[Tile.scala 115:17]
  assign dcache_clock = clock;
  assign dcache_reset = reset;
  assign dcache_io_cpu_abort = core_io_dcache_abort; // @[Tile.scala 114:18]
  assign dcache_io_cpu_req_valid = core_io_dcache_req_valid; // @[Tile.scala 114:18]
  assign dcache_io_cpu_req_bits_addr = core_io_dcache_req_bits_addr; // @[Tile.scala 114:18]
  assign dcache_io_cpu_req_bits_data = core_io_dcache_req_bits_data; // @[Tile.scala 114:18]
  assign dcache_io_cpu_req_bits_mask = core_io_dcache_req_bits_mask; // @[Tile.scala 114:18]
  assign dcache_io_nasti_aw_ready = arb_io_dcache_aw_ready; // @[Tile.scala 116:17]
  assign dcache_io_nasti_w_ready = arb_io_dcache_w_ready; // @[Tile.scala 116:17]
  assign dcache_io_nasti_b_valid = arb_io_dcache_b_valid; // @[Tile.scala 116:17]
  assign dcache_io_nasti_ar_ready = arb_io_dcache_ar_ready; // @[Tile.scala 116:17]
  assign dcache_io_nasti_r_valid = arb_io_dcache_r_valid; // @[Tile.scala 116:17]
  assign dcache_io_nasti_r_bits_data = arb_io_dcache_r_bits_data; // @[Tile.scala 116:17]
  assign arb_clock = clock;
  assign arb_reset = reset;
  assign arb_io_icache_ar_valid = icache_io_nasti_ar_valid; // @[Tile.scala 115:17]
  assign arb_io_icache_ar_bits_addr = icache_io_nasti_ar_bits_addr; // @[Tile.scala 115:17]
  assign arb_io_icache_r_ready = icache_io_nasti_r_ready; // @[Tile.scala 115:17]
  assign arb_io_dcache_aw_valid = dcache_io_nasti_aw_valid; // @[Tile.scala 116:17]
  assign arb_io_dcache_aw_bits_addr = dcache_io_nasti_aw_bits_addr; // @[Tile.scala 116:17]
  assign arb_io_dcache_w_valid = dcache_io_nasti_w_valid; // @[Tile.scala 116:17]
  assign arb_io_dcache_w_bits_data = dcache_io_nasti_w_bits_data; // @[Tile.scala 116:17]
  assign arb_io_dcache_w_bits_last = dcache_io_nasti_w_bits_last; // @[Tile.scala 116:17]
  assign arb_io_dcache_b_ready = dcache_io_nasti_b_ready; // @[Tile.scala 116:17]
  assign arb_io_dcache_ar_valid = dcache_io_nasti_ar_valid; // @[Tile.scala 116:17]
  assign arb_io_dcache_ar_bits_addr = dcache_io_nasti_ar_bits_addr; // @[Tile.scala 116:17]
  assign arb_io_dcache_r_ready = dcache_io_nasti_r_ready; // @[Tile.scala 116:17]
  assign arb_io_nasti_aw_ready = io_nasti_aw_ready; // @[Tile.scala 117:12]
  assign arb_io_nasti_w_ready = io_nasti_w_ready; // @[Tile.scala 117:12]
  assign arb_io_nasti_b_valid = io_nasti_b_valid; // @[Tile.scala 117:12]
  assign arb_io_nasti_ar_ready = io_nasti_ar_ready; // @[Tile.scala 117:12]
  assign arb_io_nasti_r_valid = io_nasti_r_valid; // @[Tile.scala 117:12]
  assign arb_io_nasti_r_bits_data = io_nasti_r_bits_data; // @[Tile.scala 117:12]
  assign arb_io_nasti_r_bits_last = io_nasti_r_bits_last; // @[Tile.scala 117:12]
endmodule
