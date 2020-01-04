module MemArbiter(
  input         clock,
  input         reset,
  output        io_icache_ar_ready,
  input         io_icache_ar_valid,
  input  [31:0] io_icache_ar_bits_addr,
  input         io_icache_r_ready,
  output        io_icache_r_valid,
  output [63:0] io_icache_r_bits_data,
  output        io_dcache_aw_ready,
  input         io_dcache_aw_valid,
  input  [31:0] io_dcache_aw_bits_addr,
  output        io_dcache_w_ready,
  input         io_dcache_w_valid,
  input  [63:0] io_dcache_w_bits_data,
  input         io_dcache_w_bits_last,
  input         io_dcache_b_ready,
  output        io_dcache_b_valid,
  output        io_dcache_ar_ready,
  input         io_dcache_ar_valid,
  input  [31:0] io_dcache_ar_bits_addr,
  input         io_dcache_r_ready,
  output        io_dcache_r_valid,
  output [63:0] io_dcache_r_bits_data,
  input         io_nasti_aw_ready,
  output        io_nasti_aw_valid,
  output [31:0] io_nasti_aw_bits_addr,
  input         io_nasti_w_ready,
  output        io_nasti_w_valid,
  output [63:0] io_nasti_w_bits_data,
  output        io_nasti_w_bits_last,
  output        io_nasti_b_ready,
  input         io_nasti_b_valid,
  input         io_nasti_ar_ready,
  output        io_nasti_ar_valid,
  output [31:0] io_nasti_ar_bits_addr,
  output        io_nasti_r_ready,
  input         io_nasti_r_valid,
  input  [63:0] io_nasti_r_bits_data,
  input         io_nasti_r_bits_last
);
  reg [2:0] state; // @[Tile.scala 21:22]
  reg [31:0] _RAND_0;
  wire  _T; // @[Tile.scala 25:52]
  wire  _T_4; // @[Tile.scala 31:50]
  wire  _T_8; // @[Tile.scala 37:50]
  wire  _T_19; // @[Tile.scala 47:44]
  wire  _T_20; // @[Tile.scala 48:5]
  wire  _T_21; // @[Tile.scala 47:67]
  wire  _T_25; // @[Tile.scala 49:43]
  wire  _T_28; // @[Tile.scala 50:47]
  wire  _T_30; // @[Tile.scala 55:50]
  wire  _T_32; // @[Tile.scala 56:50]
  wire  _T_35; // @[Tile.scala 57:41]
  wire  _T_37; // @[Tile.scala 58:41]
  wire  _T_39; // @[Conditional.scala 37:30]
  wire  _T_40; // @[Decoupled.scala 40:37]
  wire  _T_41; // @[Decoupled.scala 40:37]
  wire  _T_42; // @[Decoupled.scala 40:37]
  wire  _T_43; // @[Conditional.scala 37:30]
  wire  _T_44; // @[Decoupled.scala 40:37]
  wire  _T_45; // @[Tile.scala 71:30]
  wire  _T_46; // @[Conditional.scala 37:30]
  wire  _T_49; // @[Conditional.scala 37:30]
  wire  _T_50; // @[Decoupled.scala 40:37]
  wire  _T_51; // @[Tile.scala 81:31]
  wire  _T_52; // @[Conditional.scala 37:30]
  wire  _T_53; // @[Decoupled.scala 40:37]
  assign _T = state == 3'h0; // @[Tile.scala 25:52]
  assign _T_4 = state == 3'h3; // @[Tile.scala 31:50]
  assign _T_8 = state == 3'h4; // @[Tile.scala 37:50]
  assign _T_19 = io_icache_ar_valid | io_dcache_ar_valid; // @[Tile.scala 47:44]
  assign _T_20 = io_nasti_aw_valid == 1'h0; // @[Tile.scala 48:5]
  assign _T_21 = _T_19 & _T_20; // @[Tile.scala 47:67]
  assign _T_25 = io_nasti_ar_ready & _T_20; // @[Tile.scala 49:43]
  assign _T_28 = io_dcache_ar_valid == 1'h0; // @[Tile.scala 50:47]
  assign _T_30 = state == 3'h1; // @[Tile.scala 55:50]
  assign _T_32 = state == 3'h2; // @[Tile.scala 56:50]
  assign _T_35 = io_icache_r_ready & _T_30; // @[Tile.scala 57:41]
  assign _T_37 = io_dcache_r_ready & _T_32; // @[Tile.scala 58:41]
  assign _T_39 = 3'h0 == state; // @[Conditional.scala 37:30]
  assign _T_40 = io_dcache_aw_ready & io_dcache_aw_valid; // @[Decoupled.scala 40:37]
  assign _T_41 = io_dcache_ar_ready & io_dcache_ar_valid; // @[Decoupled.scala 40:37]
  assign _T_42 = io_icache_ar_ready & io_icache_ar_valid; // @[Decoupled.scala 40:37]
  assign _T_43 = 3'h1 == state; // @[Conditional.scala 37:30]
  assign _T_44 = io_nasti_r_ready & io_nasti_r_valid; // @[Decoupled.scala 40:37]
  assign _T_45 = _T_44 & io_nasti_r_bits_last; // @[Tile.scala 71:30]
  assign _T_46 = 3'h2 == state; // @[Conditional.scala 37:30]
  assign _T_49 = 3'h3 == state; // @[Conditional.scala 37:30]
  assign _T_50 = io_dcache_w_ready & io_dcache_w_valid; // @[Decoupled.scala 40:37]
  assign _T_51 = _T_50 & io_dcache_w_bits_last; // @[Tile.scala 81:31]
  assign _T_52 = 3'h4 == state; // @[Conditional.scala 37:30]
  assign _T_53 = io_nasti_b_ready & io_nasti_b_valid; // @[Decoupled.scala 40:37]
  assign io_icache_ar_ready = io_dcache_ar_ready & _T_28; // @[Tile.scala 50:22]
  assign io_icache_r_valid = io_nasti_r_valid & _T_30; // @[Tile.scala 55:21]
  assign io_icache_r_bits_data = io_nasti_r_bits_data; // @[Tile.scala 53:21]
  assign io_dcache_aw_ready = io_nasti_aw_ready & _T; // @[Tile.scala 26:22]
  assign io_dcache_w_ready = io_nasti_w_ready & _T_4; // @[Tile.scala 32:21]
  assign io_dcache_b_valid = io_nasti_b_valid & _T_8; // @[Tile.scala 37:21]
  assign io_dcache_ar_ready = _T_25 & _T; // @[Tile.scala 49:22]
  assign io_dcache_r_valid = io_nasti_r_valid & _T_32; // @[Tile.scala 56:21]
  assign io_dcache_r_bits_data = io_nasti_r_bits_data; // @[Tile.scala 54:21]
  assign io_nasti_aw_valid = io_dcache_aw_valid & _T; // @[Tile.scala 25:21]
  assign io_nasti_aw_bits_addr = io_dcache_aw_bits_addr; // @[Tile.scala 24:20]
  assign io_nasti_w_valid = io_dcache_w_valid & _T_4; // @[Tile.scala 31:20]
  assign io_nasti_w_bits_data = io_dcache_w_bits_data; // @[Tile.scala 30:20]
  assign io_nasti_w_bits_last = io_dcache_w_bits_last; // @[Tile.scala 30:20]
  assign io_nasti_b_ready = io_dcache_b_ready & _T_8; // @[Tile.scala 38:20]
  assign io_nasti_ar_valid = _T_21 & _T; // @[Tile.scala 47:21]
  assign io_nasti_ar_bits_addr = io_dcache_ar_valid ? io_dcache_ar_bits_addr : io_icache_ar_bits_addr; // @[Tile.scala 42:20]
  assign io_nasti_r_ready = _T_35 | _T_37; // @[Tile.scala 57:20]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  state = _RAND_0[2:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      state <= 3'h0;
    end else if (_T_39) begin
      if (_T_40) begin
        state <= 3'h3;
      end else if (_T_41) begin
        state <= 3'h2;
      end else if (_T_42) begin
        state <= 3'h1;
      end
    end else if (_T_43) begin
      if (_T_45) begin
        state <= 3'h0;
      end
    end else if (_T_46) begin
      if (_T_45) begin
        state <= 3'h0;
      end
    end else if (_T_49) begin
      if (_T_51) begin
        state <= 3'h4;
      end
    end else if (_T_52) begin
      if (_T_53) begin
        state <= 3'h0;
      end
    end
  end
endmodule
