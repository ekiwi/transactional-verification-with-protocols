module RegFile(
  input         clock,
  input  [4:0]  io_raddr1,
  input  [4:0]  io_raddr2,
  output [31:0] io_rdata1,
  output [31:0] io_rdata2,
  input         io_wen,
  input  [4:0]  io_waddr,
  input  [31:0] io_wdata
);
  reg [31:0] regs [0:31]; // @[RegFile.scala 20:17]
  reg [31:0] _RAND_0;
  wire [31:0] regs__T_1_data; // @[RegFile.scala 20:17]
  wire [4:0] regs__T_1_addr; // @[RegFile.scala 20:17]
  wire [31:0] regs__T_4_data; // @[RegFile.scala 20:17]
  wire [4:0] regs__T_4_addr; // @[RegFile.scala 20:17]
  wire [31:0] regs__T_8_data; // @[RegFile.scala 20:17]
  wire [4:0] regs__T_8_addr; // @[RegFile.scala 20:17]
  wire  regs__T_8_mask; // @[RegFile.scala 20:17]
  wire  regs__T_8_en; // @[RegFile.scala 20:17]
  wire  _T; // @[RegFile.scala 21:30]
  wire  _T_3; // @[RegFile.scala 22:30]
  wire  _T_6; // @[RegFile.scala 23:26]
  assign regs__T_1_addr = io_raddr1;
  assign regs__T_1_data = regs[regs__T_1_addr]; // @[RegFile.scala 20:17]
  assign regs__T_4_addr = io_raddr2;
  assign regs__T_4_data = regs[regs__T_4_addr]; // @[RegFile.scala 20:17]
  assign regs__T_8_data = io_wdata;
  assign regs__T_8_addr = io_waddr;
  assign regs__T_8_mask = 1'h1;
  assign regs__T_8_en = io_wen & _T_6;
  assign _T = io_raddr1 != 5'h0; // @[RegFile.scala 21:30]
  assign _T_3 = io_raddr2 != 5'h0; // @[RegFile.scala 22:30]
  assign _T_6 = io_waddr != 5'h0; // @[RegFile.scala 23:26]
  assign io_rdata1 = _T ? regs__T_1_data : 32'h0; // @[RegFile.scala 21:13]
  assign io_rdata2 = _T_3 ? regs__T_4_data : 32'h0; // @[RegFile.scala 22:13]
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
  _RAND_0 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 32; initvar = initvar+1)
    regs[initvar] = _RAND_0[31:0];
  `endif // RANDOMIZE_MEM_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if(regs__T_8_en & regs__T_8_mask) begin
      regs[regs__T_8_addr] <= regs__T_8_data; // @[RegFile.scala 20:17]
    end
  end
endmodule
