module Datapath(
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
  input  [31:0] io_dcache_resp_bits_data,
  output [31:0] io_ctrl_inst,
  input  [1:0]  io_ctrl_pc_sel,
  input         io_ctrl_inst_kill,
  input         io_ctrl_A_sel,
  input         io_ctrl_B_sel,
  input  [2:0]  io_ctrl_imm_sel,
  input  [3:0]  io_ctrl_alu_op,
  input  [2:0]  io_ctrl_br_type,
  input  [1:0]  io_ctrl_st_type,
  input  [2:0]  io_ctrl_ld_type,
  input  [1:0]  io_ctrl_wb_sel,
  input         io_ctrl_wb_en,
  input  [2:0]  io_ctrl_csr_cmd,
  input         io_ctrl_illegal
);
  wire  csr_clock; // @[Datapath.scala 23:23]
  wire  csr_reset; // @[Datapath.scala 23:23]
  wire  csr_io_stall; // @[Datapath.scala 23:23]
  wire [2:0] csr_io_cmd; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_in; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_out; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_pc; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_addr; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_inst; // @[Datapath.scala 23:23]
  wire  csr_io_illegal; // @[Datapath.scala 23:23]
  wire [1:0] csr_io_st_type; // @[Datapath.scala 23:23]
  wire [2:0] csr_io_ld_type; // @[Datapath.scala 23:23]
  wire  csr_io_pc_check; // @[Datapath.scala 23:23]
  wire  csr_io_expt; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_evec; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_epc; // @[Datapath.scala 23:23]
  wire  csr_io_host_fromhost_valid; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_host_fromhost_bits; // @[Datapath.scala 23:23]
  wire [31:0] csr_io_host_tohost; // @[Datapath.scala 23:23]
  wire  regFile_clock; // @[Datapath.scala 24:23]
  wire [4:0] regFile_io_raddr1; // @[Datapath.scala 24:23]
  wire [4:0] regFile_io_raddr2; // @[Datapath.scala 24:23]
  wire [31:0] regFile_io_rdata1; // @[Datapath.scala 24:23]
  wire [31:0] regFile_io_rdata2; // @[Datapath.scala 24:23]
  wire  regFile_io_wen; // @[Datapath.scala 24:23]
  wire [4:0] regFile_io_waddr; // @[Datapath.scala 24:23]
  wire [31:0] regFile_io_wdata; // @[Datapath.scala 24:23]
  wire [31:0] alu_io_A; // @[Config.scala 13:50]
  wire [31:0] alu_io_B; // @[Config.scala 13:50]
  wire [3:0] alu_io_alu_op; // @[Config.scala 13:50]
  wire [31:0] alu_io_out; // @[Config.scala 13:50]
  wire [31:0] alu_io_sum; // @[Config.scala 13:50]
  wire [31:0] immGen_io_inst; // @[Config.scala 14:50]
  wire [2:0] immGen_io_sel; // @[Config.scala 14:50]
  wire [31:0] immGen_io_out; // @[Config.scala 14:50]
  wire [31:0] brCond_io_rs1; // @[Config.scala 15:50]
  wire [31:0] brCond_io_rs2; // @[Config.scala 15:50]
  wire [2:0] brCond_io_br_type; // @[Config.scala 15:50]
  wire  brCond_io_taken; // @[Config.scala 15:50]
  reg [31:0] fe_inst; // @[Datapath.scala 32:24]
  reg [31:0] _RAND_0;
  reg [32:0] fe_pc; // @[Datapath.scala 33:20]
  reg [63:0] _RAND_1;
  reg [31:0] ew_inst; // @[Datapath.scala 36:24]
  reg [31:0] _RAND_2;
  reg [32:0] ew_pc; // @[Datapath.scala 37:20]
  reg [63:0] _RAND_3;
  reg [31:0] ew_alu; // @[Datapath.scala 38:20]
  reg [31:0] _RAND_4;
  reg [31:0] csr_in; // @[Datapath.scala 39:20]
  reg [31:0] _RAND_5;
  reg [1:0] st_type; // @[Datapath.scala 42:21]
  reg [31:0] _RAND_6;
  reg [2:0] ld_type; // @[Datapath.scala 43:21]
  reg [31:0] _RAND_7;
  reg [1:0] wb_sel; // @[Datapath.scala 44:21]
  reg [31:0] _RAND_8;
  reg  wb_en; // @[Datapath.scala 45:21]
  reg [31:0] _RAND_9;
  reg [2:0] csr_cmd; // @[Datapath.scala 46:21]
  reg [31:0] _RAND_10;
  reg  illegal; // @[Datapath.scala 47:21]
  reg [31:0] _RAND_11;
  reg  pc_check; // @[Datapath.scala 48:21]
  reg [31:0] _RAND_12;
  wire  _T; // @[Datapath.scala 51:31]
  reg  started; // @[Datapath.scala 51:24]
  reg [31:0] _RAND_13;
  wire  _T_1; // @[Datapath.scala 52:15]
  wire  _T_2; // @[Datapath.scala 52:40]
  wire  stall; // @[Datapath.scala 52:37]
  wire [31:0] _T_4; // @[Datapath.scala 53:47]
  reg [32:0] pc; // @[Datapath.scala 53:21]
  reg [63:0] _RAND_14;
  wire  _T_5; // @[Datapath.scala 55:33]
  wire  _T_6; // @[Datapath.scala 56:33]
  wire  _T_7; // @[Datapath.scala 56:44]
  wire [30:0] _GEN_24; // @[Datapath.scala 56:75]
  wire [31:0] _T_8; // @[Datapath.scala 56:75]
  wire [32:0] _T_9; // @[Datapath.scala 56:82]
  wire  _T_10; // @[Datapath.scala 57:33]
  wire [32:0] _T_12; // @[Datapath.scala 57:50]
  wire [32:0] _T_13; // @[Datapath.scala 57:17]
  wire [32:0] _T_14; // @[Datapath.scala 56:17]
  wire [32:0] _T_15; // @[Datapath.scala 55:17]
  wire [32:0] _T_16; // @[Datapath.scala 54:32]
  wire [32:0] npc; // @[Datapath.scala 54:17]
  wire  _T_17; // @[Datapath.scala 58:26]
  wire  _T_18; // @[Datapath.scala 58:47]
  wire  _T_19; // @[Datapath.scala 58:66]
  wire  _T_20; // @[Datapath.scala 63:30]
  wire [4:0] rs1_addr; // @[Datapath.scala 78:25]
  wire [4:0] rs2_addr; // @[Datapath.scala 79:25]
  wire [4:0] wb_rd_addr; // @[Datapath.scala 88:27]
  wire  _T_22; // @[Datapath.scala 89:37]
  wire  _T_23; // @[Datapath.scala 89:25]
  wire  _T_24; // @[Datapath.scala 89:54]
  wire  rs1hazard; // @[Datapath.scala 89:41]
  wire  _T_25; // @[Datapath.scala 90:37]
  wire  _T_26; // @[Datapath.scala 90:25]
  wire  _T_27; // @[Datapath.scala 90:54]
  wire  rs2hazard; // @[Datapath.scala 90:41]
  wire  _T_28; // @[Datapath.scala 91:24]
  wire  _T_29; // @[Datapath.scala 91:35]
  wire [31:0] rs1; // @[Datapath.scala 91:16]
  wire  _T_31; // @[Datapath.scala 92:35]
  wire [31:0] rs2; // @[Datapath.scala 92:16]
  wire [32:0] _T_33; // @[Datapath.scala 95:18]
  wire [31:0] _T_36; // @[Datapath.scala 105:20]
  wire [29:0] _GEN_25; // @[Datapath.scala 105:48]
  wire [31:0] _T_37; // @[Datapath.scala 105:48]
  wire [33:0] _GEN_26; // @[Datapath.scala 105:55]
  wire [34:0] daddr; // @[Datapath.scala 105:55]
  wire  _T_38; // @[Datapath.scala 106:28]
  wire [4:0] _GEN_27; // @[Datapath.scala 106:32]
  wire [7:0] _T_39; // @[Datapath.scala 106:32]
  wire  _T_40; // @[Datapath.scala 106:60]
  wire [3:0] _T_41; // @[Datapath.scala 106:64]
  wire [7:0] _GEN_28; // @[Datapath.scala 106:47]
  wire [7:0] woffset; // @[Datapath.scala 106:47]
  wire  _T_43; // @[Datapath.scala 107:57]
  wire  _T_44; // @[Datapath.scala 107:80]
  wire  _T_45; // @[Datapath.scala 107:61]
  wire [286:0] _GEN_29; // @[Datapath.scala 109:34]
  wire [286:0] _T_47; // @[Datapath.scala 109:34]
  wire [1:0] _T_48; // @[Datapath.scala 110:43]
  wire [1:0] _T_49; // @[Datapath.scala 113:36]
  wire [4:0] _T_50; // @[Datapath.scala 113:23]
  wire [3:0] _T_52; // @[Datapath.scala 114:23]
  wire  _T_53; // @[Mux.scala 80:60]
  wire [3:0] _T_54; // @[Mux.scala 80:57]
  wire  _T_55; // @[Mux.scala 80:60]
  wire [4:0] _T_56; // @[Mux.scala 80:57]
  wire  _T_57; // @[Mux.scala 80:60]
  wire [4:0] _T_58; // @[Mux.scala 80:57]
  wire  _T_61; // @[Datapath.scala 117:31]
  wire  _T_62; // @[Datapath.scala 117:21]
  wire  _T_64; // @[Datapath.scala 124:24]
  wire  _T_65; // @[Datapath.scala 124:21]
  wire  _T_66; // @[Datapath.scala 128:38]
  wire  _T_69; // @[Datapath.scala 139:24]
  wire [4:0] _GEN_30; // @[Datapath.scala 139:28]
  wire [7:0] _T_70; // @[Datapath.scala 139:28]
  wire  _T_71; // @[Datapath.scala 139:52]
  wire [3:0] _T_72; // @[Datapath.scala 139:56]
  wire [7:0] _GEN_31; // @[Datapath.scala 139:43]
  wire [7:0] loffset; // @[Datapath.scala 139:43]
  wire [31:0] lshift; // @[Datapath.scala 140:42]
  wire [32:0] _T_73; // @[Datapath.scala 141:61]
  wire [15:0] _T_74; // @[Datapath.scala 142:21]
  wire [15:0] _T_75; // @[Datapath.scala 142:29]
  wire [7:0] _T_76; // @[Datapath.scala 142:53]
  wire [7:0] _T_77; // @[Datapath.scala 142:60]
  wire [16:0] _T_79; // @[Datapath.scala 143:29]
  wire [8:0] _T_81; // @[Datapath.scala 143:60]
  wire  _T_82; // @[Mux.scala 80:60]
  wire [32:0] _T_83; // @[Mux.scala 80:57]
  wire  _T_84; // @[Mux.scala 80:60]
  wire [32:0] _T_85; // @[Mux.scala 80:57]
  wire  _T_86; // @[Mux.scala 80:60]
  wire [32:0] _T_87; // @[Mux.scala 80:57]
  wire  _T_88; // @[Mux.scala 80:60]
  wire [32:0] load; // @[Mux.scala 80:57]
  wire [32:0] _T_89; // @[Datapath.scala 159:43]
  wire [32:0] _T_91; // @[Datapath.scala 161:22]
  wire [33:0] _T_92; // @[Datapath.scala 161:29]
  wire [32:0] _T_93; // @[Datapath.scala 162:26]
  wire  _T_94; // @[Mux.scala 80:60]
  wire [32:0] _T_95; // @[Mux.scala 80:57]
  wire  _T_96; // @[Mux.scala 80:60]
  wire [33:0] _T_97; // @[Mux.scala 80:57]
  wire  _T_98; // @[Mux.scala 80:60]
  wire [33:0] _T_99; // @[Mux.scala 80:57]
  wire [33:0] regWrite; // @[Datapath.scala 162:34]
  wire  _T_101; // @[Datapath.scala 164:29]
  CSR csr ( // @[Datapath.scala 23:23]
    .clock(csr_clock),
    .reset(csr_reset),
    .io_stall(csr_io_stall),
    .io_cmd(csr_io_cmd),
    .io_in(csr_io_in),
    .io_out(csr_io_out),
    .io_pc(csr_io_pc),
    .io_addr(csr_io_addr),
    .io_inst(csr_io_inst),
    .io_illegal(csr_io_illegal),
    .io_st_type(csr_io_st_type),
    .io_ld_type(csr_io_ld_type),
    .io_pc_check(csr_io_pc_check),
    .io_expt(csr_io_expt),
    .io_evec(csr_io_evec),
    .io_epc(csr_io_epc),
    .io_host_fromhost_valid(csr_io_host_fromhost_valid),
    .io_host_fromhost_bits(csr_io_host_fromhost_bits),
    .io_host_tohost(csr_io_host_tohost)
  );
  RegFile regFile ( // @[Datapath.scala 24:23]
    .clock(regFile_clock),
    .io_raddr1(regFile_io_raddr1),
    .io_raddr2(regFile_io_raddr2),
    .io_rdata1(regFile_io_rdata1),
    .io_rdata2(regFile_io_rdata2),
    .io_wen(regFile_io_wen),
    .io_waddr(regFile_io_waddr),
    .io_wdata(regFile_io_wdata)
  );
  ALUArea alu ( // @[Config.scala 13:50]
    .io_A(alu_io_A),
    .io_B(alu_io_B),
    .io_alu_op(alu_io_alu_op),
    .io_out(alu_io_out),
    .io_sum(alu_io_sum)
  );
  ImmGenWire immGen ( // @[Config.scala 14:50]
    .io_inst(immGen_io_inst),
    .io_sel(immGen_io_sel),
    .io_out(immGen_io_out)
  );
  BrCondArea brCond ( // @[Config.scala 15:50]
    .io_rs1(brCond_io_rs1),
    .io_rs2(brCond_io_rs2),
    .io_br_type(brCond_io_br_type),
    .io_taken(brCond_io_taken)
  );
  assign _T = $unsigned(reset); // @[Datapath.scala 51:31]
  assign _T_1 = io_icache_resp_valid == 1'h0; // @[Datapath.scala 52:15]
  assign _T_2 = io_dcache_resp_valid == 1'h0; // @[Datapath.scala 52:40]
  assign stall = _T_1 | _T_2; // @[Datapath.scala 52:37]
  assign _T_4 = 32'h200 - 32'h4; // @[Datapath.scala 53:47]
  assign _T_5 = io_ctrl_pc_sel == 2'h3; // @[Datapath.scala 55:33]
  assign _T_6 = io_ctrl_pc_sel == 2'h1; // @[Datapath.scala 56:33]
  assign _T_7 = _T_6 | brCond_io_taken; // @[Datapath.scala 56:44]
  assign _GEN_24 = alu_io_sum[31:1]; // @[Datapath.scala 56:75]
  assign _T_8 = {{1'd0}, _GEN_24}; // @[Datapath.scala 56:75]
  assign _T_9 = {_T_8, 1'h0}; // @[Datapath.scala 56:82]
  assign _T_10 = io_ctrl_pc_sel == 2'h2; // @[Datapath.scala 57:33]
  assign _T_12 = pc + 33'h4; // @[Datapath.scala 57:50]
  assign _T_13 = _T_10 ? pc : _T_12; // @[Datapath.scala 57:17]
  assign _T_14 = _T_7 ? _T_9 : _T_13; // @[Datapath.scala 56:17]
  assign _T_15 = _T_5 ? {{1'd0}, csr_io_epc} : _T_14; // @[Datapath.scala 55:17]
  assign _T_16 = csr_io_expt ? {{1'd0}, csr_io_evec} : _T_15; // @[Datapath.scala 54:32]
  assign npc = stall ? pc : _T_16; // @[Datapath.scala 54:17]
  assign _T_17 = started | io_ctrl_inst_kill; // @[Datapath.scala 58:26]
  assign _T_18 = _T_17 | brCond_io_taken; // @[Datapath.scala 58:47]
  assign _T_19 = _T_18 | csr_io_expt; // @[Datapath.scala 58:66]
  assign _T_20 = stall == 1'h0; // @[Datapath.scala 63:30]
  assign rs1_addr = fe_inst[19:15]; // @[Datapath.scala 78:25]
  assign rs2_addr = fe_inst[24:20]; // @[Datapath.scala 79:25]
  assign wb_rd_addr = ew_inst[11:7]; // @[Datapath.scala 88:27]
  assign _T_22 = rs1_addr != 5'h0; // @[Datapath.scala 89:37]
  assign _T_23 = wb_en & _T_22; // @[Datapath.scala 89:25]
  assign _T_24 = rs1_addr == wb_rd_addr; // @[Datapath.scala 89:54]
  assign rs1hazard = _T_23 & _T_24; // @[Datapath.scala 89:41]
  assign _T_25 = rs2_addr != 5'h0; // @[Datapath.scala 90:37]
  assign _T_26 = wb_en & _T_25; // @[Datapath.scala 90:25]
  assign _T_27 = rs2_addr == wb_rd_addr; // @[Datapath.scala 90:54]
  assign rs2hazard = _T_26 & _T_27; // @[Datapath.scala 90:41]
  assign _T_28 = wb_sel == 2'h0; // @[Datapath.scala 91:24]
  assign _T_29 = _T_28 & rs1hazard; // @[Datapath.scala 91:35]
  assign rs1 = _T_29 ? ew_alu : regFile_io_rdata1; // @[Datapath.scala 91:16]
  assign _T_31 = _T_28 & rs2hazard; // @[Datapath.scala 92:35]
  assign rs2 = _T_31 ? ew_alu : regFile_io_rdata2; // @[Datapath.scala 92:16]
  assign _T_33 = io_ctrl_A_sel ? {{1'd0}, rs1} : fe_pc; // @[Datapath.scala 95:18]
  assign _T_36 = stall ? ew_alu : alu_io_sum; // @[Datapath.scala 105:20]
  assign _GEN_25 = _T_36[31:2]; // @[Datapath.scala 105:48]
  assign _T_37 = {{2'd0}, _GEN_25}; // @[Datapath.scala 105:48]
  assign _GEN_26 = {_T_37, 2'h0}; // @[Datapath.scala 105:55]
  assign daddr = {{1'd0}, _GEN_26}; // @[Datapath.scala 105:55]
  assign _T_38 = alu_io_sum[1]; // @[Datapath.scala 106:28]
  assign _GEN_27 = {_T_38, 4'h0}; // @[Datapath.scala 106:32]
  assign _T_39 = {{3'd0}, _GEN_27}; // @[Datapath.scala 106:32]
  assign _T_40 = alu_io_sum[0]; // @[Datapath.scala 106:60]
  assign _T_41 = {_T_40, 3'h0}; // @[Datapath.scala 106:64]
  assign _GEN_28 = {{4'd0}, _T_41}; // @[Datapath.scala 106:47]
  assign woffset = _T_39 | _GEN_28; // @[Datapath.scala 106:47]
  assign _T_43 = io_ctrl_st_type != 2'h0; // @[Datapath.scala 107:57]
  assign _T_44 = io_ctrl_ld_type != 3'h0; // @[Datapath.scala 107:80]
  assign _T_45 = _T_43 | _T_44; // @[Datapath.scala 107:61]
  assign _GEN_29 = {{255'd0}, rs2}; // @[Datapath.scala 109:34]
  assign _T_47 = _GEN_29 << woffset; // @[Datapath.scala 109:34]
  assign _T_48 = stall ? st_type : io_ctrl_st_type; // @[Datapath.scala 110:43]
  assign _T_49 = alu_io_sum[1:0]; // @[Datapath.scala 113:36]
  assign _T_50 = 5'h3 << _T_49; // @[Datapath.scala 113:23]
  assign _T_52 = 4'h1 << _T_49; // @[Datapath.scala 114:23]
  assign _T_53 = 2'h1 == _T_48; // @[Mux.scala 80:60]
  assign _T_54 = _T_53 ? 4'hf : 4'h0; // @[Mux.scala 80:57]
  assign _T_55 = 2'h2 == _T_48; // @[Mux.scala 80:60]
  assign _T_56 = _T_55 ? _T_50 : {{1'd0}, _T_54}; // @[Mux.scala 80:57]
  assign _T_57 = 2'h3 == _T_48; // @[Mux.scala 80:60]
  assign _T_58 = _T_57 ? {{1'd0}, _T_52} : _T_56; // @[Mux.scala 80:57]
  assign _T_61 = _T_20 & csr_io_expt; // @[Datapath.scala 117:31]
  assign _T_62 = _T | _T_61; // @[Datapath.scala 117:21]
  assign _T_64 = csr_io_expt == 1'h0; // @[Datapath.scala 124:24]
  assign _T_65 = _T_20 & _T_64; // @[Datapath.scala 124:21]
  assign _T_66 = io_ctrl_imm_sel == 3'h6; // @[Datapath.scala 128:38]
  assign _T_69 = ew_alu[1]; // @[Datapath.scala 139:24]
  assign _GEN_30 = {_T_69, 4'h0}; // @[Datapath.scala 139:28]
  assign _T_70 = {{3'd0}, _GEN_30}; // @[Datapath.scala 139:28]
  assign _T_71 = ew_alu[0]; // @[Datapath.scala 139:52]
  assign _T_72 = {_T_71, 3'h0}; // @[Datapath.scala 139:56]
  assign _GEN_31 = {{4'd0}, _T_72}; // @[Datapath.scala 139:43]
  assign loffset = _T_70 | _GEN_31; // @[Datapath.scala 139:43]
  assign lshift = io_dcache_resp_bits_data >> loffset; // @[Datapath.scala 140:42]
  assign _T_73 = {1'b0,$signed(io_dcache_resp_bits_data)}; // @[Datapath.scala 141:61]
  assign _T_74 = lshift[15:0]; // @[Datapath.scala 142:21]
  assign _T_75 = $signed(_T_74); // @[Datapath.scala 142:29]
  assign _T_76 = lshift[7:0]; // @[Datapath.scala 142:53]
  assign _T_77 = $signed(_T_76); // @[Datapath.scala 142:60]
  assign _T_79 = {1'b0,$signed(_T_74)}; // @[Datapath.scala 143:29]
  assign _T_81 = {1'b0,$signed(_T_76)}; // @[Datapath.scala 143:60]
  assign _T_82 = 3'h2 == ld_type; // @[Mux.scala 80:60]
  assign _T_83 = _T_82 ? $signed({{17{_T_75[15]}},_T_75}) : $signed(_T_73); // @[Mux.scala 80:57]
  assign _T_84 = 3'h3 == ld_type; // @[Mux.scala 80:60]
  assign _T_85 = _T_84 ? $signed({{25{_T_77[7]}},_T_77}) : $signed(_T_83); // @[Mux.scala 80:57]
  assign _T_86 = 3'h4 == ld_type; // @[Mux.scala 80:60]
  assign _T_87 = _T_86 ? $signed({{16{_T_79[16]}},_T_79}) : $signed(_T_85); // @[Mux.scala 80:57]
  assign _T_88 = 3'h5 == ld_type; // @[Mux.scala 80:60]
  assign load = _T_88 ? $signed({{24{_T_81[8]}},_T_81}) : $signed(_T_87); // @[Mux.scala 80:57]
  assign _T_89 = {1'b0,$signed(ew_alu)}; // @[Datapath.scala 159:43]
  assign _T_91 = ew_pc + 33'h4; // @[Datapath.scala 161:22]
  assign _T_92 = {1'b0,$signed(_T_91)}; // @[Datapath.scala 161:29]
  assign _T_93 = {1'b0,$signed(csr_io_out)}; // @[Datapath.scala 162:26]
  assign _T_94 = 2'h1 == wb_sel; // @[Mux.scala 80:60]
  assign _T_95 = _T_94 ? $signed(load) : $signed(_T_89); // @[Mux.scala 80:57]
  assign _T_96 = 2'h2 == wb_sel; // @[Mux.scala 80:60]
  assign _T_97 = _T_96 ? $signed(_T_92) : $signed({{1{_T_95[32]}},_T_95}); // @[Mux.scala 80:57]
  assign _T_98 = 2'h3 == wb_sel; // @[Mux.scala 80:60]
  assign _T_99 = _T_98 ? $signed({{1{_T_93[32]}},_T_93}) : $signed(_T_97); // @[Mux.scala 80:57]
  assign regWrite = $unsigned(_T_99); // @[Datapath.scala 162:34]
  assign _T_101 = wb_en & _T_20; // @[Datapath.scala 164:29]
  assign io_host_tohost = csr_io_host_tohost; // @[Datapath.scala 156:11]
  assign io_icache_req_valid = stall == 1'h0; // @[Datapath.scala 63:27]
  assign io_icache_req_bits_addr = npc[31:0]; // @[Datapath.scala 60:27]
  assign io_dcache_abort = csr_io_expt; // @[Datapath.scala 169:19]
  assign io_dcache_req_valid = _T_20 & _T_45; // @[Datapath.scala 107:27]
  assign io_dcache_req_bits_addr = daddr[31:0]; // @[Datapath.scala 108:27]
  assign io_dcache_req_bits_data = _T_47[31:0]; // @[Datapath.scala 109:27]
  assign io_dcache_req_bits_mask = _T_58[3:0]; // @[Datapath.scala 110:27]
  assign io_ctrl_inst = fe_inst; // @[Datapath.scala 74:17]
  assign csr_clock = clock;
  assign csr_reset = reset;
  assign csr_io_stall = _T_1 | _T_2; // @[Datapath.scala 146:19]
  assign csr_io_cmd = csr_cmd; // @[Datapath.scala 148:19]
  assign csr_io_in = csr_in; // @[Datapath.scala 147:19]
  assign csr_io_pc = ew_pc[31:0]; // @[Datapath.scala 150:19]
  assign csr_io_addr = ew_alu; // @[Datapath.scala 151:19]
  assign csr_io_inst = ew_inst; // @[Datapath.scala 149:19]
  assign csr_io_illegal = illegal; // @[Datapath.scala 152:19]
  assign csr_io_st_type = st_type; // @[Datapath.scala 155:19]
  assign csr_io_ld_type = ld_type; // @[Datapath.scala 154:19]
  assign csr_io_pc_check = pc_check; // @[Datapath.scala 153:19]
  assign csr_io_host_fromhost_valid = io_host_fromhost_valid; // @[Datapath.scala 156:11]
  assign csr_io_host_fromhost_bits = io_host_fromhost_bits; // @[Datapath.scala 156:11]
  assign regFile_clock = clock;
  assign regFile_io_raddr1 = fe_inst[19:15]; // @[Datapath.scala 80:21]
  assign regFile_io_raddr2 = fe_inst[24:20]; // @[Datapath.scala 81:21]
  assign regFile_io_wen = _T_101 & _T_64; // @[Datapath.scala 164:20]
  assign regFile_io_waddr = ew_inst[11:7]; // @[Datapath.scala 165:20]
  assign regFile_io_wdata = regWrite[31:0]; // @[Datapath.scala 166:20]
  assign alu_io_A = _T_33[31:0]; // @[Datapath.scala 95:12]
  assign alu_io_B = io_ctrl_B_sel ? rs2 : immGen_io_out; // @[Datapath.scala 96:12]
  assign alu_io_alu_op = io_ctrl_alu_op; // @[Datapath.scala 97:17]
  assign immGen_io_inst = fe_inst; // @[Datapath.scala 84:18]
  assign immGen_io_sel = io_ctrl_imm_sel; // @[Datapath.scala 85:18]
  assign brCond_io_rs1 = _T_29 ? ew_alu : regFile_io_rdata1; // @[Datapath.scala 100:17]
  assign brCond_io_rs2 = _T_31 ? ew_alu : regFile_io_rdata2; // @[Datapath.scala 101:17]
  assign brCond_io_br_type = io_ctrl_br_type; // @[Datapath.scala 102:21]
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
  fe_inst = _RAND_0[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {2{`RANDOM}};
  fe_pc = _RAND_1[32:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  ew_inst = _RAND_2[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {2{`RANDOM}};
  ew_pc = _RAND_3[32:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {1{`RANDOM}};
  ew_alu = _RAND_4[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  csr_in = _RAND_5[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_6 = {1{`RANDOM}};
  st_type = _RAND_6[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_7 = {1{`RANDOM}};
  ld_type = _RAND_7[2:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_8 = {1{`RANDOM}};
  wb_sel = _RAND_8[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_9 = {1{`RANDOM}};
  wb_en = _RAND_9[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_10 = {1{`RANDOM}};
  csr_cmd = _RAND_10[2:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_11 = {1{`RANDOM}};
  illegal = _RAND_11[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_12 = {1{`RANDOM}};
  pc_check = _RAND_12[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_13 = {1{`RANDOM}};
  started = _RAND_13[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_14 = {2{`RANDOM}};
  pc = _RAND_14[32:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      fe_inst <= 32'h13;
    end else if (_T_20) begin
      if (_T_19) begin
        fe_inst <= 32'h13;
      end else begin
        fe_inst <= io_icache_resp_bits_data;
      end
    end
    if (_T_20) begin
      fe_pc <= pc;
    end
    if (reset) begin
      ew_inst <= 32'h13;
    end else if (!(_T_62)) begin
      if (_T_65) begin
        ew_inst <= fe_inst;
      end
    end
    if (!(_T_62)) begin
      if (_T_65) begin
        ew_pc <= fe_pc;
      end
    end
    if (!(_T_62)) begin
      if (_T_65) begin
        ew_alu <= alu_io_out;
      end
    end
    if (!(_T_62)) begin
      if (_T_65) begin
        if (_T_66) begin
          csr_in <= immGen_io_out;
        end else if (_T_29) begin
          csr_in <= ew_alu;
        end else begin
          csr_in <= regFile_io_rdata1;
        end
      end
    end
    if (_T_62) begin
      st_type <= 2'h0;
    end else if (_T_65) begin
      st_type <= io_ctrl_st_type;
    end
    if (_T_62) begin
      ld_type <= 3'h0;
    end else if (_T_65) begin
      ld_type <= io_ctrl_ld_type;
    end
    if (!(_T_62)) begin
      if (_T_65) begin
        wb_sel <= io_ctrl_wb_sel;
      end
    end
    if (_T_62) begin
      wb_en <= 1'h0;
    end else if (_T_65) begin
      wb_en <= io_ctrl_wb_en;
    end
    if (_T_62) begin
      csr_cmd <= 3'h0;
    end else if (_T_65) begin
      csr_cmd <= io_ctrl_csr_cmd;
    end
    if (_T_62) begin
      illegal <= 1'h0;
    end else if (_T_65) begin
      illegal <= io_ctrl_illegal;
    end
    if (_T_62) begin
      pc_check <= 1'h0;
    end else if (_T_65) begin
      pc_check <= _T_6;
    end
    started <= $unsigned(reset);
    if (reset) begin
      pc <= {{1'd0}, _T_4};
    end else if (!(stall)) begin
      if (csr_io_expt) begin
        pc <= {{1'd0}, csr_io_evec};
      end else if (_T_5) begin
        pc <= {{1'd0}, csr_io_epc};
      end else if (_T_7) begin
        pc <= _T_9;
      end else if (!(_T_10)) begin
        pc <= _T_12;
      end
    end
  end
endmodule
