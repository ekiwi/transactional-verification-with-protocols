module ALUArea(
  input  [31:0] io_A,
  input  [31:0] io_B,
  input  [3:0]  io_alu_op,
  output [31:0] io_out,
  output [31:0] io_sum
);
  wire  _T; // @[ALU.scala 64:33]
  wire [31:0] _T_2; // @[ALU.scala 64:38]
  wire [31:0] _T_3; // @[ALU.scala 64:23]
  wire [31:0] sum; // @[ALU.scala 64:18]
  wire  _T_5; // @[ALU.scala 65:21]
  wire  _T_6; // @[ALU.scala 65:38]
  wire  _T_7; // @[ALU.scala 65:30]
  wire  _T_8; // @[ALU.scala 65:51]
  wire  _T_9; // @[ALU.scala 66:26]
  wire  _T_12; // @[ALU.scala 66:16]
  wire  cmp; // @[ALU.scala 65:16]
  wire [4:0] shamt; // @[ALU.scala 67:20]
  wire  _T_13; // @[ALU.scala 68:29]
  wire [15:0] _T_16; // @[Bitwise.scala 102:21]
  wire [31:0] _T_17; // @[Bitwise.scala 102:31]
  wire [15:0] _T_18; // @[Bitwise.scala 102:46]
  wire [31:0] _T_19; // @[Bitwise.scala 102:65]
  wire [31:0] _T_21; // @[Bitwise.scala 102:75]
  wire [31:0] _T_22; // @[Bitwise.scala 102:39]
  wire [23:0] _T_26; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_0; // @[Bitwise.scala 102:31]
  wire [31:0] _T_27; // @[Bitwise.scala 102:31]
  wire [23:0] _T_28; // @[Bitwise.scala 102:46]
  wire [31:0] _T_29; // @[Bitwise.scala 102:65]
  wire [31:0] _T_31; // @[Bitwise.scala 102:75]
  wire [31:0] _T_32; // @[Bitwise.scala 102:39]
  wire [27:0] _T_36; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_1; // @[Bitwise.scala 102:31]
  wire [31:0] _T_37; // @[Bitwise.scala 102:31]
  wire [27:0] _T_38; // @[Bitwise.scala 102:46]
  wire [31:0] _T_39; // @[Bitwise.scala 102:65]
  wire [31:0] _T_41; // @[Bitwise.scala 102:75]
  wire [31:0] _T_42; // @[Bitwise.scala 102:39]
  wire [29:0] _T_46; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_2; // @[Bitwise.scala 102:31]
  wire [31:0] _T_47; // @[Bitwise.scala 102:31]
  wire [29:0] _T_48; // @[Bitwise.scala 102:46]
  wire [31:0] _T_49; // @[Bitwise.scala 102:65]
  wire [31:0] _T_51; // @[Bitwise.scala 102:75]
  wire [31:0] _T_52; // @[Bitwise.scala 102:39]
  wire [30:0] _T_56; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_3; // @[Bitwise.scala 102:31]
  wire [31:0] _T_57; // @[Bitwise.scala 102:31]
  wire [30:0] _T_58; // @[Bitwise.scala 102:46]
  wire [31:0] _T_59; // @[Bitwise.scala 102:65]
  wire [31:0] _T_61; // @[Bitwise.scala 102:75]
  wire [31:0] _T_62; // @[Bitwise.scala 102:39]
  wire [31:0] shin; // @[ALU.scala 68:19]
  wire  _T_64; // @[ALU.scala 69:41]
  wire  _T_65; // @[ALU.scala 69:34]
  wire [32:0] _T_66; // @[Cat.scala 29:58]
  wire [32:0] _T_67; // @[ALU.scala 69:57]
  wire [32:0] _T_68; // @[ALU.scala 69:64]
  wire [31:0] shiftr; // @[ALU.scala 69:73]
  wire [15:0] _T_71; // @[Bitwise.scala 102:21]
  wire [31:0] _T_72; // @[Bitwise.scala 102:31]
  wire [15:0] _T_73; // @[Bitwise.scala 102:46]
  wire [31:0] _T_74; // @[Bitwise.scala 102:65]
  wire [31:0] _T_76; // @[Bitwise.scala 102:75]
  wire [31:0] _T_77; // @[Bitwise.scala 102:39]
  wire [23:0] _T_81; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_4; // @[Bitwise.scala 102:31]
  wire [31:0] _T_82; // @[Bitwise.scala 102:31]
  wire [23:0] _T_83; // @[Bitwise.scala 102:46]
  wire [31:0] _T_84; // @[Bitwise.scala 102:65]
  wire [31:0] _T_86; // @[Bitwise.scala 102:75]
  wire [31:0] _T_87; // @[Bitwise.scala 102:39]
  wire [27:0] _T_91; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_5; // @[Bitwise.scala 102:31]
  wire [31:0] _T_92; // @[Bitwise.scala 102:31]
  wire [27:0] _T_93; // @[Bitwise.scala 102:46]
  wire [31:0] _T_94; // @[Bitwise.scala 102:65]
  wire [31:0] _T_96; // @[Bitwise.scala 102:75]
  wire [31:0] _T_97; // @[Bitwise.scala 102:39]
  wire [29:0] _T_101; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_6; // @[Bitwise.scala 102:31]
  wire [31:0] _T_102; // @[Bitwise.scala 102:31]
  wire [29:0] _T_103; // @[Bitwise.scala 102:46]
  wire [31:0] _T_104; // @[Bitwise.scala 102:65]
  wire [31:0] _T_106; // @[Bitwise.scala 102:75]
  wire [31:0] _T_107; // @[Bitwise.scala 102:39]
  wire [30:0] _T_111; // @[Bitwise.scala 102:21]
  wire [31:0] _GEN_7; // @[Bitwise.scala 102:31]
  wire [31:0] _T_112; // @[Bitwise.scala 102:31]
  wire [30:0] _T_113; // @[Bitwise.scala 102:46]
  wire [31:0] _T_114; // @[Bitwise.scala 102:65]
  wire [31:0] _T_116; // @[Bitwise.scala 102:75]
  wire [31:0] shiftl; // @[Bitwise.scala 102:39]
  wire  _T_117; // @[ALU.scala 73:19]
  wire  _T_118; // @[ALU.scala 73:44]
  wire  _T_119; // @[ALU.scala 73:31]
  wire  _T_120; // @[ALU.scala 74:19]
  wire  _T_121; // @[ALU.scala 74:44]
  wire  _T_122; // @[ALU.scala 74:31]
  wire  _T_123; // @[ALU.scala 75:19]
  wire  _T_124; // @[ALU.scala 75:44]
  wire  _T_125; // @[ALU.scala 75:31]
  wire  _T_126; // @[ALU.scala 76:19]
  wire  _T_127; // @[ALU.scala 77:19]
  wire [31:0] _T_128; // @[ALU.scala 77:38]
  wire  _T_129; // @[ALU.scala 78:19]
  wire [31:0] _T_130; // @[ALU.scala 78:38]
  wire  _T_131; // @[ALU.scala 79:19]
  wire [31:0] _T_132; // @[ALU.scala 79:38]
  wire  _T_133; // @[ALU.scala 80:19]
  wire [31:0] _T_134; // @[ALU.scala 80:8]
  wire [31:0] _T_135; // @[ALU.scala 79:8]
  wire [31:0] _T_136; // @[ALU.scala 78:8]
  wire [31:0] _T_137; // @[ALU.scala 77:8]
  wire [31:0] _T_138; // @[ALU.scala 76:8]
  wire [31:0] _T_139; // @[ALU.scala 75:8]
  wire [31:0] _T_140; // @[ALU.scala 74:8]
  assign _T = io_alu_op[0]; // @[ALU.scala 64:33]
  assign _T_2 = 32'h0 - io_B; // @[ALU.scala 64:38]
  assign _T_3 = _T ? _T_2 : io_B; // @[ALU.scala 64:23]
  assign sum = io_A + _T_3; // @[ALU.scala 64:18]
  assign _T_5 = io_A[31]; // @[ALU.scala 65:21]
  assign _T_6 = io_B[31]; // @[ALU.scala 65:38]
  assign _T_7 = _T_5 == _T_6; // @[ALU.scala 65:30]
  assign _T_8 = sum[31]; // @[ALU.scala 65:51]
  assign _T_9 = io_alu_op[1]; // @[ALU.scala 66:26]
  assign _T_12 = _T_9 ? _T_6 : _T_5; // @[ALU.scala 66:16]
  assign cmp = _T_7 ? _T_8 : _T_12; // @[ALU.scala 65:16]
  assign shamt = io_B[4:0]; // @[ALU.scala 67:20]
  assign _T_13 = io_alu_op[3]; // @[ALU.scala 68:29]
  assign _T_16 = io_A[31:16]; // @[Bitwise.scala 102:21]
  assign _T_17 = {{16'd0}, _T_16}; // @[Bitwise.scala 102:31]
  assign _T_18 = io_A[15:0]; // @[Bitwise.scala 102:46]
  assign _T_19 = {_T_18, 16'h0}; // @[Bitwise.scala 102:65]
  assign _T_21 = _T_19 & 32'hffff0000; // @[Bitwise.scala 102:75]
  assign _T_22 = _T_17 | _T_21; // @[Bitwise.scala 102:39]
  assign _T_26 = _T_22[31:8]; // @[Bitwise.scala 102:21]
  assign _GEN_0 = {{8'd0}, _T_26}; // @[Bitwise.scala 102:31]
  assign _T_27 = _GEN_0 & 32'hff00ff; // @[Bitwise.scala 102:31]
  assign _T_28 = _T_22[23:0]; // @[Bitwise.scala 102:46]
  assign _T_29 = {_T_28, 8'h0}; // @[Bitwise.scala 102:65]
  assign _T_31 = _T_29 & 32'hff00ff00; // @[Bitwise.scala 102:75]
  assign _T_32 = _T_27 | _T_31; // @[Bitwise.scala 102:39]
  assign _T_36 = _T_32[31:4]; // @[Bitwise.scala 102:21]
  assign _GEN_1 = {{4'd0}, _T_36}; // @[Bitwise.scala 102:31]
  assign _T_37 = _GEN_1 & 32'hf0f0f0f; // @[Bitwise.scala 102:31]
  assign _T_38 = _T_32[27:0]; // @[Bitwise.scala 102:46]
  assign _T_39 = {_T_38, 4'h0}; // @[Bitwise.scala 102:65]
  assign _T_41 = _T_39 & 32'hf0f0f0f0; // @[Bitwise.scala 102:75]
  assign _T_42 = _T_37 | _T_41; // @[Bitwise.scala 102:39]
  assign _T_46 = _T_42[31:2]; // @[Bitwise.scala 102:21]
  assign _GEN_2 = {{2'd0}, _T_46}; // @[Bitwise.scala 102:31]
  assign _T_47 = _GEN_2 & 32'h33333333; // @[Bitwise.scala 102:31]
  assign _T_48 = _T_42[29:0]; // @[Bitwise.scala 102:46]
  assign _T_49 = {_T_48, 2'h0}; // @[Bitwise.scala 102:65]
  assign _T_51 = _T_49 & 32'hcccccccc; // @[Bitwise.scala 102:75]
  assign _T_52 = _T_47 | _T_51; // @[Bitwise.scala 102:39]
  assign _T_56 = _T_52[31:1]; // @[Bitwise.scala 102:21]
  assign _GEN_3 = {{1'd0}, _T_56}; // @[Bitwise.scala 102:31]
  assign _T_57 = _GEN_3 & 32'h55555555; // @[Bitwise.scala 102:31]
  assign _T_58 = _T_52[30:0]; // @[Bitwise.scala 102:46]
  assign _T_59 = {_T_58, 1'h0}; // @[Bitwise.scala 102:65]
  assign _T_61 = _T_59 & 32'haaaaaaaa; // @[Bitwise.scala 102:75]
  assign _T_62 = _T_57 | _T_61; // @[Bitwise.scala 102:39]
  assign shin = _T_13 ? io_A : _T_62; // @[ALU.scala 68:19]
  assign _T_64 = shin[31]; // @[ALU.scala 69:41]
  assign _T_65 = _T & _T_64; // @[ALU.scala 69:34]
  assign _T_66 = {_T_65,shin}; // @[Cat.scala 29:58]
  assign _T_67 = $signed(_T_66); // @[ALU.scala 69:57]
  assign _T_68 = $signed(_T_67) >>> shamt; // @[ALU.scala 69:64]
  assign shiftr = _T_68[31:0]; // @[ALU.scala 69:73]
  assign _T_71 = shiftr[31:16]; // @[Bitwise.scala 102:21]
  assign _T_72 = {{16'd0}, _T_71}; // @[Bitwise.scala 102:31]
  assign _T_73 = shiftr[15:0]; // @[Bitwise.scala 102:46]
  assign _T_74 = {_T_73, 16'h0}; // @[Bitwise.scala 102:65]
  assign _T_76 = _T_74 & 32'hffff0000; // @[Bitwise.scala 102:75]
  assign _T_77 = _T_72 | _T_76; // @[Bitwise.scala 102:39]
  assign _T_81 = _T_77[31:8]; // @[Bitwise.scala 102:21]
  assign _GEN_4 = {{8'd0}, _T_81}; // @[Bitwise.scala 102:31]
  assign _T_82 = _GEN_4 & 32'hff00ff; // @[Bitwise.scala 102:31]
  assign _T_83 = _T_77[23:0]; // @[Bitwise.scala 102:46]
  assign _T_84 = {_T_83, 8'h0}; // @[Bitwise.scala 102:65]
  assign _T_86 = _T_84 & 32'hff00ff00; // @[Bitwise.scala 102:75]
  assign _T_87 = _T_82 | _T_86; // @[Bitwise.scala 102:39]
  assign _T_91 = _T_87[31:4]; // @[Bitwise.scala 102:21]
  assign _GEN_5 = {{4'd0}, _T_91}; // @[Bitwise.scala 102:31]
  assign _T_92 = _GEN_5 & 32'hf0f0f0f; // @[Bitwise.scala 102:31]
  assign _T_93 = _T_87[27:0]; // @[Bitwise.scala 102:46]
  assign _T_94 = {_T_93, 4'h0}; // @[Bitwise.scala 102:65]
  assign _T_96 = _T_94 & 32'hf0f0f0f0; // @[Bitwise.scala 102:75]
  assign _T_97 = _T_92 | _T_96; // @[Bitwise.scala 102:39]
  assign _T_101 = _T_97[31:2]; // @[Bitwise.scala 102:21]
  assign _GEN_6 = {{2'd0}, _T_101}; // @[Bitwise.scala 102:31]
  assign _T_102 = _GEN_6 & 32'h33333333; // @[Bitwise.scala 102:31]
  assign _T_103 = _T_97[29:0]; // @[Bitwise.scala 102:46]
  assign _T_104 = {_T_103, 2'h0}; // @[Bitwise.scala 102:65]
  assign _T_106 = _T_104 & 32'hcccccccc; // @[Bitwise.scala 102:75]
  assign _T_107 = _T_102 | _T_106; // @[Bitwise.scala 102:39]
  assign _T_111 = _T_107[31:1]; // @[Bitwise.scala 102:21]
  assign _GEN_7 = {{1'd0}, _T_111}; // @[Bitwise.scala 102:31]
  assign _T_112 = _GEN_7 & 32'h55555555; // @[Bitwise.scala 102:31]
  assign _T_113 = _T_107[30:0]; // @[Bitwise.scala 102:46]
  assign _T_114 = {_T_113, 1'h0}; // @[Bitwise.scala 102:65]
  assign _T_116 = _T_114 & 32'haaaaaaaa; // @[Bitwise.scala 102:75]
  assign shiftl = _T_112 | _T_116; // @[Bitwise.scala 102:39]
  assign _T_117 = io_alu_op == 4'h0; // @[ALU.scala 73:19]
  assign _T_118 = io_alu_op == 4'h1; // @[ALU.scala 73:44]
  assign _T_119 = _T_117 | _T_118; // @[ALU.scala 73:31]
  assign _T_120 = io_alu_op == 4'h5; // @[ALU.scala 74:19]
  assign _T_121 = io_alu_op == 4'h7; // @[ALU.scala 74:44]
  assign _T_122 = _T_120 | _T_121; // @[ALU.scala 74:31]
  assign _T_123 = io_alu_op == 4'h9; // @[ALU.scala 75:19]
  assign _T_124 = io_alu_op == 4'h8; // @[ALU.scala 75:44]
  assign _T_125 = _T_123 | _T_124; // @[ALU.scala 75:31]
  assign _T_126 = io_alu_op == 4'h6; // @[ALU.scala 76:19]
  assign _T_127 = io_alu_op == 4'h2; // @[ALU.scala 77:19]
  assign _T_128 = io_A & io_B; // @[ALU.scala 77:38]
  assign _T_129 = io_alu_op == 4'h3; // @[ALU.scala 78:19]
  assign _T_130 = io_A | io_B; // @[ALU.scala 78:38]
  assign _T_131 = io_alu_op == 4'h4; // @[ALU.scala 79:19]
  assign _T_132 = io_A ^ io_B; // @[ALU.scala 79:38]
  assign _T_133 = io_alu_op == 4'ha; // @[ALU.scala 80:19]
  assign _T_134 = _T_133 ? io_A : io_B; // @[ALU.scala 80:8]
  assign _T_135 = _T_131 ? _T_132 : _T_134; // @[ALU.scala 79:8]
  assign _T_136 = _T_129 ? _T_130 : _T_135; // @[ALU.scala 78:8]
  assign _T_137 = _T_127 ? _T_128 : _T_136; // @[ALU.scala 77:8]
  assign _T_138 = _T_126 ? shiftl : _T_137; // @[ALU.scala 76:8]
  assign _T_139 = _T_125 ? shiftr : _T_138; // @[ALU.scala 75:8]
  assign _T_140 = _T_122 ? {{31'd0}, cmp} : _T_139; // @[ALU.scala 74:8]
  assign io_out = _T_119 ? sum : _T_140; // @[ALU.scala 83:10]
  assign io_sum = io_A + _T_3; // @[ALU.scala 84:10]
endmodule
