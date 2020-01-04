module CSR(
  input         clock,
  input         reset,
  input         io_stall,
  input  [2:0]  io_cmd,
  input  [31:0] io_in,
  output [31:0] io_out,
  input  [31:0] io_pc,
  input  [31:0] io_addr,
  input  [31:0] io_inst,
  input         io_illegal,
  input  [1:0]  io_st_type,
  input  [2:0]  io_ld_type,
  input         io_pc_check,
  output        io_expt,
  output [31:0] io_evec,
  output [31:0] io_epc,
  input         io_host_fromhost_valid,
  input  [31:0] io_host_fromhost_bits,
  output [31:0] io_host_tohost
);
  wire [11:0] csr_addr; // @[CSR.scala 100:25]
  wire [4:0] rs1_addr; // @[CSR.scala 101:25]
  reg [31:0] time_; // @[CSR.scala 104:25]
  reg [31:0] _RAND_0;
  reg [31:0] timeh; // @[CSR.scala 105:25]
  reg [31:0] _RAND_1;
  reg [31:0] cycle; // @[CSR.scala 106:25]
  reg [31:0] _RAND_2;
  reg [31:0] cycleh; // @[CSR.scala 107:25]
  reg [31:0] _RAND_3;
  reg [31:0] instret; // @[CSR.scala 108:25]
  reg [31:0] _RAND_4;
  reg [31:0] instreth; // @[CSR.scala 109:25]
  reg [31:0] _RAND_5;
  reg [1:0] PRV; // @[CSR.scala 118:21]
  reg [31:0] _RAND_6;
  reg [1:0] PRV1; // @[CSR.scala 119:21]
  reg [31:0] _RAND_7;
  reg  IE; // @[CSR.scala 122:20]
  reg [31:0] _RAND_8;
  reg  IE1; // @[CSR.scala 123:20]
  reg [31:0] _RAND_9;
  wire [31:0] mstatus; // @[Cat.scala 29:58]
  reg  MTIP; // @[CSR.scala 139:21]
  reg [31:0] _RAND_10;
  reg  MTIE; // @[CSR.scala 142:21]
  reg [31:0] _RAND_11;
  reg  MSIP; // @[CSR.scala 145:21]
  reg [31:0] _RAND_12;
  reg  MSIE; // @[CSR.scala 148:21]
  reg [31:0] _RAND_13;
  wire [31:0] mip; // @[Cat.scala 29:58]
  wire [31:0] mie; // @[Cat.scala 29:58]
  reg [31:0] mtimecmp; // @[CSR.scala 154:21]
  reg [31:0] _RAND_14;
  reg [31:0] mscratch; // @[CSR.scala 156:21]
  reg [31:0] _RAND_15;
  reg [31:0] mepc; // @[CSR.scala 158:17]
  reg [31:0] _RAND_16;
  reg [31:0] mcause; // @[CSR.scala 159:19]
  reg [31:0] _RAND_17;
  reg [31:0] mbadaddr; // @[CSR.scala 160:21]
  reg [31:0] _RAND_18;
  reg [31:0] mtohost; // @[CSR.scala 162:24]
  reg [31:0] _RAND_19;
  reg [31:0] mfromhost; // @[CSR.scala 163:22]
  reg [31:0] _RAND_20;
  wire [31:0] _GEN_0; // @[CSR.scala 165:32]
  wire  _T_28; // @[Lookup.scala 31:38]
  wire  _T_30; // @[Lookup.scala 31:38]
  wire  _T_32; // @[Lookup.scala 31:38]
  wire  _T_34; // @[Lookup.scala 31:38]
  wire  _T_36; // @[Lookup.scala 31:38]
  wire  _T_38; // @[Lookup.scala 31:38]
  wire  _T_40; // @[Lookup.scala 31:38]
  wire  _T_42; // @[Lookup.scala 31:38]
  wire  _T_44; // @[Lookup.scala 31:38]
  wire  _T_46; // @[Lookup.scala 31:38]
  wire  _T_48; // @[Lookup.scala 31:38]
  wire  _T_50; // @[Lookup.scala 31:38]
  wire  _T_52; // @[Lookup.scala 31:38]
  wire  _T_54; // @[Lookup.scala 31:38]
  wire  _T_56; // @[Lookup.scala 31:38]
  wire  _T_58; // @[Lookup.scala 31:38]
  wire  _T_60; // @[Lookup.scala 31:38]
  wire  _T_62; // @[Lookup.scala 31:38]
  wire  _T_64; // @[Lookup.scala 31:38]
  wire  _T_66; // @[Lookup.scala 31:38]
  wire  _T_68; // @[Lookup.scala 31:38]
  wire  _T_70; // @[Lookup.scala 31:38]
  wire  _T_72; // @[Lookup.scala 31:38]
  wire  _T_74; // @[Lookup.scala 31:38]
  wire  _T_76; // @[Lookup.scala 31:38]
  wire  _T_78; // @[Lookup.scala 31:38]
  wire  _T_80; // @[Lookup.scala 31:38]
  wire  _T_82; // @[Lookup.scala 31:38]
  wire  _T_84; // @[Lookup.scala 31:38]
  wire [31:0] _T_85; // @[Lookup.scala 33:37]
  wire [31:0] _T_86; // @[Lookup.scala 33:37]
  wire [31:0] _T_87; // @[Lookup.scala 33:37]
  wire [31:0] _T_88; // @[Lookup.scala 33:37]
  wire [31:0] _T_89; // @[Lookup.scala 33:37]
  wire [31:0] _T_90; // @[Lookup.scala 33:37]
  wire [31:0] _T_91; // @[Lookup.scala 33:37]
  wire [31:0] _T_92; // @[Lookup.scala 33:37]
  wire [31:0] _T_93; // @[Lookup.scala 33:37]
  wire [31:0] _T_94; // @[Lookup.scala 33:37]
  wire [31:0] _T_95; // @[Lookup.scala 33:37]
  wire [31:0] _T_96; // @[Lookup.scala 33:37]
  wire [31:0] _T_97; // @[Lookup.scala 33:37]
  wire [31:0] _T_98; // @[Lookup.scala 33:37]
  wire [31:0] _T_99; // @[Lookup.scala 33:37]
  wire [31:0] _T_100; // @[Lookup.scala 33:37]
  wire [31:0] _T_101; // @[Lookup.scala 33:37]
  wire [31:0] _T_102; // @[Lookup.scala 33:37]
  wire [31:0] _T_103; // @[Lookup.scala 33:37]
  wire [31:0] _T_104; // @[Lookup.scala 33:37]
  wire [31:0] _T_105; // @[Lookup.scala 33:37]
  wire [31:0] _T_106; // @[Lookup.scala 33:37]
  wire [31:0] _T_107; // @[Lookup.scala 33:37]
  wire [31:0] _T_108; // @[Lookup.scala 33:37]
  wire [31:0] _T_109; // @[Lookup.scala 33:37]
  wire [31:0] _T_110; // @[Lookup.scala 33:37]
  wire [31:0] _T_111; // @[Lookup.scala 33:37]
  wire [31:0] _T_112; // @[Lookup.scala 33:37]
  wire [1:0] _T_114; // @[CSR.scala 203:27]
  wire  privValid; // @[CSR.scala 203:34]
  wire  privInst; // @[CSR.scala 204:26]
  wire  _T_115; // @[CSR.scala 205:40]
  wire  _T_116; // @[CSR.scala 205:31]
  wire  _T_117; // @[CSR.scala 205:28]
  wire  _T_118; // @[CSR.scala 205:56]
  wire  _T_119; // @[CSR.scala 205:47]
  wire  isEcall; // @[CSR.scala 205:44]
  wire  _T_121; // @[CSR.scala 206:28]
  wire  isEbreak; // @[CSR.scala 206:44]
  wire  isEret; // @[CSR.scala 207:44]
  wire  _T_186; // @[CSR.scala 208:61]
  wire  _T_187; // @[CSR.scala 208:61]
  wire  _T_188; // @[CSR.scala 208:61]
  wire  _T_189; // @[CSR.scala 208:61]
  wire  _T_190; // @[CSR.scala 208:61]
  wire  _T_191; // @[CSR.scala 208:61]
  wire  _T_192; // @[CSR.scala 208:61]
  wire  _T_193; // @[CSR.scala 208:61]
  wire  _T_194; // @[CSR.scala 208:61]
  wire  _T_195; // @[CSR.scala 208:61]
  wire  _T_196; // @[CSR.scala 208:61]
  wire  _T_197; // @[CSR.scala 208:61]
  wire  _T_198; // @[CSR.scala 208:61]
  wire  _T_199; // @[CSR.scala 208:61]
  wire  _T_200; // @[CSR.scala 208:61]
  wire  _T_201; // @[CSR.scala 208:61]
  wire  _T_202; // @[CSR.scala 208:61]
  wire  _T_203; // @[CSR.scala 208:61]
  wire  _T_204; // @[CSR.scala 208:61]
  wire  _T_205; // @[CSR.scala 208:61]
  wire  _T_206; // @[CSR.scala 208:61]
  wire  _T_207; // @[CSR.scala 208:61]
  wire  _T_208; // @[CSR.scala 208:61]
  wire  _T_209; // @[CSR.scala 208:61]
  wire  _T_210; // @[CSR.scala 208:61]
  wire  _T_211; // @[CSR.scala 208:61]
  wire  _T_212; // @[CSR.scala 208:61]
  wire  csrValid; // @[CSR.scala 208:61]
  wire [1:0] _T_213; // @[CSR.scala 209:27]
  wire  _T_214; // @[CSR.scala 209:36]
  wire  _T_215; // @[CSR.scala 209:53]
  wire  _T_216; // @[CSR.scala 209:41]
  wire  _T_217; // @[CSR.scala 209:79]
  wire  csrRO; // @[CSR.scala 209:67]
  wire  _T_218; // @[CSR.scala 210:26]
  wire  _T_219; // @[CSR.scala 210:45]
  wire  _T_220; // @[CSR.scala 210:61]
  wire  _T_221; // @[CSR.scala 210:49]
  wire  wen; // @[CSR.scala 210:36]
  wire [31:0] _T_222; // @[CSR.scala 213:22]
  wire [31:0] _T_223; // @[CSR.scala 214:24]
  wire [31:0] _T_224; // @[CSR.scala 214:22]
  wire  _T_225; // @[Mux.scala 80:60]
  wire [31:0] _T_226; // @[Mux.scala 80:57]
  wire  _T_227; // @[Mux.scala 80:60]
  wire [31:0] _T_228; // @[Mux.scala 80:57]
  wire  _T_229; // @[Mux.scala 80:60]
  wire [31:0] wdata; // @[Mux.scala 80:57]
  wire  _T_230; // @[CSR.scala 216:44]
  wire  iaddrInvalid; // @[CSR.scala 216:34]
  wire [1:0] _T_231; // @[CSR.scala 218:29]
  wire  _T_232; // @[CSR.scala 218:36]
  wire  _T_233; // @[CSR.scala 218:65]
  wire  _T_235; // @[Mux.scala 80:60]
  wire  _T_236; // @[Mux.scala 80:57]
  wire  _T_237; // @[Mux.scala 80:60]
  wire  _T_238; // @[Mux.scala 80:57]
  wire  _T_239; // @[Mux.scala 80:60]
  wire  laddrInvalid; // @[Mux.scala 80:57]
  wire  _T_243; // @[Mux.scala 80:60]
  wire  _T_244; // @[Mux.scala 80:57]
  wire  _T_245; // @[Mux.scala 80:60]
  wire  saddrInvalid; // @[Mux.scala 80:57]
  wire  _T_246; // @[CSR.scala 221:25]
  wire  _T_247; // @[CSR.scala 221:41]
  wire  _T_248; // @[CSR.scala 221:57]
  wire [1:0] _T_249; // @[CSR.scala 222:20]
  wire  _T_250; // @[CSR.scala 222:27]
  wire  _T_251; // @[CSR.scala 222:35]
  wire  _T_252; // @[CSR.scala 222:48]
  wire  _T_253; // @[CSR.scala 222:45]
  wire  _T_254; // @[CSR.scala 222:31]
  wire  _T_255; // @[CSR.scala 221:73]
  wire  _T_256; // @[CSR.scala 222:67]
  wire  _T_257; // @[CSR.scala 222:60]
  wire  _T_259; // @[CSR.scala 223:24]
  wire  _T_260; // @[CSR.scala 222:76]
  wire  _T_261; // @[CSR.scala 223:39]
  wire [7:0] _T_263; // @[CSR.scala 224:27]
  wire [31:0] _GEN_260; // @[CSR.scala 224:20]
  wire [31:0] _T_267; // @[CSR.scala 228:16]
  wire  _T_268; // @[CSR.scala 229:13]
  wire [31:0] _T_270; // @[CSR.scala 229:36]
  wire [31:0] _GEN_1; // @[CSR.scala 229:19]
  wire [31:0] _T_272; // @[CSR.scala 230:18]
  wire  _T_273; // @[CSR.scala 231:14]
  wire [31:0] _T_275; // @[CSR.scala 231:39]
  wire [31:0] _GEN_2; // @[CSR.scala 231:20]
  wire  _T_276; // @[CSR.scala 232:27]
  wire  _T_277; // @[CSR.scala 232:52]
  wire  _T_278; // @[CSR.scala 232:61]
  wire  _T_279; // @[CSR.scala 232:72]
  wire  _T_280; // @[CSR.scala 232:48]
  wire  _T_281; // @[CSR.scala 232:88]
  wire  isInstRet; // @[CSR.scala 232:85]
  wire [31:0] _T_283; // @[CSR.scala 233:40]
  wire [31:0] _GEN_3; // @[CSR.scala 233:19]
  wire  _T_284; // @[CSR.scala 234:29]
  wire  _T_285; // @[CSR.scala 234:18]
  wire [31:0] _T_287; // @[CSR.scala 234:58]
  wire [31:0] _GEN_4; // @[CSR.scala 234:35]
  wire [29:0] _T_289; // @[CSR.scala 238:23]
  wire [31:0] _T_290; // @[CSR.scala 238:28]
  wire [3:0] _GEN_261; // @[CSR.scala 242:47]
  wire [3:0] _T_292; // @[CSR.scala 242:47]
  wire [1:0] _T_293; // @[CSR.scala 243:20]
  wire [3:0] _T_294; // @[CSR.scala 242:20]
  wire [3:0] _T_295; // @[CSR.scala 241:20]
  wire [3:0] _T_296; // @[CSR.scala 240:20]
  wire [3:0] _T_297; // @[CSR.scala 239:20]
  wire  _T_298; // @[CSR.scala 248:25]
  wire  _T_299; // @[CSR.scala 248:41]
  wire  _T_300; // @[CSR.scala 255:21]
  wire [1:0] _T_301; // @[CSR.scala 256:22]
  wire  _T_302; // @[CSR.scala 257:22]
  wire [1:0] _T_303; // @[CSR.scala 258:22]
  wire  _T_304; // @[CSR.scala 259:22]
  wire  _T_305; // @[CSR.scala 261:26]
  wire  _T_306; // @[CSR.scala 262:22]
  wire  _T_308; // @[CSR.scala 265:26]
  wire  _T_311; // @[CSR.scala 269:26]
  wire  _T_312; // @[CSR.scala 270:26]
  wire  _T_313; // @[CSR.scala 271:26]
  wire  _T_314; // @[CSR.scala 272:26]
  wire  _T_315; // @[CSR.scala 273:26]
  wire [29:0] _GEN_262; // @[CSR.scala 273:56]
  wire [31:0] _T_316; // @[CSR.scala 273:56]
  wire [33:0] _GEN_263; // @[CSR.scala 273:63]
  wire [34:0] _T_317; // @[CSR.scala 273:63]
  wire  _T_318; // @[CSR.scala 274:26]
  wire [31:0] _T_319; // @[CSR.scala 274:60]
  wire  _T_320; // @[CSR.scala 275:26]
  wire  _T_321; // @[CSR.scala 276:26]
  wire  _T_322; // @[CSR.scala 277:26]
  wire  _T_323; // @[CSR.scala 278:26]
  wire  _T_324; // @[CSR.scala 279:26]
  wire  _T_325; // @[CSR.scala 280:26]
  wire  _T_326; // @[CSR.scala 281:26]
  wire  _T_327; // @[CSR.scala 282:26]
  wire  _T_328; // @[CSR.scala 283:26]
  wire [34:0] _GEN_61; // @[CSR.scala 273:40]
  wire [34:0] _GEN_73; // @[CSR.scala 272:44]
  wire [34:0] _GEN_86; // @[CSR.scala 271:44]
  wire [34:0] _GEN_100; // @[CSR.scala 270:42]
  wire [34:0] _GEN_114; // @[CSR.scala 269:41]
  wire [34:0] _GEN_129; // @[CSR.scala 265:39]
  wire [34:0] _GEN_146; // @[CSR.scala 261:39]
  wire  _GEN_156; // @[CSR.scala 255:38]
  wire [34:0] _GEN_167; // @[CSR.scala 255:38]
  wire  _GEN_177; // @[CSR.scala 254:21]
  wire [34:0] _GEN_188; // @[CSR.scala 254:21]
  wire  _GEN_200; // @[CSR.scala 249:24]
  wire [34:0] _GEN_209; // @[CSR.scala 249:24]
  wire [34:0] _GEN_218; // @[CSR.scala 237:19]
  wire [34:0] _GEN_239; // @[CSR.scala 236:19]
  assign csr_addr = io_inst[31:20]; // @[CSR.scala 100:25]
  assign rs1_addr = io_inst[19:15]; // @[CSR.scala 101:25]
  assign mstatus = {22'h0,3'h0,1'h0,PRV1,IE1,PRV,IE}; // @[Cat.scala 29:58]
  assign mip = {24'h0,MTIP,1'h0,2'h0,MSIP,1'h0,2'h0}; // @[Cat.scala 29:58]
  assign mie = {24'h0,MTIE,1'h0,2'h0,MSIE,1'h0,2'h0}; // @[Cat.scala 29:58]
  assign _GEN_0 = io_host_fromhost_valid ? io_host_fromhost_bits : mfromhost; // @[CSR.scala 165:32]
  assign _T_28 = 12'hc00 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_30 = 12'hc01 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_32 = 12'hc02 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_34 = 12'hc80 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_36 = 12'hc81 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_38 = 12'hc82 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_40 = 12'h900 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_42 = 12'h901 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_44 = 12'h902 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_46 = 12'h980 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_48 = 12'h981 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_50 = 12'h982 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_52 = 12'hf00 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_54 = 12'hf01 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_56 = 12'hf10 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_58 = 12'h301 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_60 = 12'h302 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_62 = 12'h304 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_64 = 12'h321 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_66 = 12'h701 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_68 = 12'h741 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_70 = 12'h340 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_72 = 12'h341 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_74 = 12'h342 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_76 = 12'h343 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_78 = 12'h344 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_80 = 12'h780 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_82 = 12'h781 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_84 = 12'h300 == csr_addr; // @[Lookup.scala 31:38]
  assign _T_85 = _T_84 ? mstatus : 32'h0; // @[Lookup.scala 33:37]
  assign _T_86 = _T_82 ? mfromhost : _T_85; // @[Lookup.scala 33:37]
  assign _T_87 = _T_80 ? mtohost : _T_86; // @[Lookup.scala 33:37]
  assign _T_88 = _T_78 ? mip : _T_87; // @[Lookup.scala 33:37]
  assign _T_89 = _T_76 ? mbadaddr : _T_88; // @[Lookup.scala 33:37]
  assign _T_90 = _T_74 ? mcause : _T_89; // @[Lookup.scala 33:37]
  assign _T_91 = _T_72 ? mepc : _T_90; // @[Lookup.scala 33:37]
  assign _T_92 = _T_70 ? mscratch : _T_91; // @[Lookup.scala 33:37]
  assign _T_93 = _T_68 ? timeh : _T_92; // @[Lookup.scala 33:37]
  assign _T_94 = _T_66 ? time_ : _T_93; // @[Lookup.scala 33:37]
  assign _T_95 = _T_64 ? mtimecmp : _T_94; // @[Lookup.scala 33:37]
  assign _T_96 = _T_62 ? mie : _T_95; // @[Lookup.scala 33:37]
  assign _T_97 = _T_60 ? 32'h0 : _T_96; // @[Lookup.scala 33:37]
  assign _T_98 = _T_58 ? 32'h100 : _T_97; // @[Lookup.scala 33:37]
  assign _T_99 = _T_56 ? 32'h0 : _T_98; // @[Lookup.scala 33:37]
  assign _T_100 = _T_54 ? 32'h0 : _T_99; // @[Lookup.scala 33:37]
  assign _T_101 = _T_52 ? 32'h100100 : _T_100; // @[Lookup.scala 33:37]
  assign _T_102 = _T_50 ? instreth : _T_101; // @[Lookup.scala 33:37]
  assign _T_103 = _T_48 ? timeh : _T_102; // @[Lookup.scala 33:37]
  assign _T_104 = _T_46 ? cycleh : _T_103; // @[Lookup.scala 33:37]
  assign _T_105 = _T_44 ? instret : _T_104; // @[Lookup.scala 33:37]
  assign _T_106 = _T_42 ? time_ : _T_105; // @[Lookup.scala 33:37]
  assign _T_107 = _T_40 ? cycle : _T_106; // @[Lookup.scala 33:37]
  assign _T_108 = _T_38 ? instreth : _T_107; // @[Lookup.scala 33:37]
  assign _T_109 = _T_36 ? timeh : _T_108; // @[Lookup.scala 33:37]
  assign _T_110 = _T_34 ? cycleh : _T_109; // @[Lookup.scala 33:37]
  assign _T_111 = _T_32 ? instret : _T_110; // @[Lookup.scala 33:37]
  assign _T_112 = _T_30 ? time_ : _T_111; // @[Lookup.scala 33:37]
  assign _T_114 = csr_addr[9:8]; // @[CSR.scala 203:27]
  assign privValid = _T_114 <= PRV; // @[CSR.scala 203:34]
  assign privInst = io_cmd == 3'h4; // @[CSR.scala 204:26]
  assign _T_115 = csr_addr[0]; // @[CSR.scala 205:40]
  assign _T_116 = _T_115 == 1'h0; // @[CSR.scala 205:31]
  assign _T_117 = privInst & _T_116; // @[CSR.scala 205:28]
  assign _T_118 = csr_addr[8]; // @[CSR.scala 205:56]
  assign _T_119 = _T_118 == 1'h0; // @[CSR.scala 205:47]
  assign isEcall = _T_117 & _T_119; // @[CSR.scala 205:44]
  assign _T_121 = privInst & _T_115; // @[CSR.scala 206:28]
  assign isEbreak = _T_121 & _T_119; // @[CSR.scala 206:44]
  assign isEret = _T_117 & _T_118; // @[CSR.scala 207:44]
  assign _T_186 = _T_28 | _T_30; // @[CSR.scala 208:61]
  assign _T_187 = _T_186 | _T_32; // @[CSR.scala 208:61]
  assign _T_188 = _T_187 | _T_34; // @[CSR.scala 208:61]
  assign _T_189 = _T_188 | _T_36; // @[CSR.scala 208:61]
  assign _T_190 = _T_189 | _T_38; // @[CSR.scala 208:61]
  assign _T_191 = _T_190 | _T_40; // @[CSR.scala 208:61]
  assign _T_192 = _T_191 | _T_42; // @[CSR.scala 208:61]
  assign _T_193 = _T_192 | _T_44; // @[CSR.scala 208:61]
  assign _T_194 = _T_193 | _T_46; // @[CSR.scala 208:61]
  assign _T_195 = _T_194 | _T_48; // @[CSR.scala 208:61]
  assign _T_196 = _T_195 | _T_50; // @[CSR.scala 208:61]
  assign _T_197 = _T_196 | _T_52; // @[CSR.scala 208:61]
  assign _T_198 = _T_197 | _T_54; // @[CSR.scala 208:61]
  assign _T_199 = _T_198 | _T_56; // @[CSR.scala 208:61]
  assign _T_200 = _T_199 | _T_58; // @[CSR.scala 208:61]
  assign _T_201 = _T_200 | _T_60; // @[CSR.scala 208:61]
  assign _T_202 = _T_201 | _T_62; // @[CSR.scala 208:61]
  assign _T_203 = _T_202 | _T_64; // @[CSR.scala 208:61]
  assign _T_204 = _T_203 | _T_66; // @[CSR.scala 208:61]
  assign _T_205 = _T_204 | _T_68; // @[CSR.scala 208:61]
  assign _T_206 = _T_205 | _T_70; // @[CSR.scala 208:61]
  assign _T_207 = _T_206 | _T_72; // @[CSR.scala 208:61]
  assign _T_208 = _T_207 | _T_74; // @[CSR.scala 208:61]
  assign _T_209 = _T_208 | _T_76; // @[CSR.scala 208:61]
  assign _T_210 = _T_209 | _T_78; // @[CSR.scala 208:61]
  assign _T_211 = _T_210 | _T_80; // @[CSR.scala 208:61]
  assign _T_212 = _T_211 | _T_82; // @[CSR.scala 208:61]
  assign csrValid = _T_212 | _T_84; // @[CSR.scala 208:61]
  assign _T_213 = csr_addr[11:10]; // @[CSR.scala 209:27]
  assign _T_214 = _T_213 == 2'h3; // @[CSR.scala 209:36]
  assign _T_215 = csr_addr == 12'h301; // @[CSR.scala 209:53]
  assign _T_216 = _T_214 | _T_215; // @[CSR.scala 209:41]
  assign _T_217 = csr_addr == 12'h302; // @[CSR.scala 209:79]
  assign csrRO = _T_216 | _T_217; // @[CSR.scala 209:67]
  assign _T_218 = io_cmd == 3'h1; // @[CSR.scala 210:26]
  assign _T_219 = io_cmd[1]; // @[CSR.scala 210:45]
  assign _T_220 = rs1_addr != 5'h0; // @[CSR.scala 210:61]
  assign _T_221 = _T_219 & _T_220; // @[CSR.scala 210:49]
  assign wen = _T_218 | _T_221; // @[CSR.scala 210:36]
  assign _T_222 = io_out | io_in; // @[CSR.scala 213:22]
  assign _T_223 = ~ io_in; // @[CSR.scala 214:24]
  assign _T_224 = io_out & _T_223; // @[CSR.scala 214:22]
  assign _T_225 = 3'h1 == io_cmd; // @[Mux.scala 80:60]
  assign _T_226 = _T_225 ? io_in : 32'h0; // @[Mux.scala 80:57]
  assign _T_227 = 3'h2 == io_cmd; // @[Mux.scala 80:60]
  assign _T_228 = _T_227 ? _T_222 : _T_226; // @[Mux.scala 80:57]
  assign _T_229 = 3'h3 == io_cmd; // @[Mux.scala 80:60]
  assign wdata = _T_229 ? _T_224 : _T_228; // @[Mux.scala 80:57]
  assign _T_230 = io_addr[1]; // @[CSR.scala 216:44]
  assign iaddrInvalid = io_pc_check & _T_230; // @[CSR.scala 216:34]
  assign _T_231 = io_addr[1:0]; // @[CSR.scala 218:29]
  assign _T_232 = _T_231 != 2'h0; // @[CSR.scala 218:36]
  assign _T_233 = io_addr[0]; // @[CSR.scala 218:65]
  assign _T_235 = 3'h1 == io_ld_type; // @[Mux.scala 80:60]
  assign _T_236 = _T_235 & _T_232; // @[Mux.scala 80:57]
  assign _T_237 = 3'h2 == io_ld_type; // @[Mux.scala 80:60]
  assign _T_238 = _T_237 ? _T_233 : _T_236; // @[Mux.scala 80:57]
  assign _T_239 = 3'h4 == io_ld_type; // @[Mux.scala 80:60]
  assign laddrInvalid = _T_239 ? _T_233 : _T_238; // @[Mux.scala 80:57]
  assign _T_243 = 2'h1 == io_st_type; // @[Mux.scala 80:60]
  assign _T_244 = _T_243 & _T_232; // @[Mux.scala 80:57]
  assign _T_245 = 2'h2 == io_st_type; // @[Mux.scala 80:60]
  assign saddrInvalid = _T_245 ? _T_233 : _T_244; // @[Mux.scala 80:57]
  assign _T_246 = io_illegal | iaddrInvalid; // @[CSR.scala 221:25]
  assign _T_247 = _T_246 | laddrInvalid; // @[CSR.scala 221:41]
  assign _T_248 = _T_247 | saddrInvalid; // @[CSR.scala 221:57]
  assign _T_249 = io_cmd[1:0]; // @[CSR.scala 222:20]
  assign _T_250 = _T_249 != 2'h0; // @[CSR.scala 222:27]
  assign _T_251 = csrValid == 1'h0; // @[CSR.scala 222:35]
  assign _T_252 = privValid == 1'h0; // @[CSR.scala 222:48]
  assign _T_253 = _T_251 | _T_252; // @[CSR.scala 222:45]
  assign _T_254 = _T_250 & _T_253; // @[CSR.scala 222:31]
  assign _T_255 = _T_248 | _T_254; // @[CSR.scala 221:73]
  assign _T_256 = wen & csrRO; // @[CSR.scala 222:67]
  assign _T_257 = _T_255 | _T_256; // @[CSR.scala 222:60]
  assign _T_259 = privInst & _T_252; // @[CSR.scala 223:24]
  assign _T_260 = _T_257 | _T_259; // @[CSR.scala 222:76]
  assign _T_261 = _T_260 | isEcall; // @[CSR.scala 223:39]
  assign _T_263 = {PRV, 6'h0}; // @[CSR.scala 224:27]
  assign _GEN_260 = {{24'd0}, _T_263}; // @[CSR.scala 224:20]
  assign _T_267 = time_ + 32'h1; // @[CSR.scala 228:16]
  assign _T_268 = time_ == 32'hffffffff; // @[CSR.scala 229:13]
  assign _T_270 = timeh + 32'h1; // @[CSR.scala 229:36]
  assign _GEN_1 = _T_268 ? _T_270 : timeh; // @[CSR.scala 229:19]
  assign _T_272 = cycle + 32'h1; // @[CSR.scala 230:18]
  assign _T_273 = cycle == 32'hffffffff; // @[CSR.scala 231:14]
  assign _T_275 = cycleh + 32'h1; // @[CSR.scala 231:39]
  assign _GEN_2 = _T_273 ? _T_275 : cycleh; // @[CSR.scala 231:20]
  assign _T_276 = io_inst != 32'h13; // @[CSR.scala 232:27]
  assign _T_277 = io_expt == 1'h0; // @[CSR.scala 232:52]
  assign _T_278 = _T_277 | isEcall; // @[CSR.scala 232:61]
  assign _T_279 = _T_278 | isEbreak; // @[CSR.scala 232:72]
  assign _T_280 = _T_276 & _T_279; // @[CSR.scala 232:48]
  assign _T_281 = io_stall == 1'h0; // @[CSR.scala 232:88]
  assign isInstRet = _T_280 & _T_281; // @[CSR.scala 232:85]
  assign _T_283 = instret + 32'h1; // @[CSR.scala 233:40]
  assign _GEN_3 = isInstRet ? _T_283 : instret; // @[CSR.scala 233:19]
  assign _T_284 = instret == 32'hffffffff; // @[CSR.scala 234:29]
  assign _T_285 = isInstRet & _T_284; // @[CSR.scala 234:18]
  assign _T_287 = instreth + 32'h1; // @[CSR.scala 234:58]
  assign _GEN_4 = _T_285 ? _T_287 : instreth; // @[CSR.scala 234:35]
  assign _T_289 = io_pc[31:2]; // @[CSR.scala 238:23]
  assign _T_290 = {_T_289, 2'h0}; // @[CSR.scala 238:28]
  assign _GEN_261 = {{2'd0}, PRV}; // @[CSR.scala 242:47]
  assign _T_292 = 4'h8 + _GEN_261; // @[CSR.scala 242:47]
  assign _T_293 = isEbreak ? 2'h3 : 2'h2; // @[CSR.scala 243:20]
  assign _T_294 = isEcall ? _T_292 : {{2'd0}, _T_293}; // @[CSR.scala 242:20]
  assign _T_295 = saddrInvalid ? 4'h6 : _T_294; // @[CSR.scala 241:20]
  assign _T_296 = laddrInvalid ? 4'h4 : _T_295; // @[CSR.scala 240:20]
  assign _T_297 = iaddrInvalid ? 4'h0 : _T_296; // @[CSR.scala 239:20]
  assign _T_298 = iaddrInvalid | laddrInvalid; // @[CSR.scala 248:25]
  assign _T_299 = _T_298 | saddrInvalid; // @[CSR.scala 248:41]
  assign _T_300 = csr_addr == 12'h300; // @[CSR.scala 255:21]
  assign _T_301 = wdata[5:4]; // @[CSR.scala 256:22]
  assign _T_302 = wdata[3]; // @[CSR.scala 257:22]
  assign _T_303 = wdata[2:1]; // @[CSR.scala 258:22]
  assign _T_304 = wdata[0]; // @[CSR.scala 259:22]
  assign _T_305 = csr_addr == 12'h344; // @[CSR.scala 261:26]
  assign _T_306 = wdata[7]; // @[CSR.scala 262:22]
  assign _T_308 = csr_addr == 12'h304; // @[CSR.scala 265:26]
  assign _T_311 = csr_addr == 12'h701; // @[CSR.scala 269:26]
  assign _T_312 = csr_addr == 12'h741; // @[CSR.scala 270:26]
  assign _T_313 = csr_addr == 12'h321; // @[CSR.scala 271:26]
  assign _T_314 = csr_addr == 12'h340; // @[CSR.scala 272:26]
  assign _T_315 = csr_addr == 12'h341; // @[CSR.scala 273:26]
  assign _GEN_262 = wdata[31:2]; // @[CSR.scala 273:56]
  assign _T_316 = {{2'd0}, _GEN_262}; // @[CSR.scala 273:56]
  assign _GEN_263 = {_T_316, 2'h0}; // @[CSR.scala 273:63]
  assign _T_317 = {{1'd0}, _GEN_263}; // @[CSR.scala 273:63]
  assign _T_318 = csr_addr == 12'h342; // @[CSR.scala 274:26]
  assign _T_319 = wdata & 32'h8000000f; // @[CSR.scala 274:60]
  assign _T_320 = csr_addr == 12'h343; // @[CSR.scala 275:26]
  assign _T_321 = csr_addr == 12'h780; // @[CSR.scala 276:26]
  assign _T_322 = csr_addr == 12'h781; // @[CSR.scala 277:26]
  assign _T_323 = csr_addr == 12'h900; // @[CSR.scala 278:26]
  assign _T_324 = csr_addr == 12'h901; // @[CSR.scala 279:26]
  assign _T_325 = csr_addr == 12'h902; // @[CSR.scala 280:26]
  assign _T_326 = csr_addr == 12'h980; // @[CSR.scala 281:26]
  assign _T_327 = csr_addr == 12'h981; // @[CSR.scala 282:26]
  assign _T_328 = csr_addr == 12'h982; // @[CSR.scala 283:26]
  assign _GEN_61 = _T_315 ? _T_317 : {{3'd0}, mepc}; // @[CSR.scala 273:40]
  assign _GEN_73 = _T_314 ? {{3'd0}, mepc} : _GEN_61; // @[CSR.scala 272:44]
  assign _GEN_86 = _T_313 ? {{3'd0}, mepc} : _GEN_73; // @[CSR.scala 271:44]
  assign _GEN_100 = _T_312 ? {{3'd0}, mepc} : _GEN_86; // @[CSR.scala 270:42]
  assign _GEN_114 = _T_311 ? {{3'd0}, mepc} : _GEN_100; // @[CSR.scala 269:41]
  assign _GEN_129 = _T_308 ? {{3'd0}, mepc} : _GEN_114; // @[CSR.scala 265:39]
  assign _GEN_146 = _T_305 ? {{3'd0}, mepc} : _GEN_129; // @[CSR.scala 261:39]
  assign _GEN_156 = _T_300 ? _T_302 : IE1; // @[CSR.scala 255:38]
  assign _GEN_167 = _T_300 ? {{3'd0}, mepc} : _GEN_146; // @[CSR.scala 255:38]
  assign _GEN_177 = wen ? _GEN_156 : IE1; // @[CSR.scala 254:21]
  assign _GEN_188 = wen ? _GEN_167 : {{3'd0}, mepc}; // @[CSR.scala 254:21]
  assign _GEN_200 = isEret | _GEN_177; // @[CSR.scala 249:24]
  assign _GEN_209 = isEret ? {{3'd0}, mepc} : _GEN_188; // @[CSR.scala 249:24]
  assign _GEN_218 = io_expt ? {{3'd0}, _T_290} : _GEN_209; // @[CSR.scala 237:19]
  assign _GEN_239 = _T_281 ? _GEN_218 : {{3'd0}, mepc}; // @[CSR.scala 236:19]
  assign io_out = _T_28 ? cycle : _T_112; // @[CSR.scala 201:10]
  assign io_expt = _T_261 | isEbreak; // @[CSR.scala 221:11]
  assign io_evec = 32'h100 + _GEN_260; // @[CSR.scala 224:11]
  assign io_epc = mepc; // @[CSR.scala 225:11]
  assign io_host_tohost = mtohost; // @[CSR.scala 164:18]
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
  time_ = _RAND_0[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  timeh = _RAND_1[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  cycle = _RAND_2[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {1{`RANDOM}};
  cycleh = _RAND_3[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {1{`RANDOM}};
  instret = _RAND_4[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  instreth = _RAND_5[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_6 = {1{`RANDOM}};
  PRV = _RAND_6[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_7 = {1{`RANDOM}};
  PRV1 = _RAND_7[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_8 = {1{`RANDOM}};
  IE = _RAND_8[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_9 = {1{`RANDOM}};
  IE1 = _RAND_9[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_10 = {1{`RANDOM}};
  MTIP = _RAND_10[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_11 = {1{`RANDOM}};
  MTIE = _RAND_11[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_12 = {1{`RANDOM}};
  MSIP = _RAND_12[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_13 = {1{`RANDOM}};
  MSIE = _RAND_13[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_14 = {1{`RANDOM}};
  mtimecmp = _RAND_14[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_15 = {1{`RANDOM}};
  mscratch = _RAND_15[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_16 = {1{`RANDOM}};
  mepc = _RAND_16[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_17 = {1{`RANDOM}};
  mcause = _RAND_17[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_18 = {1{`RANDOM}};
  mbadaddr = _RAND_18[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_19 = {1{`RANDOM}};
  mtohost = _RAND_19[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_20 = {1{`RANDOM}};
  mfromhost = _RAND_20[31:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      time_ <= 32'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        time_ <= _T_267;
      end else if (isEret) begin
        time_ <= _T_267;
      end else if (wen) begin
        if (_T_300) begin
          time_ <= _T_267;
        end else if (_T_305) begin
          time_ <= _T_267;
        end else if (_T_308) begin
          time_ <= _T_267;
        end else if (_T_311) begin
          if (_T_229) begin
            time_ <= _T_224;
          end else if (_T_227) begin
            time_ <= _T_222;
          end else if (_T_225) begin
            time_ <= io_in;
          end else begin
            time_ <= 32'h0;
          end
        end else if (_T_312) begin
          time_ <= _T_267;
        end else if (_T_313) begin
          time_ <= _T_267;
        end else if (_T_314) begin
          time_ <= _T_267;
        end else if (_T_315) begin
          time_ <= _T_267;
        end else if (_T_318) begin
          time_ <= _T_267;
        end else if (_T_320) begin
          time_ <= _T_267;
        end else if (_T_321) begin
          time_ <= _T_267;
        end else if (_T_322) begin
          time_ <= _T_267;
        end else if (_T_323) begin
          time_ <= _T_267;
        end else if (_T_324) begin
          if (_T_229) begin
            time_ <= _T_224;
          end else if (_T_227) begin
            time_ <= _T_222;
          end else if (_T_225) begin
            time_ <= io_in;
          end else begin
            time_ <= 32'h0;
          end
        end else begin
          time_ <= _T_267;
        end
      end else begin
        time_ <= _T_267;
      end
    end else begin
      time_ <= _T_267;
    end
    if (reset) begin
      timeh <= 32'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        if (_T_268) begin
          timeh <= _T_270;
        end
      end else if (isEret) begin
        if (_T_268) begin
          timeh <= _T_270;
        end
      end else if (wen) begin
        if (_T_300) begin
          if (_T_268) begin
            timeh <= _T_270;
          end
        end else if (_T_305) begin
          if (_T_268) begin
            timeh <= _T_270;
          end
        end else if (_T_308) begin
          timeh <= _GEN_1;
        end else if (_T_311) begin
          timeh <= _GEN_1;
        end else if (_T_312) begin
          if (_T_229) begin
            timeh <= _T_224;
          end else if (_T_227) begin
            timeh <= _T_222;
          end else if (_T_225) begin
            timeh <= io_in;
          end else begin
            timeh <= 32'h0;
          end
        end else if (_T_313) begin
          timeh <= _GEN_1;
        end else if (_T_314) begin
          timeh <= _GEN_1;
        end else if (_T_315) begin
          timeh <= _GEN_1;
        end else if (_T_318) begin
          timeh <= _GEN_1;
        end else if (_T_320) begin
          timeh <= _GEN_1;
        end else if (_T_321) begin
          timeh <= _GEN_1;
        end else if (_T_322) begin
          timeh <= _GEN_1;
        end else if (_T_323) begin
          timeh <= _GEN_1;
        end else if (_T_324) begin
          timeh <= _GEN_1;
        end else if (_T_325) begin
          timeh <= _GEN_1;
        end else if (_T_326) begin
          timeh <= _GEN_1;
        end else if (_T_327) begin
          if (_T_229) begin
            timeh <= _T_224;
          end else if (_T_227) begin
            timeh <= _T_222;
          end else if (_T_225) begin
            timeh <= io_in;
          end else begin
            timeh <= 32'h0;
          end
        end else begin
          timeh <= _GEN_1;
        end
      end else begin
        timeh <= _GEN_1;
      end
    end else begin
      timeh <= _GEN_1;
    end
    if (reset) begin
      cycle <= 32'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        cycle <= _T_272;
      end else if (isEret) begin
        cycle <= _T_272;
      end else if (wen) begin
        if (_T_300) begin
          cycle <= _T_272;
        end else if (_T_305) begin
          cycle <= _T_272;
        end else if (_T_308) begin
          cycle <= _T_272;
        end else if (_T_311) begin
          cycle <= _T_272;
        end else if (_T_312) begin
          cycle <= _T_272;
        end else if (_T_313) begin
          cycle <= _T_272;
        end else if (_T_314) begin
          cycle <= _T_272;
        end else if (_T_315) begin
          cycle <= _T_272;
        end else if (_T_318) begin
          cycle <= _T_272;
        end else if (_T_320) begin
          cycle <= _T_272;
        end else if (_T_321) begin
          cycle <= _T_272;
        end else if (_T_322) begin
          cycle <= _T_272;
        end else if (_T_323) begin
          cycle <= wdata;
        end else begin
          cycle <= _T_272;
        end
      end else begin
        cycle <= _T_272;
      end
    end else begin
      cycle <= _T_272;
    end
    if (reset) begin
      cycleh <= 32'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        if (_T_273) begin
          cycleh <= _T_275;
        end
      end else if (isEret) begin
        if (_T_273) begin
          cycleh <= _T_275;
        end
      end else if (wen) begin
        if (_T_300) begin
          if (_T_273) begin
            cycleh <= _T_275;
          end
        end else if (_T_305) begin
          if (_T_273) begin
            cycleh <= _T_275;
          end
        end else if (_T_308) begin
          cycleh <= _GEN_2;
        end else if (_T_311) begin
          cycleh <= _GEN_2;
        end else if (_T_312) begin
          cycleh <= _GEN_2;
        end else if (_T_313) begin
          cycleh <= _GEN_2;
        end else if (_T_314) begin
          cycleh <= _GEN_2;
        end else if (_T_315) begin
          cycleh <= _GEN_2;
        end else if (_T_318) begin
          cycleh <= _GEN_2;
        end else if (_T_320) begin
          cycleh <= _GEN_2;
        end else if (_T_321) begin
          cycleh <= _GEN_2;
        end else if (_T_322) begin
          cycleh <= _GEN_2;
        end else if (_T_323) begin
          cycleh <= _GEN_2;
        end else if (_T_324) begin
          cycleh <= _GEN_2;
        end else if (_T_325) begin
          cycleh <= _GEN_2;
        end else if (_T_326) begin
          cycleh <= wdata;
        end else begin
          cycleh <= _GEN_2;
        end
      end else begin
        cycleh <= _GEN_2;
      end
    end else begin
      cycleh <= _GEN_2;
    end
    if (reset) begin
      instret <= 32'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        if (isInstRet) begin
          instret <= _T_283;
        end
      end else if (isEret) begin
        if (isInstRet) begin
          instret <= _T_283;
        end
      end else if (wen) begin
        if (_T_300) begin
          if (isInstRet) begin
            instret <= _T_283;
          end
        end else if (_T_305) begin
          if (isInstRet) begin
            instret <= _T_283;
          end
        end else if (_T_308) begin
          instret <= _GEN_3;
        end else if (_T_311) begin
          instret <= _GEN_3;
        end else if (_T_312) begin
          instret <= _GEN_3;
        end else if (_T_313) begin
          instret <= _GEN_3;
        end else if (_T_314) begin
          instret <= _GEN_3;
        end else if (_T_315) begin
          instret <= _GEN_3;
        end else if (_T_318) begin
          instret <= _GEN_3;
        end else if (_T_320) begin
          instret <= _GEN_3;
        end else if (_T_321) begin
          instret <= _GEN_3;
        end else if (_T_322) begin
          instret <= _GEN_3;
        end else if (_T_323) begin
          instret <= _GEN_3;
        end else if (_T_324) begin
          instret <= _GEN_3;
        end else if (_T_325) begin
          instret <= wdata;
        end else begin
          instret <= _GEN_3;
        end
      end else begin
        instret <= _GEN_3;
      end
    end else begin
      instret <= _GEN_3;
    end
    if (reset) begin
      instreth <= 32'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        if (_T_285) begin
          instreth <= _T_287;
        end
      end else if (isEret) begin
        if (_T_285) begin
          instreth <= _T_287;
        end
      end else if (wen) begin
        if (_T_300) begin
          if (_T_285) begin
            instreth <= _T_287;
          end
        end else if (_T_305) begin
          if (_T_285) begin
            instreth <= _T_287;
          end
        end else if (_T_308) begin
          instreth <= _GEN_4;
        end else if (_T_311) begin
          instreth <= _GEN_4;
        end else if (_T_312) begin
          instreth <= _GEN_4;
        end else if (_T_313) begin
          instreth <= _GEN_4;
        end else if (_T_314) begin
          instreth <= _GEN_4;
        end else if (_T_315) begin
          instreth <= _GEN_4;
        end else if (_T_318) begin
          instreth <= _GEN_4;
        end else if (_T_320) begin
          instreth <= _GEN_4;
        end else if (_T_321) begin
          instreth <= _GEN_4;
        end else if (_T_322) begin
          instreth <= _GEN_4;
        end else if (_T_323) begin
          instreth <= _GEN_4;
        end else if (_T_324) begin
          instreth <= _GEN_4;
        end else if (_T_325) begin
          instreth <= _GEN_4;
        end else if (_T_326) begin
          instreth <= _GEN_4;
        end else if (_T_327) begin
          instreth <= _GEN_4;
        end else if (_T_328) begin
          instreth <= wdata;
        end else begin
          instreth <= _GEN_4;
        end
      end else begin
        instreth <= _GEN_4;
      end
    end else begin
      instreth <= _GEN_4;
    end
    if (reset) begin
      PRV <= 2'h3;
    end else if (_T_281) begin
      if (io_expt) begin
        PRV <= 2'h3;
      end else if (isEret) begin
        PRV <= PRV1;
      end else if (wen) begin
        if (_T_300) begin
          PRV <= _T_303;
        end
      end
    end
    if (reset) begin
      PRV1 <= 2'h3;
    end else if (_T_281) begin
      if (io_expt) begin
        PRV1 <= PRV;
      end else if (isEret) begin
        PRV1 <= 2'h0;
      end else if (wen) begin
        if (_T_300) begin
          PRV1 <= _T_301;
        end
      end
    end
    if (reset) begin
      IE <= 1'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        IE <= 1'h0;
      end else if (isEret) begin
        IE <= IE1;
      end else if (wen) begin
        if (_T_300) begin
          IE <= _T_304;
        end
      end
    end
    if (reset) begin
      IE1 <= 1'h0;
    end else if (_T_281) begin
      if (io_expt) begin
        IE1 <= IE;
      end else begin
        IE1 <= _GEN_200;
      end
    end
    if (reset) begin
      MTIP <= 1'h0;
    end else if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (_T_305) begin
                MTIP <= _T_306;
              end
            end
          end
        end
      end
    end
    if (reset) begin
      MTIE <= 1'h0;
    end else if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (!(_T_305)) begin
                if (_T_308) begin
                  MTIE <= _T_306;
                end
              end
            end
          end
        end
      end
    end
    if (reset) begin
      MSIP <= 1'h0;
    end else if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (_T_305) begin
                MSIP <= _T_302;
              end
            end
          end
        end
      end
    end
    if (reset) begin
      MSIE <= 1'h0;
    end else if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (!(_T_305)) begin
                if (_T_308) begin
                  MSIE <= _T_302;
                end
              end
            end
          end
        end
      end
    end
    if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (!(_T_305)) begin
                if (!(_T_308)) begin
                  if (!(_T_311)) begin
                    if (!(_T_312)) begin
                      if (_T_313) begin
                        mtimecmp <= wdata;
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
    if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (!(_T_305)) begin
                if (!(_T_308)) begin
                  if (!(_T_311)) begin
                    if (!(_T_312)) begin
                      if (!(_T_313)) begin
                        if (_T_314) begin
                          mscratch <= wdata;
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
    mepc <= _GEN_239[31:0];
    if (_T_281) begin
      if (io_expt) begin
        mcause <= {{28'd0}, _T_297};
      end else if (!(isEret)) begin
        if (wen) begin
          if (!(_T_300)) begin
            if (!(_T_305)) begin
              if (!(_T_308)) begin
                if (!(_T_311)) begin
                  if (!(_T_312)) begin
                    if (!(_T_313)) begin
                      if (!(_T_314)) begin
                        if (!(_T_315)) begin
                          if (_T_318) begin
                            mcause <= _T_319;
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
    if (_T_281) begin
      if (io_expt) begin
        if (_T_299) begin
          mbadaddr <= io_addr;
        end
      end else if (!(isEret)) begin
        if (wen) begin
          if (!(_T_300)) begin
            if (!(_T_305)) begin
              if (!(_T_308)) begin
                if (!(_T_311)) begin
                  if (!(_T_312)) begin
                    if (!(_T_313)) begin
                      if (!(_T_314)) begin
                        if (!(_T_315)) begin
                          if (!(_T_318)) begin
                            if (_T_320) begin
                              mbadaddr <= wdata;
                            end
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
    if (reset) begin
      mtohost <= 32'h0;
    end else if (_T_281) begin
      if (!(io_expt)) begin
        if (!(isEret)) begin
          if (wen) begin
            if (!(_T_300)) begin
              if (!(_T_305)) begin
                if (!(_T_308)) begin
                  if (!(_T_311)) begin
                    if (!(_T_312)) begin
                      if (!(_T_313)) begin
                        if (!(_T_314)) begin
                          if (!(_T_315)) begin
                            if (!(_T_318)) begin
                              if (!(_T_320)) begin
                                if (_T_321) begin
                                  mtohost <= wdata;
                                end
                              end
                            end
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
    if (_T_281) begin
      if (io_expt) begin
        if (io_host_fromhost_valid) begin
          mfromhost <= io_host_fromhost_bits;
        end
      end else if (isEret) begin
        if (io_host_fromhost_valid) begin
          mfromhost <= io_host_fromhost_bits;
        end
      end else if (wen) begin
        if (_T_300) begin
          if (io_host_fromhost_valid) begin
            mfromhost <= io_host_fromhost_bits;
          end
        end else if (_T_305) begin
          if (io_host_fromhost_valid) begin
            mfromhost <= io_host_fromhost_bits;
          end
        end else if (_T_308) begin
          mfromhost <= _GEN_0;
        end else if (_T_311) begin
          mfromhost <= _GEN_0;
        end else if (_T_312) begin
          mfromhost <= _GEN_0;
        end else if (_T_313) begin
          mfromhost <= _GEN_0;
        end else if (_T_314) begin
          mfromhost <= _GEN_0;
        end else if (_T_315) begin
          mfromhost <= _GEN_0;
        end else if (_T_318) begin
          mfromhost <= _GEN_0;
        end else if (_T_320) begin
          mfromhost <= _GEN_0;
        end else if (_T_321) begin
          mfromhost <= _GEN_0;
        end else if (_T_322) begin
          mfromhost <= wdata;
        end else begin
          mfromhost <= _GEN_0;
        end
      end else begin
        mfromhost <= _GEN_0;
      end
    end else begin
      mfromhost <= _GEN_0;
    end
  end
endmodule
