module Cache(
  input         clock,
  input         reset,
  input         io_cpu_abort,
  input         io_cpu_req_valid,
  input  [31:0] io_cpu_req_bits_addr,
  input  [31:0] io_cpu_req_bits_data,
  input  [3:0]  io_cpu_req_bits_mask,
  output        io_cpu_resp_valid,
  output [31:0] io_cpu_resp_bits_data,
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
  input  [63:0] io_nasti_r_bits_data
);
  reg [19:0] metaMem_tag [0:255]; // @[Cache.scala 62:29]
  reg [31:0] _RAND_0;
  wire [19:0] metaMem_tag_rmeta_data; // @[Cache.scala 62:29]
  wire [7:0] metaMem_tag_rmeta_addr; // @[Cache.scala 62:29]
  wire [19:0] metaMem_tag__T_87_data; // @[Cache.scala 62:29]
  wire [7:0] metaMem_tag__T_87_addr; // @[Cache.scala 62:29]
  wire  metaMem_tag__T_87_mask; // @[Cache.scala 62:29]
  wire  metaMem_tag__T_87_en; // @[Cache.scala 62:29]
  reg  metaMem_tag_rmeta_en_pipe_0;
  reg [31:0] _RAND_1;
  reg [7:0] metaMem_tag_rmeta_addr_pipe_0;
  reg [31:0] _RAND_2;
  reg [7:0] dataMem_0_0 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_3;
  wire [7:0] dataMem_0_0__T_22_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_0__T_22_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_0__T_98_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_0__T_98_addr; // @[Cache.scala 63:46]
  wire  dataMem_0_0__T_98_mask; // @[Cache.scala 63:46]
  wire  dataMem_0_0__T_98_en; // @[Cache.scala 63:46]
  reg  dataMem_0_0__T_22_en_pipe_0;
  reg [31:0] _RAND_4;
  reg [7:0] dataMem_0_0__T_22_addr_pipe_0;
  reg [31:0] _RAND_5;
  reg [7:0] dataMem_0_1 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_6;
  wire [7:0] dataMem_0_1__T_22_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_1__T_22_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_1__T_98_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_1__T_98_addr; // @[Cache.scala 63:46]
  wire  dataMem_0_1__T_98_mask; // @[Cache.scala 63:46]
  wire  dataMem_0_1__T_98_en; // @[Cache.scala 63:46]
  reg  dataMem_0_1__T_22_en_pipe_0;
  reg [31:0] _RAND_7;
  reg [7:0] dataMem_0_1__T_22_addr_pipe_0;
  reg [31:0] _RAND_8;
  reg [7:0] dataMem_0_2 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_9;
  wire [7:0] dataMem_0_2__T_22_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_2__T_22_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_2__T_98_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_2__T_98_addr; // @[Cache.scala 63:46]
  wire  dataMem_0_2__T_98_mask; // @[Cache.scala 63:46]
  wire  dataMem_0_2__T_98_en; // @[Cache.scala 63:46]
  reg  dataMem_0_2__T_22_en_pipe_0;
  reg [31:0] _RAND_10;
  reg [7:0] dataMem_0_2__T_22_addr_pipe_0;
  reg [31:0] _RAND_11;
  reg [7:0] dataMem_0_3 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_12;
  wire [7:0] dataMem_0_3__T_22_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_3__T_22_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_3__T_98_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_0_3__T_98_addr; // @[Cache.scala 63:46]
  wire  dataMem_0_3__T_98_mask; // @[Cache.scala 63:46]
  wire  dataMem_0_3__T_98_en; // @[Cache.scala 63:46]
  reg  dataMem_0_3__T_22_en_pipe_0;
  reg [31:0] _RAND_13;
  reg [7:0] dataMem_0_3__T_22_addr_pipe_0;
  reg [31:0] _RAND_14;
  reg [7:0] dataMem_1_0 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_15;
  wire [7:0] dataMem_1_0__T_29_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_0__T_29_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_0__T_109_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_0__T_109_addr; // @[Cache.scala 63:46]
  wire  dataMem_1_0__T_109_mask; // @[Cache.scala 63:46]
  wire  dataMem_1_0__T_109_en; // @[Cache.scala 63:46]
  reg  dataMem_1_0__T_29_en_pipe_0;
  reg [31:0] _RAND_16;
  reg [7:0] dataMem_1_0__T_29_addr_pipe_0;
  reg [31:0] _RAND_17;
  reg [7:0] dataMem_1_1 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_18;
  wire [7:0] dataMem_1_1__T_29_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_1__T_29_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_1__T_109_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_1__T_109_addr; // @[Cache.scala 63:46]
  wire  dataMem_1_1__T_109_mask; // @[Cache.scala 63:46]
  wire  dataMem_1_1__T_109_en; // @[Cache.scala 63:46]
  reg  dataMem_1_1__T_29_en_pipe_0;
  reg [31:0] _RAND_19;
  reg [7:0] dataMem_1_1__T_29_addr_pipe_0;
  reg [31:0] _RAND_20;
  reg [7:0] dataMem_1_2 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_21;
  wire [7:0] dataMem_1_2__T_29_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_2__T_29_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_2__T_109_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_2__T_109_addr; // @[Cache.scala 63:46]
  wire  dataMem_1_2__T_109_mask; // @[Cache.scala 63:46]
  wire  dataMem_1_2__T_109_en; // @[Cache.scala 63:46]
  reg  dataMem_1_2__T_29_en_pipe_0;
  reg [31:0] _RAND_22;
  reg [7:0] dataMem_1_2__T_29_addr_pipe_0;
  reg [31:0] _RAND_23;
  reg [7:0] dataMem_1_3 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_24;
  wire [7:0] dataMem_1_3__T_29_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_3__T_29_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_3__T_109_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_1_3__T_109_addr; // @[Cache.scala 63:46]
  wire  dataMem_1_3__T_109_mask; // @[Cache.scala 63:46]
  wire  dataMem_1_3__T_109_en; // @[Cache.scala 63:46]
  reg  dataMem_1_3__T_29_en_pipe_0;
  reg [31:0] _RAND_25;
  reg [7:0] dataMem_1_3__T_29_addr_pipe_0;
  reg [31:0] _RAND_26;
  reg [7:0] dataMem_2_0 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_27;
  wire [7:0] dataMem_2_0__T_36_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_0__T_36_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_0__T_120_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_0__T_120_addr; // @[Cache.scala 63:46]
  wire  dataMem_2_0__T_120_mask; // @[Cache.scala 63:46]
  wire  dataMem_2_0__T_120_en; // @[Cache.scala 63:46]
  reg  dataMem_2_0__T_36_en_pipe_0;
  reg [31:0] _RAND_28;
  reg [7:0] dataMem_2_0__T_36_addr_pipe_0;
  reg [31:0] _RAND_29;
  reg [7:0] dataMem_2_1 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_30;
  wire [7:0] dataMem_2_1__T_36_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_1__T_36_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_1__T_120_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_1__T_120_addr; // @[Cache.scala 63:46]
  wire  dataMem_2_1__T_120_mask; // @[Cache.scala 63:46]
  wire  dataMem_2_1__T_120_en; // @[Cache.scala 63:46]
  reg  dataMem_2_1__T_36_en_pipe_0;
  reg [31:0] _RAND_31;
  reg [7:0] dataMem_2_1__T_36_addr_pipe_0;
  reg [31:0] _RAND_32;
  reg [7:0] dataMem_2_2 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_33;
  wire [7:0] dataMem_2_2__T_36_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_2__T_36_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_2__T_120_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_2__T_120_addr; // @[Cache.scala 63:46]
  wire  dataMem_2_2__T_120_mask; // @[Cache.scala 63:46]
  wire  dataMem_2_2__T_120_en; // @[Cache.scala 63:46]
  reg  dataMem_2_2__T_36_en_pipe_0;
  reg [31:0] _RAND_34;
  reg [7:0] dataMem_2_2__T_36_addr_pipe_0;
  reg [31:0] _RAND_35;
  reg [7:0] dataMem_2_3 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_36;
  wire [7:0] dataMem_2_3__T_36_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_3__T_36_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_3__T_120_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_2_3__T_120_addr; // @[Cache.scala 63:46]
  wire  dataMem_2_3__T_120_mask; // @[Cache.scala 63:46]
  wire  dataMem_2_3__T_120_en; // @[Cache.scala 63:46]
  reg  dataMem_2_3__T_36_en_pipe_0;
  reg [31:0] _RAND_37;
  reg [7:0] dataMem_2_3__T_36_addr_pipe_0;
  reg [31:0] _RAND_38;
  reg [7:0] dataMem_3_0 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_39;
  wire [7:0] dataMem_3_0__T_43_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_0__T_43_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_0__T_131_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_0__T_131_addr; // @[Cache.scala 63:46]
  wire  dataMem_3_0__T_131_mask; // @[Cache.scala 63:46]
  wire  dataMem_3_0__T_131_en; // @[Cache.scala 63:46]
  reg  dataMem_3_0__T_43_en_pipe_0;
  reg [31:0] _RAND_40;
  reg [7:0] dataMem_3_0__T_43_addr_pipe_0;
  reg [31:0] _RAND_41;
  reg [7:0] dataMem_3_1 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_42;
  wire [7:0] dataMem_3_1__T_43_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_1__T_43_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_1__T_131_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_1__T_131_addr; // @[Cache.scala 63:46]
  wire  dataMem_3_1__T_131_mask; // @[Cache.scala 63:46]
  wire  dataMem_3_1__T_131_en; // @[Cache.scala 63:46]
  reg  dataMem_3_1__T_43_en_pipe_0;
  reg [31:0] _RAND_43;
  reg [7:0] dataMem_3_1__T_43_addr_pipe_0;
  reg [31:0] _RAND_44;
  reg [7:0] dataMem_3_2 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_45;
  wire [7:0] dataMem_3_2__T_43_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_2__T_43_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_2__T_131_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_2__T_131_addr; // @[Cache.scala 63:46]
  wire  dataMem_3_2__T_131_mask; // @[Cache.scala 63:46]
  wire  dataMem_3_2__T_131_en; // @[Cache.scala 63:46]
  reg  dataMem_3_2__T_43_en_pipe_0;
  reg [31:0] _RAND_46;
  reg [7:0] dataMem_3_2__T_43_addr_pipe_0;
  reg [31:0] _RAND_47;
  reg [7:0] dataMem_3_3 [0:255]; // @[Cache.scala 63:46]
  reg [31:0] _RAND_48;
  wire [7:0] dataMem_3_3__T_43_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_3__T_43_addr; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_3__T_131_data; // @[Cache.scala 63:46]
  wire [7:0] dataMem_3_3__T_131_addr; // @[Cache.scala 63:46]
  wire  dataMem_3_3__T_131_mask; // @[Cache.scala 63:46]
  wire  dataMem_3_3__T_131_en; // @[Cache.scala 63:46]
  reg  dataMem_3_3__T_43_en_pipe_0;
  reg [31:0] _RAND_49;
  reg [7:0] dataMem_3_3__T_43_addr_pipe_0;
  reg [31:0] _RAND_50;
  reg [2:0] state; // @[Cache.scala 58:22]
  reg [31:0] _RAND_51;
  reg [255:0] v; // @[Cache.scala 60:25]
  reg [255:0] _RAND_52;
  reg [255:0] d; // @[Cache.scala 61:25]
  reg [255:0] _RAND_53;
  reg [31:0] addr_reg; // @[Cache.scala 65:21]
  reg [31:0] _RAND_54;
  reg [31:0] cpu_data; // @[Cache.scala 66:21]
  reg [31:0] _RAND_55;
  reg [3:0] cpu_mask; // @[Cache.scala 67:21]
  reg [31:0] _RAND_56;
  wire  _T; // @[Decoupled.scala 40:37]
  reg  read_count; // @[Counter.scala 29:33]
  reg [31:0] _RAND_57;
  wire  _T_3; // @[Counter.scala 38:22]
  wire  read_wrap_out; // @[Counter.scala 72:20]
  wire  _T_4; // @[Decoupled.scala 40:37]
  reg  write_count; // @[Counter.scala 29:33]
  reg [31:0] _RAND_58;
  wire  _T_7; // @[Counter.scala 38:22]
  wire  write_wrap_out; // @[Counter.scala 72:20]
  wire  is_idle; // @[Cache.scala 74:25]
  wire  is_read; // @[Cache.scala 75:25]
  wire  is_write; // @[Cache.scala 76:25]
  wire  _T_8; // @[Cache.scala 77:25]
  wire  is_alloc; // @[Cache.scala 77:38]
  reg  is_alloc_reg; // @[Cache.scala 78:29]
  reg [31:0] _RAND_59;
  wire [7:0] idx_reg; // @[Cache.scala 88:26]
  wire [255:0] _T_51; // @[Cache.scala 97:11]
  wire  _T_52; // @[Cache.scala 97:11]
  wire [19:0] tag_reg; // @[Cache.scala 87:26]
  wire  _T_53; // @[Cache.scala 97:34]
  wire  hit; // @[Cache.scala 97:21]
  wire  _T_9; // @[Cache.scala 81:30]
  wire  _T_10; // @[Cache.scala 81:22]
  wire  _T_11; // @[Cache.scala 81:50]
  wire  _T_12; // @[Cache.scala 81:47]
  wire  wen; // @[Cache.scala 81:64]
  wire  _T_13; // @[Cache.scala 82:13]
  wire  _T_14; // @[Cache.scala 82:30]
  wire  _T_15; // @[Cache.scala 82:18]
  reg  ren_reg; // @[Cache.scala 83:24]
  reg [31:0] _RAND_60;
  wire [1:0] off_reg; // @[Cache.scala 89:26]
  wire [63:0] _T_47; // @[Cat.scala 29:58]
  wire [127:0] rdata; // @[Cat.scala 29:58]
  reg [127:0] rdata_buf; // @[Reg.scala 15:16]
  reg [127:0] _RAND_61;
  wire [127:0] _GEN_10; // @[Reg.scala 16:19]
  reg [63:0] refill_buf_0; // @[Cache.scala 94:23]
  reg [63:0] _RAND_62;
  reg [63:0] refill_buf_1; // @[Cache.scala 94:23]
  reg [63:0] _RAND_63;
  wire [127:0] _T_49; // @[Cache.scala 95:43]
  wire [127:0] read; // @[Cache.scala 95:17]
  wire [31:0] _T_55; // @[Cache.scala 100:62]
  wire [31:0] _T_56; // @[Cache.scala 100:62]
  wire [31:0] _T_57; // @[Cache.scala 100:62]
  wire [31:0] _T_58; // @[Cache.scala 100:62]
  wire [31:0] _GEN_12; // @[Cache.scala 100:25]
  wire [31:0] _GEN_13; // @[Cache.scala 100:25]
  wire  _T_60; // @[Cache.scala 101:47]
  wire  _T_61; // @[Cache.scala 101:36]
  wire  _T_62; // @[Cache.scala 101:83]
  wire  _T_63; // @[Cache.scala 101:73]
  wire  _T_64; // @[Cache.scala 101:70]
  wire  _T_66; // @[Cache.scala 112:19]
  wire [3:0] _T_67; // @[Cat.scala 29:58]
  wire [18:0] _GEN_144; // @[Cache.scala 112:40]
  wire [18:0] _T_68; // @[Cache.scala 112:40]
  wire [19:0] _T_69; // @[Cache.scala 112:80]
  wire [19:0] wmask; // @[Cache.scala 112:18]
  wire [127:0] _T_72; // @[Cat.scala 29:58]
  wire [127:0] _T_73; // @[Cat.scala 29:58]
  wire [127:0] wdata; // @[Cache.scala 113:18]
  wire [255:0] _T_74; // @[Cache.scala 117:18]
  wire [255:0] _T_75; // @[Cache.scala 117:18]
  wire [255:0] _T_82; // @[Cache.scala 118:18]
  wire [255:0] _T_83; // @[Cache.scala 118:18]
  wire [255:0] _T_84; // @[Cache.scala 118:18]
  wire [255:0] _T_85; // @[Cache.scala 118:18]
  wire [3:0] _T_93; // @[Cache.scala 124:37]
  wire [3:0] _T_104; // @[Cache.scala 124:37]
  wire [3:0] _T_115; // @[Cache.scala 124:37]
  wire [3:0] _T_126; // @[Cache.scala 124:37]
  wire [27:0] _T_132; // @[Cat.scala 29:58]
  wire [31:0] _GEN_145; // @[Cache.scala 130:33]
  wire [34:0] _T_133; // @[Cache.scala 130:33]
  wire [27:0] _T_139; // @[Cat.scala 29:58]
  wire [31:0] _GEN_146; // @[Cache.scala 138:35]
  wire [34:0] _T_140; // @[Cache.scala 138:35]
  wire [63:0] _T_144; // @[Cache.scala 142:42]
  wire [63:0] _T_145; // @[Cache.scala 142:42]
  wire [255:0] _T_151; // @[Cache.scala 149:33]
  wire  _T_152; // @[Cache.scala 149:33]
  wire  is_dirty; // @[Cache.scala 149:29]
  wire  _T_153; // @[Conditional.scala 37:30]
  wire  _T_154; // @[Cache.scala 153:43]
  wire  _T_156; // @[Conditional.scala 37:30]
  wire  _T_159; // @[Cache.scala 165:30]
  wire  _T_160; // @[Decoupled.scala 40:37]
  wire  _T_161; // @[Decoupled.scala 40:37]
  wire  _GEN_108; // @[Cache.scala 157:17]
  wire  _GEN_109; // @[Cache.scala 157:17]
  wire  _T_162; // @[Conditional.scala 37:30]
  wire  _T_164; // @[Cache.scala 174:32]
  wire  _GEN_113; // @[Cache.scala 174:49]
  wire  _GEN_114; // @[Cache.scala 174:49]
  wire  _T_168; // @[Conditional.scala 37:30]
  wire  _T_169; // @[Conditional.scala 37:30]
  wire  _T_170; // @[Decoupled.scala 40:37]
  wire  _T_171; // @[Conditional.scala 37:30]
  wire  _T_173; // @[Conditional.scala 37:30]
  wire  _GEN_124; // @[Conditional.scala 39:67]
  wire  _GEN_127; // @[Conditional.scala 39:67]
  wire  _GEN_128; // @[Conditional.scala 39:67]
  wire  _GEN_130; // @[Conditional.scala 39:67]
  wire  _GEN_131; // @[Conditional.scala 39:67]
  wire  _GEN_132; // @[Conditional.scala 39:67]
  wire  _GEN_133; // @[Conditional.scala 39:67]
  wire  _GEN_135; // @[Conditional.scala 39:67]
  wire  _GEN_136; // @[Conditional.scala 39:67]
  wire  _GEN_137; // @[Conditional.scala 39:67]
  wire  _GEN_138; // @[Conditional.scala 39:67]
  assign metaMem_tag_rmeta_addr = metaMem_tag_rmeta_addr_pipe_0;
  assign metaMem_tag_rmeta_data = metaMem_tag[metaMem_tag_rmeta_addr]; // @[Cache.scala 62:29]
  assign metaMem_tag__T_87_data = addr_reg[31:12];
  assign metaMem_tag__T_87_addr = addr_reg[11:4];
  assign metaMem_tag__T_87_mask = 1'h1;
  assign metaMem_tag__T_87_en = wen & is_alloc;
  assign dataMem_0_0__T_22_addr = dataMem_0_0__T_22_addr_pipe_0;
  assign dataMem_0_0__T_22_data = dataMem_0_0[dataMem_0_0__T_22_addr]; // @[Cache.scala 63:46]
  assign dataMem_0_0__T_98_data = wdata[7:0];
  assign dataMem_0_0__T_98_addr = addr_reg[11:4];
  assign dataMem_0_0__T_98_mask = _T_93[0];
  assign dataMem_0_0__T_98_en = _T_12 | is_alloc;
  assign dataMem_0_1__T_22_addr = dataMem_0_1__T_22_addr_pipe_0;
  assign dataMem_0_1__T_22_data = dataMem_0_1[dataMem_0_1__T_22_addr]; // @[Cache.scala 63:46]
  assign dataMem_0_1__T_98_data = wdata[15:8];
  assign dataMem_0_1__T_98_addr = addr_reg[11:4];
  assign dataMem_0_1__T_98_mask = _T_93[1];
  assign dataMem_0_1__T_98_en = _T_12 | is_alloc;
  assign dataMem_0_2__T_22_addr = dataMem_0_2__T_22_addr_pipe_0;
  assign dataMem_0_2__T_22_data = dataMem_0_2[dataMem_0_2__T_22_addr]; // @[Cache.scala 63:46]
  assign dataMem_0_2__T_98_data = wdata[23:16];
  assign dataMem_0_2__T_98_addr = addr_reg[11:4];
  assign dataMem_0_2__T_98_mask = _T_93[2];
  assign dataMem_0_2__T_98_en = _T_12 | is_alloc;
  assign dataMem_0_3__T_22_addr = dataMem_0_3__T_22_addr_pipe_0;
  assign dataMem_0_3__T_22_data = dataMem_0_3[dataMem_0_3__T_22_addr]; // @[Cache.scala 63:46]
  assign dataMem_0_3__T_98_data = wdata[31:24];
  assign dataMem_0_3__T_98_addr = addr_reg[11:4];
  assign dataMem_0_3__T_98_mask = _T_93[3];
  assign dataMem_0_3__T_98_en = _T_12 | is_alloc;
  assign dataMem_1_0__T_29_addr = dataMem_1_0__T_29_addr_pipe_0;
  assign dataMem_1_0__T_29_data = dataMem_1_0[dataMem_1_0__T_29_addr]; // @[Cache.scala 63:46]
  assign dataMem_1_0__T_109_data = wdata[39:32];
  assign dataMem_1_0__T_109_addr = addr_reg[11:4];
  assign dataMem_1_0__T_109_mask = _T_104[0];
  assign dataMem_1_0__T_109_en = _T_12 | is_alloc;
  assign dataMem_1_1__T_29_addr = dataMem_1_1__T_29_addr_pipe_0;
  assign dataMem_1_1__T_29_data = dataMem_1_1[dataMem_1_1__T_29_addr]; // @[Cache.scala 63:46]
  assign dataMem_1_1__T_109_data = wdata[47:40];
  assign dataMem_1_1__T_109_addr = addr_reg[11:4];
  assign dataMem_1_1__T_109_mask = _T_104[1];
  assign dataMem_1_1__T_109_en = _T_12 | is_alloc;
  assign dataMem_1_2__T_29_addr = dataMem_1_2__T_29_addr_pipe_0;
  assign dataMem_1_2__T_29_data = dataMem_1_2[dataMem_1_2__T_29_addr]; // @[Cache.scala 63:46]
  assign dataMem_1_2__T_109_data = wdata[55:48];
  assign dataMem_1_2__T_109_addr = addr_reg[11:4];
  assign dataMem_1_2__T_109_mask = _T_104[2];
  assign dataMem_1_2__T_109_en = _T_12 | is_alloc;
  assign dataMem_1_3__T_29_addr = dataMem_1_3__T_29_addr_pipe_0;
  assign dataMem_1_3__T_29_data = dataMem_1_3[dataMem_1_3__T_29_addr]; // @[Cache.scala 63:46]
  assign dataMem_1_3__T_109_data = wdata[63:56];
  assign dataMem_1_3__T_109_addr = addr_reg[11:4];
  assign dataMem_1_3__T_109_mask = _T_104[3];
  assign dataMem_1_3__T_109_en = _T_12 | is_alloc;
  assign dataMem_2_0__T_36_addr = dataMem_2_0__T_36_addr_pipe_0;
  assign dataMem_2_0__T_36_data = dataMem_2_0[dataMem_2_0__T_36_addr]; // @[Cache.scala 63:46]
  assign dataMem_2_0__T_120_data = wdata[71:64];
  assign dataMem_2_0__T_120_addr = addr_reg[11:4];
  assign dataMem_2_0__T_120_mask = _T_115[0];
  assign dataMem_2_0__T_120_en = _T_12 | is_alloc;
  assign dataMem_2_1__T_36_addr = dataMem_2_1__T_36_addr_pipe_0;
  assign dataMem_2_1__T_36_data = dataMem_2_1[dataMem_2_1__T_36_addr]; // @[Cache.scala 63:46]
  assign dataMem_2_1__T_120_data = wdata[79:72];
  assign dataMem_2_1__T_120_addr = addr_reg[11:4];
  assign dataMem_2_1__T_120_mask = _T_115[1];
  assign dataMem_2_1__T_120_en = _T_12 | is_alloc;
  assign dataMem_2_2__T_36_addr = dataMem_2_2__T_36_addr_pipe_0;
  assign dataMem_2_2__T_36_data = dataMem_2_2[dataMem_2_2__T_36_addr]; // @[Cache.scala 63:46]
  assign dataMem_2_2__T_120_data = wdata[87:80];
  assign dataMem_2_2__T_120_addr = addr_reg[11:4];
  assign dataMem_2_2__T_120_mask = _T_115[2];
  assign dataMem_2_2__T_120_en = _T_12 | is_alloc;
  assign dataMem_2_3__T_36_addr = dataMem_2_3__T_36_addr_pipe_0;
  assign dataMem_2_3__T_36_data = dataMem_2_3[dataMem_2_3__T_36_addr]; // @[Cache.scala 63:46]
  assign dataMem_2_3__T_120_data = wdata[95:88];
  assign dataMem_2_3__T_120_addr = addr_reg[11:4];
  assign dataMem_2_3__T_120_mask = _T_115[3];
  assign dataMem_2_3__T_120_en = _T_12 | is_alloc;
  assign dataMem_3_0__T_43_addr = dataMem_3_0__T_43_addr_pipe_0;
  assign dataMem_3_0__T_43_data = dataMem_3_0[dataMem_3_0__T_43_addr]; // @[Cache.scala 63:46]
  assign dataMem_3_0__T_131_data = wdata[103:96];
  assign dataMem_3_0__T_131_addr = addr_reg[11:4];
  assign dataMem_3_0__T_131_mask = _T_126[0];
  assign dataMem_3_0__T_131_en = _T_12 | is_alloc;
  assign dataMem_3_1__T_43_addr = dataMem_3_1__T_43_addr_pipe_0;
  assign dataMem_3_1__T_43_data = dataMem_3_1[dataMem_3_1__T_43_addr]; // @[Cache.scala 63:46]
  assign dataMem_3_1__T_131_data = wdata[111:104];
  assign dataMem_3_1__T_131_addr = addr_reg[11:4];
  assign dataMem_3_1__T_131_mask = _T_126[1];
  assign dataMem_3_1__T_131_en = _T_12 | is_alloc;
  assign dataMem_3_2__T_43_addr = dataMem_3_2__T_43_addr_pipe_0;
  assign dataMem_3_2__T_43_data = dataMem_3_2[dataMem_3_2__T_43_addr]; // @[Cache.scala 63:46]
  assign dataMem_3_2__T_131_data = wdata[119:112];
  assign dataMem_3_2__T_131_addr = addr_reg[11:4];
  assign dataMem_3_2__T_131_mask = _T_126[2];
  assign dataMem_3_2__T_131_en = _T_12 | is_alloc;
  assign dataMem_3_3__T_43_addr = dataMem_3_3__T_43_addr_pipe_0;
  assign dataMem_3_3__T_43_data = dataMem_3_3[dataMem_3_3__T_43_addr]; // @[Cache.scala 63:46]
  assign dataMem_3_3__T_131_data = wdata[127:120];
  assign dataMem_3_3__T_131_addr = addr_reg[11:4];
  assign dataMem_3_3__T_131_mask = _T_126[3];
  assign dataMem_3_3__T_131_en = _T_12 | is_alloc;
  assign _T = io_nasti_r_ready & io_nasti_r_valid; // @[Decoupled.scala 40:37]
  assign _T_3 = read_count + 1'h1; // @[Counter.scala 38:22]
  assign read_wrap_out = _T & read_count; // @[Counter.scala 72:20]
  assign _T_4 = io_nasti_w_ready & io_nasti_w_valid; // @[Decoupled.scala 40:37]
  assign _T_7 = write_count + 1'h1; // @[Counter.scala 38:22]
  assign write_wrap_out = _T_4 & write_count; // @[Counter.scala 72:20]
  assign is_idle = state == 3'h0; // @[Cache.scala 74:25]
  assign is_read = state == 3'h1; // @[Cache.scala 75:25]
  assign is_write = state == 3'h2; // @[Cache.scala 76:25]
  assign _T_8 = state == 3'h6; // @[Cache.scala 77:25]
  assign is_alloc = _T_8 & read_wrap_out; // @[Cache.scala 77:38]
  assign idx_reg = addr_reg[11:4]; // @[Cache.scala 88:26]
  assign _T_51 = v >> idx_reg; // @[Cache.scala 97:11]
  assign _T_52 = _T_51[0]; // @[Cache.scala 97:11]
  assign tag_reg = addr_reg[31:12]; // @[Cache.scala 87:26]
  assign _T_53 = metaMem_tag_rmeta_data == tag_reg; // @[Cache.scala 97:34]
  assign hit = _T_52 & _T_53; // @[Cache.scala 97:21]
  assign _T_9 = hit | is_alloc_reg; // @[Cache.scala 81:30]
  assign _T_10 = is_write & _T_9; // @[Cache.scala 81:22]
  assign _T_11 = io_cpu_abort == 1'h0; // @[Cache.scala 81:50]
  assign _T_12 = _T_10 & _T_11; // @[Cache.scala 81:47]
  assign wen = _T_12 | is_alloc; // @[Cache.scala 81:64]
  assign _T_13 = wen == 1'h0; // @[Cache.scala 82:13]
  assign _T_14 = is_idle | is_read; // @[Cache.scala 82:30]
  assign _T_15 = _T_13 & _T_14; // @[Cache.scala 82:18]
  assign off_reg = addr_reg[3:2]; // @[Cache.scala 89:26]
  assign _T_47 = {dataMem_1_3__T_29_data,dataMem_1_2__T_29_data,dataMem_1_1__T_29_data,dataMem_1_0__T_29_data,dataMem_0_3__T_22_data,dataMem_0_2__T_22_data,dataMem_0_1__T_22_data,dataMem_0_0__T_22_data}; // @[Cat.scala 29:58]
  assign rdata = {dataMem_3_3__T_43_data,dataMem_3_2__T_43_data,dataMem_3_1__T_43_data,dataMem_3_0__T_43_data,dataMem_2_3__T_36_data,dataMem_2_2__T_36_data,dataMem_2_1__T_36_data,dataMem_2_0__T_36_data,_T_47}; // @[Cat.scala 29:58]
  assign _GEN_10 = ren_reg ? rdata : rdata_buf; // @[Reg.scala 16:19]
  assign _T_49 = {refill_buf_1,refill_buf_0}; // @[Cache.scala 95:43]
  assign read = is_alloc_reg ? _T_49 : _GEN_10; // @[Cache.scala 95:17]
  assign _T_55 = read[31:0]; // @[Cache.scala 100:62]
  assign _T_56 = read[63:32]; // @[Cache.scala 100:62]
  assign _T_57 = read[95:64]; // @[Cache.scala 100:62]
  assign _T_58 = read[127:96]; // @[Cache.scala 100:62]
  assign _GEN_12 = 2'h1 == off_reg ? _T_56 : _T_55; // @[Cache.scala 100:25]
  assign _GEN_13 = 2'h2 == off_reg ? _T_57 : _GEN_12; // @[Cache.scala 100:25]
  assign _T_60 = is_read & hit; // @[Cache.scala 101:47]
  assign _T_61 = is_idle | _T_60; // @[Cache.scala 101:36]
  assign _T_62 = cpu_mask != 4'h0; // @[Cache.scala 101:83]
  assign _T_63 = _T_62 == 1'h0; // @[Cache.scala 101:73]
  assign _T_64 = is_alloc_reg & _T_63; // @[Cache.scala 101:70]
  assign _T_66 = is_alloc == 1'h0; // @[Cache.scala 112:19]
  assign _T_67 = {off_reg,2'h0}; // @[Cat.scala 29:58]
  assign _GEN_144 = {{15'd0}, cpu_mask}; // @[Cache.scala 112:40]
  assign _T_68 = _GEN_144 << _T_67; // @[Cache.scala 112:40]
  assign _T_69 = {1'b0,$signed(_T_68)}; // @[Cache.scala 112:80]
  assign wmask = _T_66 ? $signed(_T_69) : $signed(-20'sh1); // @[Cache.scala 112:18]
  assign _T_72 = {cpu_data,cpu_data,cpu_data,cpu_data}; // @[Cat.scala 29:58]
  assign _T_73 = {io_nasti_r_bits_data,refill_buf_0}; // @[Cat.scala 29:58]
  assign wdata = _T_66 ? _T_72 : _T_73; // @[Cache.scala 113:18]
  assign _T_74 = 256'h1 << idx_reg; // @[Cache.scala 117:18]
  assign _T_75 = v | _T_74; // @[Cache.scala 117:18]
  assign _T_82 = d | _T_74; // @[Cache.scala 118:18]
  assign _T_83 = ~ d; // @[Cache.scala 118:18]
  assign _T_84 = _T_83 | _T_74; // @[Cache.scala 118:18]
  assign _T_85 = ~ _T_84; // @[Cache.scala 118:18]
  assign _T_93 = wmask[3:0]; // @[Cache.scala 124:37]
  assign _T_104 = wmask[7:4]; // @[Cache.scala 124:37]
  assign _T_115 = wmask[11:8]; // @[Cache.scala 124:37]
  assign _T_126 = wmask[15:12]; // @[Cache.scala 124:37]
  assign _T_132 = {tag_reg,idx_reg}; // @[Cat.scala 29:58]
  assign _GEN_145 = {_T_132, 4'h0}; // @[Cache.scala 130:33]
  assign _T_133 = {{3'd0}, _GEN_145}; // @[Cache.scala 130:33]
  assign _T_139 = {metaMem_tag_rmeta_data,idx_reg}; // @[Cat.scala 29:58]
  assign _GEN_146 = {_T_139, 4'h0}; // @[Cache.scala 138:35]
  assign _T_140 = {{3'd0}, _GEN_146}; // @[Cache.scala 138:35]
  assign _T_144 = read[63:0]; // @[Cache.scala 142:42]
  assign _T_145 = read[127:64]; // @[Cache.scala 142:42]
  assign _T_151 = d >> idx_reg; // @[Cache.scala 149:33]
  assign _T_152 = _T_151[0]; // @[Cache.scala 149:33]
  assign is_dirty = _T_52 & _T_152; // @[Cache.scala 149:29]
  assign _T_153 = 3'h0 == state; // @[Conditional.scala 37:30]
  assign _T_154 = io_cpu_req_bits_mask != 4'h0; // @[Cache.scala 153:43]
  assign _T_156 = 3'h1 == state; // @[Conditional.scala 37:30]
  assign _T_159 = is_dirty == 1'h0; // @[Cache.scala 165:30]
  assign _T_160 = io_nasti_aw_ready & io_nasti_aw_valid; // @[Decoupled.scala 40:37]
  assign _T_161 = io_nasti_ar_ready & io_nasti_ar_valid; // @[Decoupled.scala 40:37]
  assign _GEN_108 = hit ? 1'h0 : is_dirty; // @[Cache.scala 157:17]
  assign _GEN_109 = hit ? 1'h0 : _T_159; // @[Cache.scala 157:17]
  assign _T_162 = 3'h2 == state; // @[Conditional.scala 37:30]
  assign _T_164 = _T_9 | io_cpu_abort; // @[Cache.scala 174:32]
  assign _GEN_113 = _T_164 ? 1'h0 : is_dirty; // @[Cache.scala 174:49]
  assign _GEN_114 = _T_164 ? 1'h0 : _T_159; // @[Cache.scala 174:49]
  assign _T_168 = 3'h3 == state; // @[Conditional.scala 37:30]
  assign _T_169 = 3'h4 == state; // @[Conditional.scala 37:30]
  assign _T_170 = io_nasti_b_ready & io_nasti_b_valid; // @[Decoupled.scala 40:37]
  assign _T_171 = 3'h5 == state; // @[Conditional.scala 37:30]
  assign _T_173 = 3'h6 == state; // @[Conditional.scala 37:30]
  assign _GEN_124 = _T_169 ? 1'h0 : _T_171; // @[Conditional.scala 39:67]
  assign _GEN_127 = _T_168 ? 1'h0 : _T_169; // @[Conditional.scala 39:67]
  assign _GEN_128 = _T_168 ? 1'h0 : _GEN_124; // @[Conditional.scala 39:67]
  assign _GEN_130 = _T_162 & _GEN_113; // @[Conditional.scala 39:67]
  assign _GEN_131 = _T_162 ? _GEN_114 : _GEN_128; // @[Conditional.scala 39:67]
  assign _GEN_132 = _T_162 ? 1'h0 : _T_168; // @[Conditional.scala 39:67]
  assign _GEN_133 = _T_162 ? 1'h0 : _GEN_127; // @[Conditional.scala 39:67]
  assign _GEN_135 = _T_156 ? _GEN_108 : _GEN_130; // @[Conditional.scala 39:67]
  assign _GEN_136 = _T_156 ? _GEN_109 : _GEN_131; // @[Conditional.scala 39:67]
  assign _GEN_137 = _T_156 ? 1'h0 : _GEN_132; // @[Conditional.scala 39:67]
  assign _GEN_138 = _T_156 ? 1'h0 : _GEN_133; // @[Conditional.scala 39:67]
  assign io_cpu_resp_valid = _T_61 | _T_64; // @[Cache.scala 101:25]
  assign io_cpu_resp_bits_data = 2'h3 == off_reg ? _T_58 : _GEN_13; // @[Cache.scala 100:25]
  assign io_nasti_aw_valid = _T_153 ? 1'h0 : _GEN_135; // @[Cache.scala 139:21 Cache.scala 164:27 Cache.scala 177:27]
  assign io_nasti_aw_bits_addr = _T_140[31:0]; // @[Cache.scala 137:20]
  assign io_nasti_w_valid = _T_153 ? 1'h0 : _GEN_137; // @[Cache.scala 144:20 Cache.scala 187:24]
  assign io_nasti_w_bits_data = write_count ? _T_145 : _T_144; // @[Cache.scala 141:19]
  assign io_nasti_w_bits_last = _T_4 & write_count; // @[Cache.scala 141:19]
  assign io_nasti_b_ready = _T_153 ? 1'h0 : _GEN_138; // @[Cache.scala 146:20 Cache.scala 193:24]
  assign io_nasti_ar_valid = _T_153 ? 1'h0 : _GEN_136; // @[Cache.scala 131:21 Cache.scala 165:27 Cache.scala 178:27 Cache.scala 199:25]
  assign io_nasti_ar_bits_addr = _T_133[31:0]; // @[Cache.scala 129:20]
  assign io_nasti_r_ready = state == 3'h6; // @[Cache.scala 133:20]
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
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    metaMem_tag[initvar] = _RAND_0[19:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  metaMem_tag_rmeta_en_pipe_0 = _RAND_1[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  metaMem_tag_rmeta_addr_pipe_0 = _RAND_2[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_3 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_0_0[initvar] = _RAND_3[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {1{`RANDOM}};
  dataMem_0_0__T_22_en_pipe_0 = _RAND_4[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  dataMem_0_0__T_22_addr_pipe_0 = _RAND_5[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_6 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_0_1[initvar] = _RAND_6[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_7 = {1{`RANDOM}};
  dataMem_0_1__T_22_en_pipe_0 = _RAND_7[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_8 = {1{`RANDOM}};
  dataMem_0_1__T_22_addr_pipe_0 = _RAND_8[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_9 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_0_2[initvar] = _RAND_9[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_10 = {1{`RANDOM}};
  dataMem_0_2__T_22_en_pipe_0 = _RAND_10[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_11 = {1{`RANDOM}};
  dataMem_0_2__T_22_addr_pipe_0 = _RAND_11[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_12 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_0_3[initvar] = _RAND_12[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_13 = {1{`RANDOM}};
  dataMem_0_3__T_22_en_pipe_0 = _RAND_13[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_14 = {1{`RANDOM}};
  dataMem_0_3__T_22_addr_pipe_0 = _RAND_14[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_15 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_1_0[initvar] = _RAND_15[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_16 = {1{`RANDOM}};
  dataMem_1_0__T_29_en_pipe_0 = _RAND_16[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_17 = {1{`RANDOM}};
  dataMem_1_0__T_29_addr_pipe_0 = _RAND_17[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_18 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_1_1[initvar] = _RAND_18[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_19 = {1{`RANDOM}};
  dataMem_1_1__T_29_en_pipe_0 = _RAND_19[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_20 = {1{`RANDOM}};
  dataMem_1_1__T_29_addr_pipe_0 = _RAND_20[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_21 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_1_2[initvar] = _RAND_21[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_22 = {1{`RANDOM}};
  dataMem_1_2__T_29_en_pipe_0 = _RAND_22[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_23 = {1{`RANDOM}};
  dataMem_1_2__T_29_addr_pipe_0 = _RAND_23[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_24 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_1_3[initvar] = _RAND_24[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_25 = {1{`RANDOM}};
  dataMem_1_3__T_29_en_pipe_0 = _RAND_25[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_26 = {1{`RANDOM}};
  dataMem_1_3__T_29_addr_pipe_0 = _RAND_26[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_27 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_2_0[initvar] = _RAND_27[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_28 = {1{`RANDOM}};
  dataMem_2_0__T_36_en_pipe_0 = _RAND_28[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_29 = {1{`RANDOM}};
  dataMem_2_0__T_36_addr_pipe_0 = _RAND_29[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_30 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_2_1[initvar] = _RAND_30[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_31 = {1{`RANDOM}};
  dataMem_2_1__T_36_en_pipe_0 = _RAND_31[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_32 = {1{`RANDOM}};
  dataMem_2_1__T_36_addr_pipe_0 = _RAND_32[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_33 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_2_2[initvar] = _RAND_33[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_34 = {1{`RANDOM}};
  dataMem_2_2__T_36_en_pipe_0 = _RAND_34[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_35 = {1{`RANDOM}};
  dataMem_2_2__T_36_addr_pipe_0 = _RAND_35[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_36 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_2_3[initvar] = _RAND_36[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_37 = {1{`RANDOM}};
  dataMem_2_3__T_36_en_pipe_0 = _RAND_37[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_38 = {1{`RANDOM}};
  dataMem_2_3__T_36_addr_pipe_0 = _RAND_38[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_39 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_3_0[initvar] = _RAND_39[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_40 = {1{`RANDOM}};
  dataMem_3_0__T_43_en_pipe_0 = _RAND_40[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_41 = {1{`RANDOM}};
  dataMem_3_0__T_43_addr_pipe_0 = _RAND_41[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_42 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_3_1[initvar] = _RAND_42[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_43 = {1{`RANDOM}};
  dataMem_3_1__T_43_en_pipe_0 = _RAND_43[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_44 = {1{`RANDOM}};
  dataMem_3_1__T_43_addr_pipe_0 = _RAND_44[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_45 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_3_2[initvar] = _RAND_45[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_46 = {1{`RANDOM}};
  dataMem_3_2__T_43_en_pipe_0 = _RAND_46[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_47 = {1{`RANDOM}};
  dataMem_3_2__T_43_addr_pipe_0 = _RAND_47[7:0];
  `endif // RANDOMIZE_REG_INIT
  _RAND_48 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 256; initvar = initvar+1)
    dataMem_3_3[initvar] = _RAND_48[7:0];
  `endif // RANDOMIZE_MEM_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_49 = {1{`RANDOM}};
  dataMem_3_3__T_43_en_pipe_0 = _RAND_49[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_50 = {1{`RANDOM}};
  dataMem_3_3__T_43_addr_pipe_0 = _RAND_50[7:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_51 = {1{`RANDOM}};
  state = _RAND_51[2:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_52 = {8{`RANDOM}};
  v = _RAND_52[255:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_53 = {8{`RANDOM}};
  d = _RAND_53[255:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_54 = {1{`RANDOM}};
  addr_reg = _RAND_54[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_55 = {1{`RANDOM}};
  cpu_data = _RAND_55[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_56 = {1{`RANDOM}};
  cpu_mask = _RAND_56[3:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_57 = {1{`RANDOM}};
  read_count = _RAND_57[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_58 = {1{`RANDOM}};
  write_count = _RAND_58[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_59 = {1{`RANDOM}};
  is_alloc_reg = _RAND_59[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_60 = {1{`RANDOM}};
  ren_reg = _RAND_60[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_61 = {4{`RANDOM}};
  rdata_buf = _RAND_61[127:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_62 = {2{`RANDOM}};
  refill_buf_0 = _RAND_62[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_63 = {2{`RANDOM}};
  refill_buf_1 = _RAND_63[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if(metaMem_tag__T_87_en & metaMem_tag__T_87_mask) begin
      metaMem_tag[metaMem_tag__T_87_addr] <= metaMem_tag__T_87_data; // @[Cache.scala 62:29]
    end
    metaMem_tag_rmeta_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      metaMem_tag_rmeta_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_0_0__T_98_en & dataMem_0_0__T_98_mask) begin
      dataMem_0_0[dataMem_0_0__T_98_addr] <= dataMem_0_0__T_98_data; // @[Cache.scala 63:46]
    end
    dataMem_0_0__T_22_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_0_0__T_22_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_0_1__T_98_en & dataMem_0_1__T_98_mask) begin
      dataMem_0_1[dataMem_0_1__T_98_addr] <= dataMem_0_1__T_98_data; // @[Cache.scala 63:46]
    end
    dataMem_0_1__T_22_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_0_1__T_22_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_0_2__T_98_en & dataMem_0_2__T_98_mask) begin
      dataMem_0_2[dataMem_0_2__T_98_addr] <= dataMem_0_2__T_98_data; // @[Cache.scala 63:46]
    end
    dataMem_0_2__T_22_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_0_2__T_22_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_0_3__T_98_en & dataMem_0_3__T_98_mask) begin
      dataMem_0_3[dataMem_0_3__T_98_addr] <= dataMem_0_3__T_98_data; // @[Cache.scala 63:46]
    end
    dataMem_0_3__T_22_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_0_3__T_22_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_1_0__T_109_en & dataMem_1_0__T_109_mask) begin
      dataMem_1_0[dataMem_1_0__T_109_addr] <= dataMem_1_0__T_109_data; // @[Cache.scala 63:46]
    end
    dataMem_1_0__T_29_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_1_0__T_29_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_1_1__T_109_en & dataMem_1_1__T_109_mask) begin
      dataMem_1_1[dataMem_1_1__T_109_addr] <= dataMem_1_1__T_109_data; // @[Cache.scala 63:46]
    end
    dataMem_1_1__T_29_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_1_1__T_29_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_1_2__T_109_en & dataMem_1_2__T_109_mask) begin
      dataMem_1_2[dataMem_1_2__T_109_addr] <= dataMem_1_2__T_109_data; // @[Cache.scala 63:46]
    end
    dataMem_1_2__T_29_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_1_2__T_29_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_1_3__T_109_en & dataMem_1_3__T_109_mask) begin
      dataMem_1_3[dataMem_1_3__T_109_addr] <= dataMem_1_3__T_109_data; // @[Cache.scala 63:46]
    end
    dataMem_1_3__T_29_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_1_3__T_29_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_2_0__T_120_en & dataMem_2_0__T_120_mask) begin
      dataMem_2_0[dataMem_2_0__T_120_addr] <= dataMem_2_0__T_120_data; // @[Cache.scala 63:46]
    end
    dataMem_2_0__T_36_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_2_0__T_36_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_2_1__T_120_en & dataMem_2_1__T_120_mask) begin
      dataMem_2_1[dataMem_2_1__T_120_addr] <= dataMem_2_1__T_120_data; // @[Cache.scala 63:46]
    end
    dataMem_2_1__T_36_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_2_1__T_36_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_2_2__T_120_en & dataMem_2_2__T_120_mask) begin
      dataMem_2_2[dataMem_2_2__T_120_addr] <= dataMem_2_2__T_120_data; // @[Cache.scala 63:46]
    end
    dataMem_2_2__T_36_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_2_2__T_36_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_2_3__T_120_en & dataMem_2_3__T_120_mask) begin
      dataMem_2_3[dataMem_2_3__T_120_addr] <= dataMem_2_3__T_120_data; // @[Cache.scala 63:46]
    end
    dataMem_2_3__T_36_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_2_3__T_36_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_3_0__T_131_en & dataMem_3_0__T_131_mask) begin
      dataMem_3_0[dataMem_3_0__T_131_addr] <= dataMem_3_0__T_131_data; // @[Cache.scala 63:46]
    end
    dataMem_3_0__T_43_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_3_0__T_43_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_3_1__T_131_en & dataMem_3_1__T_131_mask) begin
      dataMem_3_1[dataMem_3_1__T_131_addr] <= dataMem_3_1__T_131_data; // @[Cache.scala 63:46]
    end
    dataMem_3_1__T_43_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_3_1__T_43_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_3_2__T_131_en & dataMem_3_2__T_131_mask) begin
      dataMem_3_2[dataMem_3_2__T_131_addr] <= dataMem_3_2__T_131_data; // @[Cache.scala 63:46]
    end
    dataMem_3_2__T_43_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_3_2__T_43_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if(dataMem_3_3__T_131_en & dataMem_3_3__T_131_mask) begin
      dataMem_3_3[dataMem_3_3__T_131_addr] <= dataMem_3_3__T_131_data; // @[Cache.scala 63:46]
    end
    dataMem_3_3__T_43_en_pipe_0 <= _T_15 & io_cpu_req_valid;
    if (_T_15 & io_cpu_req_valid) begin
      dataMem_3_3__T_43_addr_pipe_0 <= io_cpu_req_bits_addr[11:4];
    end
    if (reset) begin
      state <= 3'h0;
    end else if (_T_153) begin
      if (io_cpu_req_valid) begin
        if (_T_154) begin
          state <= 3'h2;
        end else begin
          state <= 3'h1;
        end
      end
    end else if (_T_156) begin
      if (hit) begin
        if (io_cpu_req_valid) begin
          if (_T_154) begin
            state <= 3'h2;
          end else begin
            state <= 3'h1;
          end
        end else begin
          state <= 3'h0;
        end
      end else if (_T_160) begin
        state <= 3'h3;
      end else if (_T_161) begin
        state <= 3'h6;
      end
    end else if (_T_162) begin
      if (_T_164) begin
        state <= 3'h0;
      end else if (_T_160) begin
        state <= 3'h3;
      end else if (_T_161) begin
        state <= 3'h6;
      end
    end else if (_T_168) begin
      if (write_wrap_out) begin
        state <= 3'h4;
      end
    end else if (_T_169) begin
      if (_T_170) begin
        state <= 3'h5;
      end
    end else if (_T_171) begin
      if (_T_161) begin
        state <= 3'h6;
      end
    end else if (_T_173) begin
      if (read_wrap_out) begin
        if (_T_62) begin
          state <= 3'h2;
        end else begin
          state <= 3'h0;
        end
      end
    end
    if (reset) begin
      v <= 256'h0;
    end else if (wen) begin
      v <= _T_75;
    end
    if (reset) begin
      d <= 256'h0;
    end else if (wen) begin
      if (_T_66) begin
        d <= _T_82;
      end else begin
        d <= _T_85;
      end
    end
    if (io_cpu_resp_valid) begin
      addr_reg <= io_cpu_req_bits_addr;
    end
    if (io_cpu_resp_valid) begin
      cpu_data <= io_cpu_req_bits_data;
    end
    if (io_cpu_resp_valid) begin
      cpu_mask <= io_cpu_req_bits_mask;
    end
    if (reset) begin
      read_count <= 1'h0;
    end else if (_T) begin
      read_count <= _T_3;
    end
    if (reset) begin
      write_count <= 1'h0;
    end else if (_T_4) begin
      write_count <= _T_7;
    end
    is_alloc_reg <= _T_8 & read_wrap_out;
    ren_reg <= _T_15 & io_cpu_req_valid;
    if (ren_reg) begin
      rdata_buf <= rdata;
    end
    if (_T) begin
      if (1'h0 == read_count) begin
        refill_buf_0 <= io_nasti_r_bits_data;
      end
    end
    if (_T) begin
      if (read_count) begin
        refill_buf_1 <= io_nasti_r_bits_data;
      end
    end
  end
endmodule
