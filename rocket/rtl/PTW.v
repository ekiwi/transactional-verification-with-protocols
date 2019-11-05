module PTW( // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145049.2]
  input         clock, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145050.4]
  input         reset, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145051.4]
  output        io_requestor_0_req_ready, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_requestor_0_req_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [19:0] io_requestor_0_req_bits_bits_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_ae, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [53:0] io_requestor_0_resp_bits_pte_ppn, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_d, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_g, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_u, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_pte_v, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_level, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_resp_bits_homogeneous, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_ptbr_mode, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_status_debug, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_status_dprv, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_status_mxr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_status_sum, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_0_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_0_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_0_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_0_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_0_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_0_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_0_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_1_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_1_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_1_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_1_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_1_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_1_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_1_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_2_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_2_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_2_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_2_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_2_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_2_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_2_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_3_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_3_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_3_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_3_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_3_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_3_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_3_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_4_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_4_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_4_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_4_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_4_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_4_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_4_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_5_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_5_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_5_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_5_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_5_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_5_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_5_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_6_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_6_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_6_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_6_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_6_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_6_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_6_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_7_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_0_pmp_7_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_7_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_7_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_0_pmp_7_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_0_pmp_7_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_0_pmp_7_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_req_ready, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_requestor_1_req_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_requestor_1_req_bits_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [19:0] io_requestor_1_req_bits_bits_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_ae, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [53:0] io_requestor_1_resp_bits_pte_ppn, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_d, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_g, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_u, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_pte_v, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_level, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_resp_bits_homogeneous, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_ptbr_mode, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_status_debug, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_status_prv, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_0_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_0_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_0_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_0_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_0_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_0_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_0_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_1_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_1_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_1_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_1_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_1_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_1_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_1_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_2_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_2_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_2_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_2_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_2_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_2_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_2_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_3_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_3_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_3_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_3_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_3_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_3_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_3_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_4_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_4_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_4_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_4_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_4_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_4_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_4_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_5_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_5_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_5_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_5_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_5_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_5_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_5_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_6_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_6_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_6_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_6_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_6_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_6_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_6_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_7_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [1:0]  io_requestor_1_pmp_7_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_7_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_7_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_requestor_1_pmp_7_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [29:0] io_requestor_1_pmp_7_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_requestor_1_pmp_7_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_mem_req_ready, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_mem_req_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output [31:0] io_mem_req_bits_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  output        io_mem_s1_kill, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_mem_s2_nack, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_mem_resp_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_mem_resp_bits_data, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_mem_s2_xcpt_ae_ld, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_ptbr_mode, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [21:0] io_dpath_ptbr_ppn, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_sfence_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_sfence_bits_rs1, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_status_debug, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_status_dprv, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_status_prv, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_status_mxr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_status_sum, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_0_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_0_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_0_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_0_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_0_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_0_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_0_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_1_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_1_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_1_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_1_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_1_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_1_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_1_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_2_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_2_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_2_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_2_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_2_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_2_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_2_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_3_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_3_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_3_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_3_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_3_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_3_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_3_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_4_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_4_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_4_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_4_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_4_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_4_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_4_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_5_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_5_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_5_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_5_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_5_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_5_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_5_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_6_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_6_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_6_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_6_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_6_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_6_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_6_mask, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_7_cfg_l, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [1:0]  io_dpath_pmp_7_cfg_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_7_cfg_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_7_cfg_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input         io_dpath_pmp_7_cfg_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [29:0] io_dpath_pmp_7_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
  input  [31:0] io_dpath_pmp_7_mask // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145052.4]
);
  wire  arb_clock; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_in_0_ready; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_in_0_valid; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire [19:0] arb_io_in_0_bits_bits_addr; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_in_1_ready; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_in_1_valid; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_in_1_bits_valid; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire [19:0] arb_io_in_1_bits_bits_addr; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_out_ready; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_out_valid; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_out_bits_valid; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire [19:0] arb_io_out_bits_bits_addr; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire  arb_io_chosen; // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
  wire [2:0] _2_io_x; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@145944.4]
  wire [2:0] _2_io_y; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@145944.4]
  wire [53:0] _2_1_io_x_ppn; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_d; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_a; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_g; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_u; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_x; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_w; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_r; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_x_v; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire [53:0] _2_1_io_y_ppn; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_d; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_a; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_g; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_u; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_x; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_w; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_r; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  wire  _2_1_io_y_v; // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
  reg [2:0] state; // @[PTW.scala 86:18:freechips.rocketchip.system.DefaultRV32Config.fir@145057.4]
  reg [31:0] _RAND_0;
  reg  resp_valid_0; // @[PTW.scala 92:23:freechips.rocketchip.system.DefaultRV32Config.fir@145070.4]
  reg [31:0] _RAND_1;
  reg  resp_valid_1; // @[PTW.scala 92:23:freechips.rocketchip.system.DefaultRV32Config.fir@145070.4]
  reg [31:0] _RAND_2;
  wire  _T_2; // @[PTW.scala 94:24:freechips.rocketchip.system.DefaultRV32Config.fir@145072.4]
  reg  invalidated; // @[PTW.scala 101:24:freechips.rocketchip.system.DefaultRV32Config.fir@145079.4]
  reg [31:0] _RAND_3;
  reg  count; // @[PTW.scala 102:18:freechips.rocketchip.system.DefaultRV32Config.fir@145080.4]
  reg [31:0] _RAND_4;
  reg  resp_ae; // @[PTW.scala 103:24:freechips.rocketchip.system.DefaultRV32Config.fir@145081.4]
  reg [31:0] _RAND_5;
  reg [19:0] r_req_addr; // @[PTW.scala 106:18:freechips.rocketchip.system.DefaultRV32Config.fir@145085.4]
  reg [31:0] _RAND_6;
  reg  r_req_dest; // @[PTW.scala 107:23:freechips.rocketchip.system.DefaultRV32Config.fir@145086.4]
  reg [31:0] _RAND_7;
  reg [53:0] r_pte_ppn; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [63:0] _RAND_8;
  reg  r_pte_d; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_9;
  reg  r_pte_a; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_10;
  reg  r_pte_g; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_11;
  reg  r_pte_u; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_12;
  reg  r_pte_x; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_13;
  reg  r_pte_w; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_14;
  reg  r_pte_r; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_15;
  reg  r_pte_v; // @[PTW.scala 108:18:freechips.rocketchip.system.DefaultRV32Config.fir@145087.4]
  reg [31:0] _RAND_16;
  reg  mem_resp_valid; // @[PTW.scala 110:31:freechips.rocketchip.system.DefaultRV32Config.fir@145088.4]
  reg [31:0] _RAND_17;
  reg [31:0] mem_resp_data; // @[PTW.scala 111:30:freechips.rocketchip.system.DefaultRV32Config.fir@145090.4]
  reg [31:0] _RAND_18;
  wire [63:0] _T_7; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145094.4 :freechips.rocketchip.system.DefaultRV32Config.fir@145096.4]
  wire  tmp_v; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145097.4]
  wire  tmp_r; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145099.4]
  wire  tmp_w; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145101.4]
  wire  tmp_x; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145103.4]
  wire  tmp_u; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145105.4]
  wire  tmp_g; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145107.4]
  wire  tmp_a; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145109.4]
  wire  tmp_d; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145111.4]
  wire [53:0] tmp_ppn; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145115.4]
  wire [19:0] _T_18; // @[PTW.scala 124:23:freechips.rocketchip.system.DefaultRV32Config.fir@145120.4]
  wire  _T_19; // @[PTW.scala 125:17:freechips.rocketchip.system.DefaultRV32Config.fir@145122.4]
  wire  _T_20; // @[PTW.scala 125:26:freechips.rocketchip.system.DefaultRV32Config.fir@145123.4]
  wire  _T_21; // @[PTW.scala 128:21:freechips.rocketchip.system.DefaultRV32Config.fir@145125.6]
  wire [9:0] _T_22; // @[PTW.scala 128:36:freechips.rocketchip.system.DefaultRV32Config.fir@145126.6]
  wire  _T_23; // @[PTW.scala 128:95:freechips.rocketchip.system.DefaultRV32Config.fir@145127.6]
  wire  _T_24; // @[PTW.scala 128:26:freechips.rocketchip.system.DefaultRV32Config.fir@145128.6]
  wire  _GEN_0; // @[PTW.scala 128:102:freechips.rocketchip.system.DefaultRV32Config.fir@145129.6]
  wire  res_v; // @[PTW.scala 125:36:freechips.rocketchip.system.DefaultRV32Config.fir@145124.4]
  wire [33:0] _T_25; // @[PTW.scala 130:20:freechips.rocketchip.system.DefaultRV32Config.fir@145133.4]
  wire  invalid_paddr; // @[PTW.scala 130:32:freechips.rocketchip.system.DefaultRV32Config.fir@145134.4]
  wire  _T_26; // @[PTW.scala 67:36:freechips.rocketchip.system.DefaultRV32Config.fir@145135.4]
  wire  _T_27; // @[PTW.scala 67:33:freechips.rocketchip.system.DefaultRV32Config.fir@145136.4]
  wire  _T_28; // @[PTW.scala 67:42:freechips.rocketchip.system.DefaultRV32Config.fir@145137.4]
  wire  _T_29; // @[PTW.scala 67:39:freechips.rocketchip.system.DefaultRV32Config.fir@145138.4]
  wire  _T_30; // @[PTW.scala 67:48:freechips.rocketchip.system.DefaultRV32Config.fir@145139.4]
  wire  _T_31; // @[PTW.scala 67:45:freechips.rocketchip.system.DefaultRV32Config.fir@145140.4]
  wire  _T_32; // @[PTW.scala 132:33:freechips.rocketchip.system.DefaultRV32Config.fir@145141.4]
  wire  _T_33; // @[PTW.scala 132:30:freechips.rocketchip.system.DefaultRV32Config.fir@145142.4]
  wire  _T_34; // @[PTW.scala 132:57:freechips.rocketchip.system.DefaultRV32Config.fir@145143.4]
  wire  traverse; // @[PTW.scala 132:48:freechips.rocketchip.system.DefaultRV32Config.fir@145144.4]
  wire [9:0] vpn_idxs_0; // @[PTW.scala 134:60:freechips.rocketchip.system.DefaultRV32Config.fir@145145.4]
  wire [9:0] vpn_idxs_1; // @[PTW.scala 134:90:freechips.rocketchip.system.DefaultRV32Config.fir@145148.4]
  wire [9:0] vpn_idx; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145150.4]
  wire [63:0] _T_38; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145151.4]
  wire [65:0] pte_addr; // @[PTW.scala 136:29:freechips.rocketchip.system.DefaultRV32Config.fir@145152.4]
  wire [43:0] _T_39; // @[PTW.scala 139:69:freechips.rocketchip.system.DefaultRV32Config.fir@145153.4]
  wire [53:0] choices_0; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145155.4]
  wire  _T_41; // @[Decoupled.scala 40:37:freechips.rocketchip.system.DefaultRV32Config.fir@145156.4]
  reg [2:0] _T_42; // @[Replacement.scala 41:30:freechips.rocketchip.system.DefaultRV32Config.fir@145161.4]
  reg [31:0] _RAND_19;
  reg [3:0] valid; // @[PTW.scala 151:24:freechips.rocketchip.system.DefaultRV32Config.fir@145162.4]
  reg [31:0] _RAND_20;
  reg [31:0] tags_0; // @[PTW.scala 152:19:freechips.rocketchip.system.DefaultRV32Config.fir@145163.4]
  reg [31:0] _RAND_21;
  reg [31:0] tags_1; // @[PTW.scala 152:19:freechips.rocketchip.system.DefaultRV32Config.fir@145163.4]
  reg [31:0] _RAND_22;
  reg [31:0] tags_2; // @[PTW.scala 152:19:freechips.rocketchip.system.DefaultRV32Config.fir@145163.4]
  reg [31:0] _RAND_23;
  reg [31:0] tags_3; // @[PTW.scala 152:19:freechips.rocketchip.system.DefaultRV32Config.fir@145163.4]
  reg [31:0] _RAND_24;
  reg [19:0] data_0; // @[PTW.scala 153:19:freechips.rocketchip.system.DefaultRV32Config.fir@145164.4]
  reg [31:0] _RAND_25;
  reg [19:0] data_1; // @[PTW.scala 153:19:freechips.rocketchip.system.DefaultRV32Config.fir@145164.4]
  reg [31:0] _RAND_26;
  reg [19:0] data_2; // @[PTW.scala 153:19:freechips.rocketchip.system.DefaultRV32Config.fir@145164.4]
  reg [31:0] _RAND_27;
  reg [19:0] data_3; // @[PTW.scala 153:19:freechips.rocketchip.system.DefaultRV32Config.fir@145164.4]
  reg [31:0] _RAND_28;
  wire [65:0] _GEN_91; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145165.4]
  wire  _T_43; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145165.4]
  wire [65:0] _GEN_92; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145166.4]
  wire  _T_44; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145166.4]
  wire [65:0] _GEN_93; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145167.4]
  wire  _T_45; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145167.4]
  wire [65:0] _GEN_94; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145168.4]
  wire  _T_46; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145168.4]
  wire [3:0] _T_49; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145171.4]
  wire [3:0] hits; // @[PTW.scala 155:48:freechips.rocketchip.system.DefaultRV32Config.fir@145172.4]
  wire  hit; // @[PTW.scala 156:20:freechips.rocketchip.system.DefaultRV32Config.fir@145173.4]
  wire  _T_50; // @[PTW.scala 157:26:freechips.rocketchip.system.DefaultRV32Config.fir@145174.4]
  wire  _T_51; // @[PTW.scala 157:41:freechips.rocketchip.system.DefaultRV32Config.fir@145175.4]
  wire  _T_52; // @[PTW.scala 157:38:freechips.rocketchip.system.DefaultRV32Config.fir@145176.4]
  wire  _T_53; // @[PTW.scala 157:49:freechips.rocketchip.system.DefaultRV32Config.fir@145177.4]
  wire  _T_54; // @[PTW.scala 157:46:freechips.rocketchip.system.DefaultRV32Config.fir@145178.4]
  wire  _T_55; // @[PTW.scala 158:25:freechips.rocketchip.system.DefaultRV32Config.fir@145180.6]
  wire [3:0] _T_56; // @[Replacement.scala 57:31:freechips.rocketchip.system.DefaultRV32Config.fir@145181.6]
  wire [2:0] _GEN_95; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145185.6]
  wire [3:0] _T_60; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145185.6]
  wire  _T_61; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145186.6]
  wire [1:0] _T_63; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145188.6]
  wire [3:0] _T_67; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145192.6]
  wire  _T_68; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145193.6]
  wire [2:0] _T_70; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145195.6]
  wire [1:0] _T_71; // @[Replacement.scala 63:8:freechips.rocketchip.system.DefaultRV32Config.fir@145196.6]
  wire [3:0] _T_72; // @[PTW.scala 158:61:freechips.rocketchip.system.DefaultRV32Config.fir@145197.6]
  wire  _T_73; // @[OneHot.scala 47:40:freechips.rocketchip.system.DefaultRV32Config.fir@145198.6]
  wire  _T_74; // @[OneHot.scala 47:40:freechips.rocketchip.system.DefaultRV32Config.fir@145199.6]
  wire  _T_75; // @[OneHot.scala 47:40:freechips.rocketchip.system.DefaultRV32Config.fir@145200.6]
  wire [1:0] _T_77; // @[Mux.scala 47:69:freechips.rocketchip.system.DefaultRV32Config.fir@145202.6]
  wire [1:0] _T_78; // @[Mux.scala 47:69:freechips.rocketchip.system.DefaultRV32Config.fir@145203.6]
  wire [1:0] _T_79; // @[Mux.scala 47:69:freechips.rocketchip.system.DefaultRV32Config.fir@145204.6]
  wire [1:0] r; // @[PTW.scala 158:18:freechips.rocketchip.system.DefaultRV32Config.fir@145205.6]
  wire [3:0] _T_80; // @[OneHot.scala 58:35:freechips.rocketchip.system.DefaultRV32Config.fir@145206.6]
  wire [3:0] _T_81; // @[PTW.scala 159:22:freechips.rocketchip.system.DefaultRV32Config.fir@145207.6]
  wire [31:0] _tags_r; // @[PTW.scala 160:15:freechips.rocketchip.system.DefaultRV32Config.fir@145209.6 PTW.scala 160:15:freechips.rocketchip.system.DefaultRV32Config.fir@145209.6]
  wire [53:0] res_ppn; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145117.4 :freechips.rocketchip.system.DefaultRV32Config.fir@145119.4 PTW.scala 124:13:freechips.rocketchip.system.DefaultRV32Config.fir@145121.4]
  wire [19:0] _data_r; // @[PTW.scala 161:15:freechips.rocketchip.system.DefaultRV32Config.fir@145210.6 PTW.scala 161:15:freechips.rocketchip.system.DefaultRV32Config.fir@145210.6]
  wire  _T_82; // @[PTW.scala 163:24:freechips.rocketchip.system.DefaultRV32Config.fir@145212.4]
  wire  _T_83; // @[PTW.scala 163:15:freechips.rocketchip.system.DefaultRV32Config.fir@145213.4]
  wire [1:0] _T_84; // @[OneHot.scala 30:18:freechips.rocketchip.system.DefaultRV32Config.fir@145215.6]
  wire [1:0] _T_85; // @[OneHot.scala 31:18:freechips.rocketchip.system.DefaultRV32Config.fir@145216.6]
  wire  _T_86; // @[OneHot.scala 32:14:freechips.rocketchip.system.DefaultRV32Config.fir@145217.6]
  wire [1:0] _T_87; // @[OneHot.scala 32:28:freechips.rocketchip.system.DefaultRV32Config.fir@145218.6]
  wire  _T_88; // @[CircuitMath.scala 30:8:freechips.rocketchip.system.DefaultRV32Config.fir@145219.6]
  wire [1:0] _T_89; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145220.6]
  wire  _T_91; // @[Replacement.scala 49:20:freechips.rocketchip.system.DefaultRV32Config.fir@145222.6]
  wire  _T_92; // @[Replacement.scala 50:43:freechips.rocketchip.system.DefaultRV32Config.fir@145223.6]
  wire [3:0] _T_94; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145225.6]
  wire [3:0] _T_95; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145226.6]
  wire [3:0] _T_96; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145227.6]
  wire [3:0] _T_97; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145228.6]
  wire [3:0] _T_98; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145229.6]
  wire [1:0] _T_99; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145230.6]
  wire  _T_100; // @[Replacement.scala 49:20:freechips.rocketchip.system.DefaultRV32Config.fir@145231.6]
  wire  _T_101; // @[Replacement.scala 50:43:freechips.rocketchip.system.DefaultRV32Config.fir@145232.6]
  wire [3:0] _T_102; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145233.6]
  wire [3:0] _T_103; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145234.6]
  wire [3:0] _T_104; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145235.6]
  wire [3:0] _T_105; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145236.6]
  wire [3:0] _T_106; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145237.6]
  wire [3:0] _T_107; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145238.6]
  wire [2:0] _T_109; // @[package.scala 120:13:freechips.rocketchip.system.DefaultRV32Config.fir@145240.6]
  wire  _T_110; // @[PTW.scala 164:36:freechips.rocketchip.system.DefaultRV32Config.fir@145243.4]
  wire  _T_111; // @[PTW.scala 164:33:freechips.rocketchip.system.DefaultRV32Config.fir@145244.4]
  wire  pte_cache_hit; // @[PTW.scala 169:10:freechips.rocketchip.system.DefaultRV32Config.fir@145253.4]
  wire  _T_117; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145254.4]
  wire  _T_118; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145255.4]
  wire  _T_119; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145256.4]
  wire  _T_120; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145257.4]
  wire [19:0] _T_121; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145258.4]
  wire [19:0] _T_122; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145259.4]
  wire [19:0] _T_123; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145260.4]
  wire [19:0] _T_124; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145261.4]
  wire [19:0] _T_125; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145262.4]
  wire [19:0] _T_126; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145263.4]
  wire [19:0] pte_cache_data; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145264.4]
  wire  _T_129; // @[PTW.scala 242:56:freechips.rocketchip.system.DefaultRV32Config.fir@145273.4]
  wire  _T_132; // @[PTW.scala 244:48:freechips.rocketchip.system.DefaultRV32Config.fir@145277.4]
  wire [65:0] _T_136; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145289.4]
  wire [66:0] _T_137; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145290.4]
  wire [66:0] _T_138; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145291.4]
  wire [66:0] _T_139; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145292.4]
  wire  _T_140; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145293.4]
  wire [65:0] _T_141; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145294.4]
  wire [66:0] _T_142; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145295.4]
  wire [66:0] _T_143; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145296.4]
  wire [66:0] _T_144; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145297.4]
  wire  _T_145; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145298.4]
  wire [65:0] _T_146; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145299.4]
  wire [66:0] _T_147; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145300.4]
  wire [66:0] _T_148; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145301.4]
  wire [66:0] _T_149; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145302.4]
  wire  _T_150; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145303.4]
  wire  _T_152; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145305.4]
  wire  pmaPgLevelHomogeneous_0; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145306.4]
  wire [66:0] _T_156; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145310.4]
  wire [65:0] _T_185; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145339.4]
  wire [66:0] _T_186; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145340.4]
  wire [66:0] _T_187; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145341.4]
  wire [66:0] _T_188; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145342.4]
  wire  _T_189; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145343.4]
  wire [65:0] _T_195; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145349.4]
  wire [66:0] _T_196; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145350.4]
  wire [66:0] _T_197; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145351.4]
  wire [66:0] _T_198; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145352.4]
  wire  _T_199; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145353.4]
  wire [65:0] _T_200; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145354.4]
  wire [66:0] _T_201; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145355.4]
  wire [66:0] _T_202; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145356.4]
  wire [66:0] _T_203; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145357.4]
  wire  _T_204; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145358.4]
  wire [66:0] _T_212; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145366.4]
  wire [66:0] _T_213; // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145367.4]
  wire  _T_214; // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145368.4]
  wire  _T_216; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145370.4]
  wire  _T_217; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145371.4]
  wire  _T_218; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145372.4]
  wire  _T_219; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145373.4]
  wire  _T_220; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145374.4]
  wire  pmaPgLevelHomogeneous_1; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145375.4]
  wire  pmaHomogeneous; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145428.4]
  wire [53:0] _T_273; // @[PTW.scala 264:79:freechips.rocketchip.system.DefaultRV32Config.fir@145429.4]
  wire [65:0] _T_274; // @[PTW.scala 264:92:freechips.rocketchip.system.DefaultRV32Config.fir@145430.4]
  wire  _T_285; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145452.4]
  wire  _T_286; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145453.4]
  wire  _T_287; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145454.4]
  wire  _T_289; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145456.4]
  wire [31:0] _T_290; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145457.4]
  wire [31:0] _T_291; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145458.4]
  wire [31:0] _T_292; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145459.4]
  wire [31:0] _T_293; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145460.4]
  wire [65:0] _GEN_96; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145461.4]
  wire [65:0] _T_294; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145461.4]
  wire [43:0] _T_295; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145462.4]
  wire  _T_296; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145463.4]
  wire [53:0] _T_302; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145469.4]
  wire  _T_303; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145470.4]
  wire  _T_305; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145472.4]
  wire  _T_306; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145473.4]
  wire  _T_307; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145474.4]
  wire  _T_308; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145475.4]
  wire  _T_319; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145486.4]
  wire  _T_320; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145487.4]
  wire [31:0] _T_322; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145489.4]
  wire [65:0] _GEN_99; // @[PMP.scala 110:30:freechips.rocketchip.system.DefaultRV32Config.fir@145490.4]
  wire [65:0] _T_323; // @[PMP.scala 110:30:freechips.rocketchip.system.DefaultRV32Config.fir@145490.4]
  wire [31:0] _T_335; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145502.4]
  wire [65:0] _GEN_101; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145503.4]
  wire  _T_336; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145503.4]
  wire  _T_339; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145506.4]
  wire  _T_340; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145507.4]
  wire  _T_341; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145508.4]
  wire  _T_343; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145510.4]
  wire  _T_344; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145511.4]
  wire  _T_345; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145512.4]
  wire  _T_347; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145514.4]
  wire [31:0] _T_348; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145515.4]
  wire [31:0] _T_349; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145516.4]
  wire [31:0] _T_350; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145517.4]
  wire [31:0] _T_351; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145518.4]
  wire [65:0] _GEN_102; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145519.4]
  wire [65:0] _T_352; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145519.4]
  wire [43:0] _T_353; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145520.4]
  wire  _T_354; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145521.4]
  wire [53:0] _T_360; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145527.4]
  wire  _T_361; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145528.4]
  wire  _T_363; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145530.4]
  wire  _T_364; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145531.4]
  wire  _T_365; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145532.4]
  wire  _T_366; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145533.4]
  wire  _T_377; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145544.4]
  wire  _T_378; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145545.4]
  wire [31:0] _T_393; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145560.4]
  wire [65:0] _GEN_109; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145561.4]
  wire  _T_394; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145561.4]
  wire  _T_395; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145562.4]
  wire  _T_396; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145563.4]
  wire  _T_397; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145564.4]
  wire  _T_398; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145565.4]
  wire  _T_399; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145566.4]
  wire  _T_400; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145567.4]
  wire  _T_401; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145568.4]
  wire  _T_402; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145569.4]
  wire  _T_403; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145570.4]
  wire  _T_405; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145572.4]
  wire [31:0] _T_406; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145573.4]
  wire [31:0] _T_407; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145574.4]
  wire [31:0] _T_408; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145575.4]
  wire [31:0] _T_409; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145576.4]
  wire [65:0] _GEN_110; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145577.4]
  wire [65:0] _T_410; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145577.4]
  wire [43:0] _T_411; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145578.4]
  wire  _T_412; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145579.4]
  wire [53:0] _T_418; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145585.4]
  wire  _T_419; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145586.4]
  wire  _T_421; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145588.4]
  wire  _T_422; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145589.4]
  wire  _T_423; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145590.4]
  wire  _T_424; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145591.4]
  wire  _T_435; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145602.4]
  wire  _T_436; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145603.4]
  wire [31:0] _T_451; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145618.4]
  wire [65:0] _GEN_117; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145619.4]
  wire  _T_452; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145619.4]
  wire  _T_453; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145620.4]
  wire  _T_454; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145621.4]
  wire  _T_455; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145622.4]
  wire  _T_456; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145623.4]
  wire  _T_457; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145624.4]
  wire  _T_458; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145625.4]
  wire  _T_459; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145626.4]
  wire  _T_460; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145627.4]
  wire  _T_461; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145628.4]
  wire  _T_463; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145630.4]
  wire [31:0] _T_464; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145631.4]
  wire [31:0] _T_465; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145632.4]
  wire [31:0] _T_466; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145633.4]
  wire [31:0] _T_467; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145634.4]
  wire [65:0] _GEN_118; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145635.4]
  wire [65:0] _T_468; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145635.4]
  wire [43:0] _T_469; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145636.4]
  wire  _T_470; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145637.4]
  wire [53:0] _T_476; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145643.4]
  wire  _T_477; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145644.4]
  wire  _T_479; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145646.4]
  wire  _T_480; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145647.4]
  wire  _T_481; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145648.4]
  wire  _T_482; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145649.4]
  wire  _T_493; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145660.4]
  wire  _T_494; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145661.4]
  wire [31:0] _T_509; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145676.4]
  wire [65:0] _GEN_125; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145677.4]
  wire  _T_510; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145677.4]
  wire  _T_511; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145678.4]
  wire  _T_512; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145679.4]
  wire  _T_513; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145680.4]
  wire  _T_514; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145681.4]
  wire  _T_515; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145682.4]
  wire  _T_516; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145683.4]
  wire  _T_517; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145684.4]
  wire  _T_518; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145685.4]
  wire  _T_519; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145686.4]
  wire  _T_521; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145688.4]
  wire [31:0] _T_522; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145689.4]
  wire [31:0] _T_523; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145690.4]
  wire [31:0] _T_524; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145691.4]
  wire [31:0] _T_525; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145692.4]
  wire [65:0] _GEN_126; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145693.4]
  wire [65:0] _T_526; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145693.4]
  wire [43:0] _T_527; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145694.4]
  wire  _T_528; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145695.4]
  wire [53:0] _T_534; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145701.4]
  wire  _T_535; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145702.4]
  wire  _T_537; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145704.4]
  wire  _T_538; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145705.4]
  wire  _T_539; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145706.4]
  wire  _T_540; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145707.4]
  wire  _T_551; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145718.4]
  wire  _T_552; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145719.4]
  wire [31:0] _T_567; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145734.4]
  wire [65:0] _GEN_133; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145735.4]
  wire  _T_568; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145735.4]
  wire  _T_569; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145736.4]
  wire  _T_570; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145737.4]
  wire  _T_571; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145738.4]
  wire  _T_572; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145739.4]
  wire  _T_573; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145740.4]
  wire  _T_574; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145741.4]
  wire  _T_575; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145742.4]
  wire  _T_576; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145743.4]
  wire  _T_577; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145744.4]
  wire  _T_579; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145746.4]
  wire [31:0] _T_580; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145747.4]
  wire [31:0] _T_581; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145748.4]
  wire [31:0] _T_582; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145749.4]
  wire [31:0] _T_583; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145750.4]
  wire [65:0] _GEN_134; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145751.4]
  wire [65:0] _T_584; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145751.4]
  wire [43:0] _T_585; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145752.4]
  wire  _T_586; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145753.4]
  wire [53:0] _T_592; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145759.4]
  wire  _T_593; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145760.4]
  wire  _T_595; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145762.4]
  wire  _T_596; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145763.4]
  wire  _T_597; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145764.4]
  wire  _T_598; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145765.4]
  wire  _T_609; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145776.4]
  wire  _T_610; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145777.4]
  wire [31:0] _T_625; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145792.4]
  wire [65:0] _GEN_141; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145793.4]
  wire  _T_626; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145793.4]
  wire  _T_627; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145794.4]
  wire  _T_628; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145795.4]
  wire  _T_629; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145796.4]
  wire  _T_630; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145797.4]
  wire  _T_631; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145798.4]
  wire  _T_632; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145799.4]
  wire  _T_633; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145800.4]
  wire  _T_634; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145801.4]
  wire  _T_635; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145802.4]
  wire  _T_637; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145804.4]
  wire [31:0] _T_638; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145805.4]
  wire [31:0] _T_639; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145806.4]
  wire [31:0] _T_640; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145807.4]
  wire [31:0] _T_641; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145808.4]
  wire [65:0] _GEN_142; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145809.4]
  wire [65:0] _T_642; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145809.4]
  wire [43:0] _T_643; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145810.4]
  wire  _T_644; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145811.4]
  wire [53:0] _T_650; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145817.4]
  wire  _T_651; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145818.4]
  wire  _T_653; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145820.4]
  wire  _T_654; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145821.4]
  wire  _T_655; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145822.4]
  wire  _T_656; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145823.4]
  wire  _T_667; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145834.4]
  wire  _T_668; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145835.4]
  wire [31:0] _T_683; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145850.4]
  wire [65:0] _GEN_149; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145851.4]
  wire  _T_684; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145851.4]
  wire  _T_685; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145852.4]
  wire  _T_686; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145853.4]
  wire  _T_687; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145854.4]
  wire  _T_688; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145855.4]
  wire  _T_689; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145856.4]
  wire  _T_690; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145857.4]
  wire  _T_691; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145858.4]
  wire  _T_692; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145859.4]
  wire  _T_693; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145860.4]
  wire  _T_695; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145862.4]
  wire [31:0] _T_696; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145863.4]
  wire [31:0] _T_697; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145864.4]
  wire [31:0] _T_698; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145865.4]
  wire [31:0] _T_699; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145866.4]
  wire [65:0] _GEN_150; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145867.4]
  wire [65:0] _T_700; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145867.4]
  wire [43:0] _T_701; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145868.4]
  wire  _T_702; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145869.4]
  wire [53:0] _T_708; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145875.4]
  wire  _T_709; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145876.4]
  wire  _T_711; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145878.4]
  wire  _T_712; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145879.4]
  wire  _T_713; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145880.4]
  wire  _T_714; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145881.4]
  wire  _T_725; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145892.4]
  wire  _T_726; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145893.4]
  wire [31:0] _T_741; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145908.4]
  wire [65:0] _GEN_157; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145909.4]
  wire  _T_742; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145909.4]
  wire  _T_743; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145910.4]
  wire  _T_744; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145911.4]
  wire  _T_745; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145912.4]
  wire  _T_746; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145913.4]
  wire  _T_747; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145914.4]
  wire  pmpHomogeneous; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145915.4]
  wire  homogeneous; // @[PTW.scala 265:36:freechips.rocketchip.system.DefaultRV32Config.fir@145916.4]
  wire  _T_752; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145950.4]
  wire [2:0] _T_754; // @[PTW.scala 287:26:freechips.rocketchip.system.DefaultRV32Config.fir@145954.8]
  wire [2:0] _GEN_23; // @[PTW.scala 286:32:freechips.rocketchip.system.DefaultRV32Config.fir@145953.6]
  wire  _T_756; // @[PTW.scala 289:39:freechips.rocketchip.system.DefaultRV32Config.fir@145958.6]
  wire  _T_757; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145962.6]
  wire  _T_759; // @[PTW.scala 293:24:freechips.rocketchip.system.DefaultRV32Config.fir@145966.10]
  wire [2:0] _T_760; // @[PTW.scala 295:26:freechips.rocketchip.system.DefaultRV32Config.fir@145970.10]
  wire [2:0] _GEN_25; // @[PTW.scala 292:28:freechips.rocketchip.system.DefaultRV32Config.fir@145964.8]
  wire  _T_761; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145975.8]
  wire  _T_763; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145981.10]
  wire  _GEN_26; // @[PTW.scala 307:32:freechips.rocketchip.system.DefaultRV32Config.fir@145989.14]
  wire [2:0] _GEN_29; // @[PTW.scala 304:35:freechips.rocketchip.system.DefaultRV32Config.fir@145984.12]
  wire  _GEN_30; // @[PTW.scala 304:35:freechips.rocketchip.system.DefaultRV32Config.fir@145984.12]
  wire  _GEN_31; // @[PTW.scala 304:35:freechips.rocketchip.system.DefaultRV32Config.fir@145984.12]
  wire  _T_766; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145993.12]
  wire  _T_769; // @[PTW.scala 314:13:freechips.rocketchip.system.DefaultRV32Config.fir@146000.14]
  wire  _GEN_34; // @[PTW.scala 314:27:freechips.rocketchip.system.DefaultRV32Config.fir@146001.14]
  wire [2:0] _GEN_36; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145994.12]
  wire  _GEN_37; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145994.12]
  wire  _GEN_38; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145994.12]
  wire [2:0] _GEN_42; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  wire  _GEN_43; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  wire  _GEN_44; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  wire  _GEN_45; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  wire [2:0] _GEN_48; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145976.8]
  wire  _GEN_50; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145976.8]
  wire  _GEN_51; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145976.8]
  wire [2:0] _GEN_55; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145963.6]
  wire  _GEN_57; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145963.6]
  wire  _GEN_58; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145963.6]
  wire [2:0] _GEN_60; // @[Conditional.scala 40:58:freechips.rocketchip.system.DefaultRV32Config.fir@145951.4]
  wire  _GEN_63; // @[Conditional.scala 40:58:freechips.rocketchip.system.DefaultRV32Config.fir@145951.4]
  wire  _GEN_64; // @[Conditional.scala 40:58:freechips.rocketchip.system.DefaultRV32Config.fir@145951.4]
  wire  _T_772; // @[PTW.scala 329:15:freechips.rocketchip.system.DefaultRV32Config.fir@146008.4]
  wire  _T_774; // @[PTW.scala 329:40:freechips.rocketchip.system.DefaultRV32Config.fir@146010.4]
  wire  _T_776; // @[PTW.scala 330:25:freechips.rocketchip.system.DefaultRV32Config.fir@146016.4]
  wire [53:0] pte_2_ppn; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@146022.4 :freechips.rocketchip.system.DefaultRV32Config.fir@146024.4 PTW.scala 323:13:freechips.rocketchip.system.DefaultRV32Config.fir@146025.4]
  wire [53:0] _T_778_ppn; // @[PTW.scala 331:8:freechips.rocketchip.system.DefaultRV32Config.fir@146026.4]
  wire [53:0] pte_1_ppn; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@146017.4 :freechips.rocketchip.system.DefaultRV32Config.fir@146019.4 PTW.scala 323:13:freechips.rocketchip.system.DefaultRV32Config.fir@146020.4]
  wire [53:0] _T_779_ppn; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_d; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_a; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_g; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_u; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_x; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_w; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_r; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire  _T_779_v; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  wire [53:0] _T_780_ppn; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_d; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_a; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_g; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_u; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_x; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_w; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_r; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _T_780_v; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  wire  _GEN_66; // @[PTW.scala 337:28:freechips.rocketchip.system.DefaultRV32Config.fir@146053.6]
  wire  _GEN_67; // @[PTW.scala 337:28:freechips.rocketchip.system.DefaultRV32Config.fir@146053.6]
  wire  _T_793; // @[PTW.scala 342:18:freechips.rocketchip.system.DefaultRV32Config.fir@146058.6]
  wire  _T_795; // @[PTW.scala 342:11:freechips.rocketchip.system.DefaultRV32Config.fir@146060.6]
  wire  _T_796; // @[PTW.scala 342:11:freechips.rocketchip.system.DefaultRV32Config.fir@146061.6]
  wire  ae; // @[PTW.scala 348:22:freechips.rocketchip.system.DefaultRV32Config.fir@146078.8]
  wire [2:0] _GEN_78; // @[PTW.scala 343:21:freechips.rocketchip.system.DefaultRV32Config.fir@146066.6]
  wire [2:0] _GEN_84; // @[PTW.scala 341:25:freechips.rocketchip.system.DefaultRV32Config.fir@146057.4]
  wire  _T_809; // @[PTW.scala 359:18:freechips.rocketchip.system.DefaultRV32Config.fir@146096.6]
  wire  _T_811; // @[PTW.scala 359:11:freechips.rocketchip.system.DefaultRV32Config.fir@146098.6]
  wire  _T_812; // @[PTW.scala 359:11:freechips.rocketchip.system.DefaultRV32Config.fir@146099.6]
  RRArbiter arb ( // @[PTW.scala 88:19:freechips.rocketchip.system.DefaultRV32Config.fir@145058.4]
    .clock(arb_clock),
    .io_in_0_ready(arb_io_in_0_ready),
    .io_in_0_valid(arb_io_in_0_valid),
    .io_in_0_bits_bits_addr(arb_io_in_0_bits_bits_addr),
    .io_in_1_ready(arb_io_in_1_ready),
    .io_in_1_valid(arb_io_in_1_valid),
    .io_in_1_bits_valid(arb_io_in_1_bits_valid),
    .io_in_1_bits_bits_addr(arb_io_in_1_bits_bits_addr),
    .io_out_ready(arb_io_out_ready),
    .io_out_valid(arb_io_out_valid),
    .io_out_bits_valid(arb_io_out_bits_valid),
    .io_out_bits_bits_addr(arb_io_out_bits_bits_addr),
    .io_chosen(arb_io_chosen)
  );
  _2_79 _2 ( // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@145944.4]
    .io_x(_2_io_x),
    .io_y(_2_io_y)
  );
  _2_80 _2_1 ( // @[package.scala 213:21:freechips.rocketchip.system.DefaultRV32Config.fir@146031.4]
    .io_x_ppn(_2_1_io_x_ppn),
    .io_x_d(_2_1_io_x_d),
    .io_x_a(_2_1_io_x_a),
    .io_x_g(_2_1_io_x_g),
    .io_x_u(_2_1_io_x_u),
    .io_x_x(_2_1_io_x_x),
    .io_x_w(_2_1_io_x_w),
    .io_x_r(_2_1_io_x_r),
    .io_x_v(_2_1_io_x_v),
    .io_y_ppn(_2_1_io_y_ppn),
    .io_y_d(_2_1_io_y_d),
    .io_y_a(_2_1_io_y_a),
    .io_y_g(_2_1_io_y_g),
    .io_y_u(_2_1_io_y_u),
    .io_y_x(_2_1_io_y_x),
    .io_y_w(_2_1_io_y_w),
    .io_y_r(_2_1_io_y_r),
    .io_y_v(_2_1_io_y_v)
  );
  assign _T_2 = state != 3'h0; // @[PTW.scala 94:24:freechips.rocketchip.system.DefaultRV32Config.fir@145072.4]
  assign _T_7 = {{32'd0}, mem_resp_data}; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145094.4 :freechips.rocketchip.system.DefaultRV32Config.fir@145096.4]
  assign tmp_v = _T_7[0]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145097.4]
  assign tmp_r = _T_7[1]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145099.4]
  assign tmp_w = _T_7[2]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145101.4]
  assign tmp_x = _T_7[3]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145103.4]
  assign tmp_u = _T_7[4]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145105.4]
  assign tmp_g = _T_7[5]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145107.4]
  assign tmp_a = _T_7[6]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145109.4]
  assign tmp_d = _T_7[7]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145111.4]
  assign tmp_ppn = _T_7[63:10]; // @[PTW.scala 122:33:freechips.rocketchip.system.DefaultRV32Config.fir@145115.4]
  assign _T_18 = tmp_ppn[19:0]; // @[PTW.scala 124:23:freechips.rocketchip.system.DefaultRV32Config.fir@145120.4]
  assign _T_19 = tmp_r | tmp_w; // @[PTW.scala 125:17:freechips.rocketchip.system.DefaultRV32Config.fir@145122.4]
  assign _T_20 = _T_19 | tmp_x; // @[PTW.scala 125:26:freechips.rocketchip.system.DefaultRV32Config.fir@145123.4]
  assign _T_21 = count <= 1'h0; // @[PTW.scala 128:21:freechips.rocketchip.system.DefaultRV32Config.fir@145125.6]
  assign _T_22 = tmp_ppn[9:0]; // @[PTW.scala 128:36:freechips.rocketchip.system.DefaultRV32Config.fir@145126.6]
  assign _T_23 = _T_22 != 10'h0; // @[PTW.scala 128:95:freechips.rocketchip.system.DefaultRV32Config.fir@145127.6]
  assign _T_24 = _T_21 & _T_23; // @[PTW.scala 128:26:freechips.rocketchip.system.DefaultRV32Config.fir@145128.6]
  assign _GEN_0 = _T_24 ? 1'h0 : tmp_v; // @[PTW.scala 128:102:freechips.rocketchip.system.DefaultRV32Config.fir@145129.6]
  assign res_v = _T_20 ? _GEN_0 : tmp_v; // @[PTW.scala 125:36:freechips.rocketchip.system.DefaultRV32Config.fir@145124.4]
  assign _T_25 = tmp_ppn[53:20]; // @[PTW.scala 130:20:freechips.rocketchip.system.DefaultRV32Config.fir@145133.4]
  assign invalid_paddr = _T_25 != 34'h0; // @[PTW.scala 130:32:freechips.rocketchip.system.DefaultRV32Config.fir@145134.4]
  assign _T_26 = tmp_r == 1'h0; // @[PTW.scala 67:36:freechips.rocketchip.system.DefaultRV32Config.fir@145135.4]
  assign _T_27 = res_v & _T_26; // @[PTW.scala 67:33:freechips.rocketchip.system.DefaultRV32Config.fir@145136.4]
  assign _T_28 = tmp_w == 1'h0; // @[PTW.scala 67:42:freechips.rocketchip.system.DefaultRV32Config.fir@145137.4]
  assign _T_29 = _T_27 & _T_28; // @[PTW.scala 67:39:freechips.rocketchip.system.DefaultRV32Config.fir@145138.4]
  assign _T_30 = tmp_x == 1'h0; // @[PTW.scala 67:48:freechips.rocketchip.system.DefaultRV32Config.fir@145139.4]
  assign _T_31 = _T_29 & _T_30; // @[PTW.scala 67:45:freechips.rocketchip.system.DefaultRV32Config.fir@145140.4]
  assign _T_32 = invalid_paddr == 1'h0; // @[PTW.scala 132:33:freechips.rocketchip.system.DefaultRV32Config.fir@145141.4]
  assign _T_33 = _T_31 & _T_32; // @[PTW.scala 132:30:freechips.rocketchip.system.DefaultRV32Config.fir@145142.4]
  assign _T_34 = count < 1'h1; // @[PTW.scala 132:57:freechips.rocketchip.system.DefaultRV32Config.fir@145143.4]
  assign traverse = _T_33 & _T_34; // @[PTW.scala 132:48:freechips.rocketchip.system.DefaultRV32Config.fir@145144.4]
  assign vpn_idxs_0 = r_req_addr[19:10]; // @[PTW.scala 134:60:freechips.rocketchip.system.DefaultRV32Config.fir@145145.4]
  assign vpn_idxs_1 = r_req_addr[9:0]; // @[PTW.scala 134:90:freechips.rocketchip.system.DefaultRV32Config.fir@145148.4]
  assign vpn_idx = count ? vpn_idxs_1 : vpn_idxs_0; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145150.4]
  assign _T_38 = {r_pte_ppn,vpn_idx}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145151.4]
  assign pte_addr = {_T_38, 2'h0}; // @[PTW.scala 136:29:freechips.rocketchip.system.DefaultRV32Config.fir@145152.4]
  assign _T_39 = r_pte_ppn[53:10]; // @[PTW.scala 139:69:freechips.rocketchip.system.DefaultRV32Config.fir@145153.4]
  assign choices_0 = {_T_39,vpn_idxs_1}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145155.4]
  assign _T_41 = arb_io_out_ready & arb_io_out_valid; // @[Decoupled.scala 40:37:freechips.rocketchip.system.DefaultRV32Config.fir@145156.4]
  assign _GEN_91 = {{34'd0}, tags_0}; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145165.4]
  assign _T_43 = _GEN_91 == pte_addr; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145165.4]
  assign _GEN_92 = {{34'd0}, tags_1}; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145166.4]
  assign _T_44 = _GEN_92 == pte_addr; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145166.4]
  assign _GEN_93 = {{34'd0}, tags_2}; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145167.4]
  assign _T_45 = _GEN_93 == pte_addr; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145167.4]
  assign _GEN_94 = {{34'd0}, tags_3}; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145168.4]
  assign _T_46 = _GEN_94 == pte_addr; // @[PTW.scala 155:27:freechips.rocketchip.system.DefaultRV32Config.fir@145168.4]
  assign _T_49 = {_T_46,_T_45,_T_44,_T_43}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145171.4]
  assign hits = _T_49 & valid; // @[PTW.scala 155:48:freechips.rocketchip.system.DefaultRV32Config.fir@145172.4]
  assign hit = hits != 4'h0; // @[PTW.scala 156:20:freechips.rocketchip.system.DefaultRV32Config.fir@145173.4]
  assign _T_50 = mem_resp_valid & traverse; // @[PTW.scala 157:26:freechips.rocketchip.system.DefaultRV32Config.fir@145174.4]
  assign _T_51 = hit == 1'h0; // @[PTW.scala 157:41:freechips.rocketchip.system.DefaultRV32Config.fir@145175.4]
  assign _T_52 = _T_50 & _T_51; // @[PTW.scala 157:38:freechips.rocketchip.system.DefaultRV32Config.fir@145176.4]
  assign _T_53 = invalidated == 1'h0; // @[PTW.scala 157:49:freechips.rocketchip.system.DefaultRV32Config.fir@145177.4]
  assign _T_54 = _T_52 & _T_53; // @[PTW.scala 157:46:freechips.rocketchip.system.DefaultRV32Config.fir@145178.4]
  assign _T_55 = valid == 4'hf; // @[PTW.scala 158:25:freechips.rocketchip.system.DefaultRV32Config.fir@145180.6]
  assign _T_56 = {_T_42, 1'h0}; // @[Replacement.scala 57:31:freechips.rocketchip.system.DefaultRV32Config.fir@145181.6]
  assign _GEN_95 = _T_56[3:1]; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145185.6]
  assign _T_60 = {{1'd0}, _GEN_95}; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145185.6]
  assign _T_61 = _T_60[0]; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145186.6]
  assign _T_63 = {1'h1,_T_61}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145188.6]
  assign _T_67 = _T_56 >> _T_63; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145192.6]
  assign _T_68 = _T_67[0]; // @[Replacement.scala 61:48:freechips.rocketchip.system.DefaultRV32Config.fir@145193.6]
  assign _T_70 = {1'h1,_T_61,_T_68}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145195.6]
  assign _T_71 = _T_70[1:0]; // @[Replacement.scala 63:8:freechips.rocketchip.system.DefaultRV32Config.fir@145196.6]
  assign _T_72 = ~ valid; // @[PTW.scala 158:61:freechips.rocketchip.system.DefaultRV32Config.fir@145197.6]
  assign _T_73 = _T_72[0]; // @[OneHot.scala 47:40:freechips.rocketchip.system.DefaultRV32Config.fir@145198.6]
  assign _T_74 = _T_72[1]; // @[OneHot.scala 47:40:freechips.rocketchip.system.DefaultRV32Config.fir@145199.6]
  assign _T_75 = _T_72[2]; // @[OneHot.scala 47:40:freechips.rocketchip.system.DefaultRV32Config.fir@145200.6]
  assign _T_77 = _T_75 ? 2'h2 : 2'h3; // @[Mux.scala 47:69:freechips.rocketchip.system.DefaultRV32Config.fir@145202.6]
  assign _T_78 = _T_74 ? 2'h1 : _T_77; // @[Mux.scala 47:69:freechips.rocketchip.system.DefaultRV32Config.fir@145203.6]
  assign _T_79 = _T_73 ? 2'h0 : _T_78; // @[Mux.scala 47:69:freechips.rocketchip.system.DefaultRV32Config.fir@145204.6]
  assign r = _T_55 ? _T_71 : _T_79; // @[PTW.scala 158:18:freechips.rocketchip.system.DefaultRV32Config.fir@145205.6]
  assign _T_80 = 4'h1 << r; // @[OneHot.scala 58:35:freechips.rocketchip.system.DefaultRV32Config.fir@145206.6]
  assign _T_81 = valid | _T_80; // @[PTW.scala 159:22:freechips.rocketchip.system.DefaultRV32Config.fir@145207.6]
  assign _tags_r = pte_addr[31:0]; // @[PTW.scala 160:15:freechips.rocketchip.system.DefaultRV32Config.fir@145209.6 PTW.scala 160:15:freechips.rocketchip.system.DefaultRV32Config.fir@145209.6]
  assign res_ppn = {{34'd0}, _T_18}; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145117.4 :freechips.rocketchip.system.DefaultRV32Config.fir@145119.4 PTW.scala 124:13:freechips.rocketchip.system.DefaultRV32Config.fir@145121.4]
  assign _data_r = res_ppn[19:0]; // @[PTW.scala 161:15:freechips.rocketchip.system.DefaultRV32Config.fir@145210.6 PTW.scala 161:15:freechips.rocketchip.system.DefaultRV32Config.fir@145210.6]
  assign _T_82 = state == 3'h1; // @[PTW.scala 163:24:freechips.rocketchip.system.DefaultRV32Config.fir@145212.4]
  assign _T_83 = hit & _T_82; // @[PTW.scala 163:15:freechips.rocketchip.system.DefaultRV32Config.fir@145213.4]
  assign _T_84 = hits[3:2]; // @[OneHot.scala 30:18:freechips.rocketchip.system.DefaultRV32Config.fir@145215.6]
  assign _T_85 = hits[1:0]; // @[OneHot.scala 31:18:freechips.rocketchip.system.DefaultRV32Config.fir@145216.6]
  assign _T_86 = _T_84 != 2'h0; // @[OneHot.scala 32:14:freechips.rocketchip.system.DefaultRV32Config.fir@145217.6]
  assign _T_87 = _T_84 | _T_85; // @[OneHot.scala 32:28:freechips.rocketchip.system.DefaultRV32Config.fir@145218.6]
  assign _T_88 = _T_87[1]; // @[CircuitMath.scala 30:8:freechips.rocketchip.system.DefaultRV32Config.fir@145219.6]
  assign _T_89 = {_T_86,_T_88}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145220.6]
  assign _T_91 = _T_89[1]; // @[Replacement.scala 49:20:freechips.rocketchip.system.DefaultRV32Config.fir@145222.6]
  assign _T_92 = _T_91 == 1'h0; // @[Replacement.scala 50:43:freechips.rocketchip.system.DefaultRV32Config.fir@145223.6]
  assign _T_94 = _T_56 | 4'h2; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145225.6]
  assign _T_95 = ~ _T_56; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145226.6]
  assign _T_96 = _T_95 | 4'h2; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145227.6]
  assign _T_97 = ~ _T_96; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145228.6]
  assign _T_98 = _T_92 ? _T_94 : _T_97; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145229.6]
  assign _T_99 = {1'h1,_T_91}; // @[Cat.scala 29:58:freechips.rocketchip.system.DefaultRV32Config.fir@145230.6]
  assign _T_100 = _T_89[0]; // @[Replacement.scala 49:20:freechips.rocketchip.system.DefaultRV32Config.fir@145231.6]
  assign _T_101 = _T_100 == 1'h0; // @[Replacement.scala 50:43:freechips.rocketchip.system.DefaultRV32Config.fir@145232.6]
  assign _T_102 = 4'h1 << _T_99; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145233.6]
  assign _T_103 = _T_98 | _T_102; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145234.6]
  assign _T_104 = ~ _T_98; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145235.6]
  assign _T_105 = _T_104 | _T_102; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145236.6]
  assign _T_106 = ~ _T_105; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145237.6]
  assign _T_107 = _T_101 ? _T_103 : _T_106; // @[Replacement.scala 50:37:freechips.rocketchip.system.DefaultRV32Config.fir@145238.6]
  assign _T_109 = _T_107[3:1]; // @[package.scala 120:13:freechips.rocketchip.system.DefaultRV32Config.fir@145240.6]
  assign _T_110 = io_dpath_sfence_bits_rs1 == 1'h0; // @[PTW.scala 164:36:freechips.rocketchip.system.DefaultRV32Config.fir@145243.4]
  assign _T_111 = io_dpath_sfence_valid & _T_110; // @[PTW.scala 164:33:freechips.rocketchip.system.DefaultRV32Config.fir@145244.4]
  assign pte_cache_hit = hit & _T_34; // @[PTW.scala 169:10:freechips.rocketchip.system.DefaultRV32Config.fir@145253.4]
  assign _T_117 = hits[0]; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145254.4]
  assign _T_118 = hits[1]; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145255.4]
  assign _T_119 = hits[2]; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145256.4]
  assign _T_120 = hits[3]; // @[Mux.scala 29:36:freechips.rocketchip.system.DefaultRV32Config.fir@145257.4]
  assign _T_121 = _T_117 ? data_0 : 20'h0; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145258.4]
  assign _T_122 = _T_118 ? data_1 : 20'h0; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145259.4]
  assign _T_123 = _T_119 ? data_2 : 20'h0; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145260.4]
  assign _T_124 = _T_120 ? data_3 : 20'h0; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145261.4]
  assign _T_125 = _T_121 | _T_122; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145262.4]
  assign _T_126 = _T_125 | _T_123; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145263.4]
  assign pte_cache_data = _T_126 | _T_124; // @[Mux.scala 27:72:freechips.rocketchip.system.DefaultRV32Config.fir@145264.4]
  assign _T_129 = invalidated & _T_2; // @[PTW.scala 242:56:freechips.rocketchip.system.DefaultRV32Config.fir@145273.4]
  assign _T_132 = state == 3'h3; // @[PTW.scala 244:48:freechips.rocketchip.system.DefaultRV32Config.fir@145277.4]
  assign _T_136 = pte_addr ^ 66'h60000000; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145289.4]
  assign _T_137 = {1'b0,$signed(_T_136)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145290.4]
  assign _T_138 = $signed(_T_137) & $signed(-67'sh20000000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145291.4]
  assign _T_139 = $signed(_T_138); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145292.4]
  assign _T_140 = $signed(_T_139) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145293.4]
  assign _T_141 = pte_addr ^ 66'hc000000; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145294.4]
  assign _T_142 = {1'b0,$signed(_T_141)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145295.4]
  assign _T_143 = $signed(_T_142) & $signed(-67'sh4000000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145296.4]
  assign _T_144 = $signed(_T_143); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145297.4]
  assign _T_145 = $signed(_T_144) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145298.4]
  assign _T_146 = pte_addr ^ 66'h80000000; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145299.4]
  assign _T_147 = {1'b0,$signed(_T_146)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145300.4]
  assign _T_148 = $signed(_T_147) & $signed(-67'sh10000000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145301.4]
  assign _T_149 = $signed(_T_148); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145302.4]
  assign _T_150 = $signed(_T_149) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145303.4]
  assign _T_152 = _T_140 | _T_145; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145305.4]
  assign pmaPgLevelHomogeneous_0 = _T_152 | _T_150; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145306.4]
  assign _T_156 = {1'b0,$signed(pte_addr)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145310.4]
  assign _T_185 = pte_addr ^ 66'h3000; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145339.4]
  assign _T_186 = {1'b0,$signed(_T_185)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145340.4]
  assign _T_187 = $signed(_T_186) & $signed(-67'sh1000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145341.4]
  assign _T_188 = $signed(_T_187); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145342.4]
  assign _T_189 = $signed(_T_188) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145343.4]
  assign _T_195 = pte_addr ^ 66'h2000000; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145349.4]
  assign _T_196 = {1'b0,$signed(_T_195)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145350.4]
  assign _T_197 = $signed(_T_196) & $signed(-67'sh10000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145351.4]
  assign _T_198 = $signed(_T_197); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145352.4]
  assign _T_199 = $signed(_T_198) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145353.4]
  assign _T_200 = pte_addr ^ 66'h10000; // @[Parameters.scala 125:31:freechips.rocketchip.system.DefaultRV32Config.fir@145354.4]
  assign _T_201 = {1'b0,$signed(_T_200)}; // @[Parameters.scala 125:49:freechips.rocketchip.system.DefaultRV32Config.fir@145355.4]
  assign _T_202 = $signed(_T_201) & $signed(-67'sh10000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145356.4]
  assign _T_203 = $signed(_T_202); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145357.4]
  assign _T_204 = $signed(_T_203) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145358.4]
  assign _T_212 = $signed(_T_156) & $signed(-67'sh1000); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145366.4]
  assign _T_213 = $signed(_T_212); // @[Parameters.scala 125:52:freechips.rocketchip.system.DefaultRV32Config.fir@145367.4]
  assign _T_214 = $signed(_T_213) == $signed(67'sh0); // @[Parameters.scala 125:67:freechips.rocketchip.system.DefaultRV32Config.fir@145368.4]
  assign _T_216 = _T_140 | _T_189; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145370.4]
  assign _T_217 = _T_216 | _T_145; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145371.4]
  assign _T_218 = _T_217 | _T_199; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145372.4]
  assign _T_219 = _T_218 | _T_204; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145373.4]
  assign _T_220 = _T_219 | _T_150; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145374.4]
  assign pmaPgLevelHomogeneous_1 = _T_220 | _T_214; // @[TLBPermissions.scala 98:65:freechips.rocketchip.system.DefaultRV32Config.fir@145375.4]
  assign pmaHomogeneous = count ? pmaPgLevelHomogeneous_1 : pmaPgLevelHomogeneous_0; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145428.4]
  assign _T_273 = pte_addr[65:12]; // @[PTW.scala 264:79:freechips.rocketchip.system.DefaultRV32Config.fir@145429.4]
  assign _T_274 = {_T_273, 12'h0}; // @[PTW.scala 264:92:freechips.rocketchip.system.DefaultRV32Config.fir@145430.4]
  assign _T_285 = io_dpath_pmp_0_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145452.4]
  assign _T_286 = io_dpath_pmp_0_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145453.4]
  assign _T_287 = io_dpath_pmp_0_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145454.4]
  assign _T_289 = count ? _T_287 : _T_286; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145456.4]
  assign _T_290 = {io_dpath_pmp_0_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145457.4]
  assign _T_291 = ~ _T_290; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145458.4]
  assign _T_292 = _T_291 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145459.4]
  assign _T_293 = ~ _T_292; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145460.4]
  assign _GEN_96 = {{34'd0}, _T_293}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145461.4]
  assign _T_294 = _T_274 ^ _GEN_96; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145461.4]
  assign _T_295 = _T_294[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145462.4]
  assign _T_296 = _T_295 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145463.4]
  assign _T_302 = _T_294[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145469.4]
  assign _T_303 = _T_302 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145470.4]
  assign _T_305 = count ? _T_303 : _T_296; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145472.4]
  assign _T_306 = _T_289 | _T_305; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145473.4]
  assign _T_307 = io_dpath_pmp_0_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145474.4]
  assign _T_308 = _T_307 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145475.4]
  assign _T_319 = _T_274 < _GEN_96; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145486.4]
  assign _T_320 = _T_319 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145487.4]
  assign _T_322 = count ? 32'hfffff000 : 32'hffc00000; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145489.4]
  assign _GEN_99 = {{34'd0}, _T_322}; // @[PMP.scala 110:30:freechips.rocketchip.system.DefaultRV32Config.fir@145490.4]
  assign _T_323 = _T_274 & _GEN_99; // @[PMP.scala 110:30:freechips.rocketchip.system.DefaultRV32Config.fir@145490.4]
  assign _T_335 = _T_293 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145502.4]
  assign _GEN_101 = {{34'd0}, _T_335}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145503.4]
  assign _T_336 = _T_323 < _GEN_101; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145503.4]
  assign _T_339 = _T_320 | _T_336; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145506.4]
  assign _T_340 = _T_308 | _T_339; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145507.4]
  assign _T_341 = _T_285 ? _T_306 : _T_340; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145508.4]
  assign _T_343 = io_dpath_pmp_1_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145510.4]
  assign _T_344 = io_dpath_pmp_1_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145511.4]
  assign _T_345 = io_dpath_pmp_1_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145512.4]
  assign _T_347 = count ? _T_345 : _T_344; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145514.4]
  assign _T_348 = {io_dpath_pmp_1_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145515.4]
  assign _T_349 = ~ _T_348; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145516.4]
  assign _T_350 = _T_349 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145517.4]
  assign _T_351 = ~ _T_350; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145518.4]
  assign _GEN_102 = {{34'd0}, _T_351}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145519.4]
  assign _T_352 = _T_274 ^ _GEN_102; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145519.4]
  assign _T_353 = _T_352[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145520.4]
  assign _T_354 = _T_353 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145521.4]
  assign _T_360 = _T_352[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145527.4]
  assign _T_361 = _T_360 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145528.4]
  assign _T_363 = count ? _T_361 : _T_354; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145530.4]
  assign _T_364 = _T_347 | _T_363; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145531.4]
  assign _T_365 = io_dpath_pmp_1_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145532.4]
  assign _T_366 = _T_365 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145533.4]
  assign _T_377 = _T_274 < _GEN_102; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145544.4]
  assign _T_378 = _T_377 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145545.4]
  assign _T_393 = _T_351 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145560.4]
  assign _GEN_109 = {{34'd0}, _T_393}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145561.4]
  assign _T_394 = _T_323 < _GEN_109; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145561.4]
  assign _T_395 = _T_336 | _T_378; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145562.4]
  assign _T_396 = _T_320 & _T_394; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145563.4]
  assign _T_397 = _T_395 | _T_396; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145564.4]
  assign _T_398 = _T_366 | _T_397; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145565.4]
  assign _T_399 = _T_343 ? _T_364 : _T_398; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145566.4]
  assign _T_400 = _T_341 & _T_399; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145567.4]
  assign _T_401 = io_dpath_pmp_2_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145568.4]
  assign _T_402 = io_dpath_pmp_2_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145569.4]
  assign _T_403 = io_dpath_pmp_2_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145570.4]
  assign _T_405 = count ? _T_403 : _T_402; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145572.4]
  assign _T_406 = {io_dpath_pmp_2_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145573.4]
  assign _T_407 = ~ _T_406; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145574.4]
  assign _T_408 = _T_407 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145575.4]
  assign _T_409 = ~ _T_408; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145576.4]
  assign _GEN_110 = {{34'd0}, _T_409}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145577.4]
  assign _T_410 = _T_274 ^ _GEN_110; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145577.4]
  assign _T_411 = _T_410[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145578.4]
  assign _T_412 = _T_411 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145579.4]
  assign _T_418 = _T_410[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145585.4]
  assign _T_419 = _T_418 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145586.4]
  assign _T_421 = count ? _T_419 : _T_412; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145588.4]
  assign _T_422 = _T_405 | _T_421; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145589.4]
  assign _T_423 = io_dpath_pmp_2_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145590.4]
  assign _T_424 = _T_423 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145591.4]
  assign _T_435 = _T_274 < _GEN_110; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145602.4]
  assign _T_436 = _T_435 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145603.4]
  assign _T_451 = _T_409 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145618.4]
  assign _GEN_117 = {{34'd0}, _T_451}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145619.4]
  assign _T_452 = _T_323 < _GEN_117; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145619.4]
  assign _T_453 = _T_394 | _T_436; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145620.4]
  assign _T_454 = _T_378 & _T_452; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145621.4]
  assign _T_455 = _T_453 | _T_454; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145622.4]
  assign _T_456 = _T_424 | _T_455; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145623.4]
  assign _T_457 = _T_401 ? _T_422 : _T_456; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145624.4]
  assign _T_458 = _T_400 & _T_457; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145625.4]
  assign _T_459 = io_dpath_pmp_3_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145626.4]
  assign _T_460 = io_dpath_pmp_3_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145627.4]
  assign _T_461 = io_dpath_pmp_3_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145628.4]
  assign _T_463 = count ? _T_461 : _T_460; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145630.4]
  assign _T_464 = {io_dpath_pmp_3_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145631.4]
  assign _T_465 = ~ _T_464; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145632.4]
  assign _T_466 = _T_465 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145633.4]
  assign _T_467 = ~ _T_466; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145634.4]
  assign _GEN_118 = {{34'd0}, _T_467}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145635.4]
  assign _T_468 = _T_274 ^ _GEN_118; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145635.4]
  assign _T_469 = _T_468[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145636.4]
  assign _T_470 = _T_469 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145637.4]
  assign _T_476 = _T_468[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145643.4]
  assign _T_477 = _T_476 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145644.4]
  assign _T_479 = count ? _T_477 : _T_470; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145646.4]
  assign _T_480 = _T_463 | _T_479; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145647.4]
  assign _T_481 = io_dpath_pmp_3_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145648.4]
  assign _T_482 = _T_481 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145649.4]
  assign _T_493 = _T_274 < _GEN_118; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145660.4]
  assign _T_494 = _T_493 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145661.4]
  assign _T_509 = _T_467 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145676.4]
  assign _GEN_125 = {{34'd0}, _T_509}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145677.4]
  assign _T_510 = _T_323 < _GEN_125; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145677.4]
  assign _T_511 = _T_452 | _T_494; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145678.4]
  assign _T_512 = _T_436 & _T_510; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145679.4]
  assign _T_513 = _T_511 | _T_512; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145680.4]
  assign _T_514 = _T_482 | _T_513; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145681.4]
  assign _T_515 = _T_459 ? _T_480 : _T_514; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145682.4]
  assign _T_516 = _T_458 & _T_515; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145683.4]
  assign _T_517 = io_dpath_pmp_4_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145684.4]
  assign _T_518 = io_dpath_pmp_4_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145685.4]
  assign _T_519 = io_dpath_pmp_4_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145686.4]
  assign _T_521 = count ? _T_519 : _T_518; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145688.4]
  assign _T_522 = {io_dpath_pmp_4_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145689.4]
  assign _T_523 = ~ _T_522; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145690.4]
  assign _T_524 = _T_523 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145691.4]
  assign _T_525 = ~ _T_524; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145692.4]
  assign _GEN_126 = {{34'd0}, _T_525}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145693.4]
  assign _T_526 = _T_274 ^ _GEN_126; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145693.4]
  assign _T_527 = _T_526[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145694.4]
  assign _T_528 = _T_527 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145695.4]
  assign _T_534 = _T_526[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145701.4]
  assign _T_535 = _T_534 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145702.4]
  assign _T_537 = count ? _T_535 : _T_528; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145704.4]
  assign _T_538 = _T_521 | _T_537; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145705.4]
  assign _T_539 = io_dpath_pmp_4_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145706.4]
  assign _T_540 = _T_539 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145707.4]
  assign _T_551 = _T_274 < _GEN_126; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145718.4]
  assign _T_552 = _T_551 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145719.4]
  assign _T_567 = _T_525 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145734.4]
  assign _GEN_133 = {{34'd0}, _T_567}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145735.4]
  assign _T_568 = _T_323 < _GEN_133; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145735.4]
  assign _T_569 = _T_510 | _T_552; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145736.4]
  assign _T_570 = _T_494 & _T_568; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145737.4]
  assign _T_571 = _T_569 | _T_570; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145738.4]
  assign _T_572 = _T_540 | _T_571; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145739.4]
  assign _T_573 = _T_517 ? _T_538 : _T_572; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145740.4]
  assign _T_574 = _T_516 & _T_573; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145741.4]
  assign _T_575 = io_dpath_pmp_5_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145742.4]
  assign _T_576 = io_dpath_pmp_5_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145743.4]
  assign _T_577 = io_dpath_pmp_5_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145744.4]
  assign _T_579 = count ? _T_577 : _T_576; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145746.4]
  assign _T_580 = {io_dpath_pmp_5_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145747.4]
  assign _T_581 = ~ _T_580; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145748.4]
  assign _T_582 = _T_581 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145749.4]
  assign _T_583 = ~ _T_582; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145750.4]
  assign _GEN_134 = {{34'd0}, _T_583}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145751.4]
  assign _T_584 = _T_274 ^ _GEN_134; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145751.4]
  assign _T_585 = _T_584[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145752.4]
  assign _T_586 = _T_585 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145753.4]
  assign _T_592 = _T_584[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145759.4]
  assign _T_593 = _T_592 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145760.4]
  assign _T_595 = count ? _T_593 : _T_586; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145762.4]
  assign _T_596 = _T_579 | _T_595; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145763.4]
  assign _T_597 = io_dpath_pmp_5_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145764.4]
  assign _T_598 = _T_597 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145765.4]
  assign _T_609 = _T_274 < _GEN_134; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145776.4]
  assign _T_610 = _T_609 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145777.4]
  assign _T_625 = _T_583 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145792.4]
  assign _GEN_141 = {{34'd0}, _T_625}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145793.4]
  assign _T_626 = _T_323 < _GEN_141; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145793.4]
  assign _T_627 = _T_568 | _T_610; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145794.4]
  assign _T_628 = _T_552 & _T_626; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145795.4]
  assign _T_629 = _T_627 | _T_628; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145796.4]
  assign _T_630 = _T_598 | _T_629; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145797.4]
  assign _T_631 = _T_575 ? _T_596 : _T_630; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145798.4]
  assign _T_632 = _T_574 & _T_631; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145799.4]
  assign _T_633 = io_dpath_pmp_6_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145800.4]
  assign _T_634 = io_dpath_pmp_6_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145801.4]
  assign _T_635 = io_dpath_pmp_6_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145802.4]
  assign _T_637 = count ? _T_635 : _T_634; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145804.4]
  assign _T_638 = {io_dpath_pmp_6_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145805.4]
  assign _T_639 = ~ _T_638; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145806.4]
  assign _T_640 = _T_639 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145807.4]
  assign _T_641 = ~ _T_640; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145808.4]
  assign _GEN_142 = {{34'd0}, _T_641}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145809.4]
  assign _T_642 = _T_274 ^ _GEN_142; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145809.4]
  assign _T_643 = _T_642[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145810.4]
  assign _T_644 = _T_643 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145811.4]
  assign _T_650 = _T_642[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145817.4]
  assign _T_651 = _T_650 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145818.4]
  assign _T_653 = count ? _T_651 : _T_644; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145820.4]
  assign _T_654 = _T_637 | _T_653; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145821.4]
  assign _T_655 = io_dpath_pmp_6_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145822.4]
  assign _T_656 = _T_655 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145823.4]
  assign _T_667 = _T_274 < _GEN_142; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145834.4]
  assign _T_668 = _T_667 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145835.4]
  assign _T_683 = _T_641 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145850.4]
  assign _GEN_149 = {{34'd0}, _T_683}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145851.4]
  assign _T_684 = _T_323 < _GEN_149; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145851.4]
  assign _T_685 = _T_626 | _T_668; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145852.4]
  assign _T_686 = _T_610 & _T_684; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145853.4]
  assign _T_687 = _T_685 | _T_686; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145854.4]
  assign _T_688 = _T_656 | _T_687; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145855.4]
  assign _T_689 = _T_633 ? _T_654 : _T_688; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145856.4]
  assign _T_690 = _T_632 & _T_689; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145857.4]
  assign _T_691 = io_dpath_pmp_7_cfg_a[1]; // @[PMP.scala 45:20:freechips.rocketchip.system.DefaultRV32Config.fir@145858.4]
  assign _T_692 = io_dpath_pmp_7_mask[21]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145859.4]
  assign _T_693 = io_dpath_pmp_7_mask[11]; // @[PMP.scala 97:93:freechips.rocketchip.system.DefaultRV32Config.fir@145860.4]
  assign _T_695 = count ? _T_693 : _T_692; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145862.4]
  assign _T_696 = {io_dpath_pmp_7_addr, 2'h0}; // @[PMP.scala 60:36:freechips.rocketchip.system.DefaultRV32Config.fir@145863.4]
  assign _T_697 = ~ _T_696; // @[PMP.scala 60:29:freechips.rocketchip.system.DefaultRV32Config.fir@145864.4]
  assign _T_698 = _T_697 | 32'h3; // @[PMP.scala 60:48:freechips.rocketchip.system.DefaultRV32Config.fir@145865.4]
  assign _T_699 = ~ _T_698; // @[PMP.scala 60:27:freechips.rocketchip.system.DefaultRV32Config.fir@145866.4]
  assign _GEN_150 = {{34'd0}, _T_699}; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145867.4]
  assign _T_700 = _T_274 ^ _GEN_150; // @[PMP.scala 98:53:freechips.rocketchip.system.DefaultRV32Config.fir@145867.4]
  assign _T_701 = _T_700[65:22]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145868.4]
  assign _T_702 = _T_701 != 44'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145869.4]
  assign _T_708 = _T_700[65:12]; // @[PMP.scala 98:66:freechips.rocketchip.system.DefaultRV32Config.fir@145875.4]
  assign _T_709 = _T_708 != 54'h0; // @[PMP.scala 98:78:freechips.rocketchip.system.DefaultRV32Config.fir@145876.4]
  assign _T_711 = count ? _T_709 : _T_702; // @[package.scala 32:71:freechips.rocketchip.system.DefaultRV32Config.fir@145878.4]
  assign _T_712 = _T_695 | _T_711; // @[PMP.scala 98:21:freechips.rocketchip.system.DefaultRV32Config.fir@145879.4]
  assign _T_713 = io_dpath_pmp_7_cfg_a[0]; // @[PMP.scala 46:26:freechips.rocketchip.system.DefaultRV32Config.fir@145880.4]
  assign _T_714 = _T_713 == 1'h0; // @[PMP.scala 118:45:freechips.rocketchip.system.DefaultRV32Config.fir@145881.4]
  assign _T_725 = _T_274 < _GEN_150; // @[PMP.scala 107:32:freechips.rocketchip.system.DefaultRV32Config.fir@145892.4]
  assign _T_726 = _T_725 == 1'h0; // @[PMP.scala 107:28:freechips.rocketchip.system.DefaultRV32Config.fir@145893.4]
  assign _T_741 = _T_699 & _T_322; // @[PMP.scala 111:53:freechips.rocketchip.system.DefaultRV32Config.fir@145908.4]
  assign _GEN_157 = {{34'd0}, _T_741}; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145909.4]
  assign _T_742 = _T_323 < _GEN_157; // @[PMP.scala 111:40:freechips.rocketchip.system.DefaultRV32Config.fir@145909.4]
  assign _T_743 = _T_684 | _T_726; // @[PMP.scala 113:21:freechips.rocketchip.system.DefaultRV32Config.fir@145910.4]
  assign _T_744 = _T_668 & _T_742; // @[PMP.scala 113:62:freechips.rocketchip.system.DefaultRV32Config.fir@145911.4]
  assign _T_745 = _T_743 | _T_744; // @[PMP.scala 113:41:freechips.rocketchip.system.DefaultRV32Config.fir@145912.4]
  assign _T_746 = _T_714 | _T_745; // @[PMP.scala 118:58:freechips.rocketchip.system.DefaultRV32Config.fir@145913.4]
  assign _T_747 = _T_691 ? _T_712 : _T_746; // @[PMP.scala 118:8:freechips.rocketchip.system.DefaultRV32Config.fir@145914.4]
  assign pmpHomogeneous = _T_690 & _T_747; // @[PMP.scala 138:10:freechips.rocketchip.system.DefaultRV32Config.fir@145915.4]
  assign homogeneous = pmaHomogeneous & pmpHomogeneous; // @[PTW.scala 265:36:freechips.rocketchip.system.DefaultRV32Config.fir@145916.4]
  assign _T_752 = 3'h0 == state; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145950.4]
  assign _T_754 = arb_io_out_bits_valid ? 3'h1 : 3'h0; // @[PTW.scala 287:26:freechips.rocketchip.system.DefaultRV32Config.fir@145954.8]
  assign _GEN_23 = _T_41 ? _T_754 : state; // @[PTW.scala 286:32:freechips.rocketchip.system.DefaultRV32Config.fir@145953.6]
  assign _T_756 = 1'h0 - 1'h0; // @[PTW.scala 289:39:freechips.rocketchip.system.DefaultRV32Config.fir@145958.6]
  assign _T_757 = 3'h1 == state; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145962.6]
  assign _T_759 = count + 1'h1; // @[PTW.scala 293:24:freechips.rocketchip.system.DefaultRV32Config.fir@145966.10]
  assign _T_760 = io_mem_req_ready ? 3'h2 : 3'h1; // @[PTW.scala 295:26:freechips.rocketchip.system.DefaultRV32Config.fir@145970.10]
  assign _GEN_25 = pte_cache_hit ? state : _T_760; // @[PTW.scala 292:28:freechips.rocketchip.system.DefaultRV32Config.fir@145964.8]
  assign _T_761 = 3'h2 == state; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145975.8]
  assign _T_763 = 3'h4 == state; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145981.10]
  assign _GEN_26 = 1'h0 == r_req_dest; // @[PTW.scala 307:32:freechips.rocketchip.system.DefaultRV32Config.fir@145989.14]
  assign _GEN_29 = io_mem_s2_xcpt_ae_ld ? 3'h0 : 3'h5; // @[PTW.scala 304:35:freechips.rocketchip.system.DefaultRV32Config.fir@145984.12]
  assign _GEN_30 = io_mem_s2_xcpt_ae_ld & _GEN_26; // @[PTW.scala 304:35:freechips.rocketchip.system.DefaultRV32Config.fir@145984.12]
  assign _GEN_31 = io_mem_s2_xcpt_ae_ld & r_req_dest; // @[PTW.scala 304:35:freechips.rocketchip.system.DefaultRV32Config.fir@145984.12]
  assign _T_766 = 3'h7 == state; // @[Conditional.scala 37:30:freechips.rocketchip.system.DefaultRV32Config.fir@145993.12]
  assign _T_769 = homogeneous == 1'h0; // @[PTW.scala 314:13:freechips.rocketchip.system.DefaultRV32Config.fir@146000.14]
  assign _GEN_34 = _T_769 | count; // @[PTW.scala 314:27:freechips.rocketchip.system.DefaultRV32Config.fir@146001.14]
  assign _GEN_36 = _T_766 ? 3'h0 : state; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145994.12]
  assign _GEN_37 = _T_766 & _GEN_26; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145994.12]
  assign _GEN_38 = _T_766 & r_req_dest; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145994.12]
  assign _GEN_42 = _T_763 ? _GEN_29 : _GEN_36; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  assign _GEN_43 = _T_763 & io_mem_s2_xcpt_ae_ld; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  assign _GEN_44 = _T_763 ? _GEN_30 : _GEN_37; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  assign _GEN_45 = _T_763 ? _GEN_31 : _GEN_38; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145982.10]
  assign _GEN_48 = _T_761 ? 3'h4 : _GEN_42; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145976.8]
  assign _GEN_50 = _T_761 ? 1'h0 : _GEN_44; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145976.8]
  assign _GEN_51 = _T_761 ? 1'h0 : _GEN_45; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145976.8]
  assign _GEN_55 = _T_757 ? _GEN_25 : _GEN_48; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145963.6]
  assign _GEN_57 = _T_757 ? 1'h0 : _GEN_50; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145963.6]
  assign _GEN_58 = _T_757 ? 1'h0 : _GEN_51; // @[Conditional.scala 39:67:freechips.rocketchip.system.DefaultRV32Config.fir@145963.6]
  assign _GEN_60 = _T_752 ? _GEN_23 : _GEN_55; // @[Conditional.scala 40:58:freechips.rocketchip.system.DefaultRV32Config.fir@145951.4]
  assign _GEN_63 = _T_752 ? 1'h0 : _GEN_57; // @[Conditional.scala 40:58:freechips.rocketchip.system.DefaultRV32Config.fir@145951.4]
  assign _GEN_64 = _T_752 ? 1'h0 : _GEN_58; // @[Conditional.scala 40:58:freechips.rocketchip.system.DefaultRV32Config.fir@145951.4]
  assign _T_772 = state == 3'h7; // @[PTW.scala 329:15:freechips.rocketchip.system.DefaultRV32Config.fir@146008.4]
  assign _T_774 = _T_772 & _T_769; // @[PTW.scala 329:40:freechips.rocketchip.system.DefaultRV32Config.fir@146010.4]
  assign _T_776 = _T_82 & pte_cache_hit; // @[PTW.scala 330:25:freechips.rocketchip.system.DefaultRV32Config.fir@146016.4]
  assign pte_2_ppn = {{32'd0}, io_dpath_ptbr_ppn}; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@146022.4 :freechips.rocketchip.system.DefaultRV32Config.fir@146024.4 PTW.scala 323:13:freechips.rocketchip.system.DefaultRV32Config.fir@146025.4]
  assign _T_778_ppn = _T_41 ? pte_2_ppn : r_pte_ppn; // @[PTW.scala 331:8:freechips.rocketchip.system.DefaultRV32Config.fir@146026.4]
  assign pte_1_ppn = {{34'd0}, pte_cache_data}; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@146017.4 :freechips.rocketchip.system.DefaultRV32Config.fir@146019.4 PTW.scala 323:13:freechips.rocketchip.system.DefaultRV32Config.fir@146020.4]
  assign _T_779_ppn = _T_776 ? pte_1_ppn : _T_778_ppn; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_d = _T_776 ? 1'h0 : r_pte_d; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_a = _T_776 ? 1'h0 : r_pte_a; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_g = _T_776 ? 1'h0 : r_pte_g; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_u = _T_776 ? 1'h0 : r_pte_u; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_x = _T_776 ? 1'h0 : r_pte_x; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_w = _T_776 ? 1'h0 : r_pte_w; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_r = _T_776 ? 1'h0 : r_pte_r; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_779_v = _T_776 ? 1'h0 : r_pte_v; // @[PTW.scala 330:8:freechips.rocketchip.system.DefaultRV32Config.fir@146027.4]
  assign _T_780_ppn = _T_774 ? choices_0 : _T_779_ppn; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_d = _T_774 ? r_pte_d : _T_779_d; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_a = _T_774 ? r_pte_a : _T_779_a; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_g = _T_774 ? r_pte_g : _T_779_g; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_u = _T_774 ? r_pte_u : _T_779_u; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_x = _T_774 ? r_pte_x : _T_779_x; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_w = _T_774 ? r_pte_w : _T_779_w; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_r = _T_774 ? r_pte_r : _T_779_r; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _T_780_v = _T_774 ? r_pte_v : _T_779_v; // @[PTW.scala 329:8:freechips.rocketchip.system.DefaultRV32Config.fir@146028.4]
  assign _GEN_66 = _GEN_26 | _GEN_63; // @[PTW.scala 337:28:freechips.rocketchip.system.DefaultRV32Config.fir@146053.6]
  assign _GEN_67 = r_req_dest | _GEN_64; // @[PTW.scala 337:28:freechips.rocketchip.system.DefaultRV32Config.fir@146053.6]
  assign _T_793 = state == 3'h5; // @[PTW.scala 342:18:freechips.rocketchip.system.DefaultRV32Config.fir@146058.6]
  assign _T_795 = _T_793 | reset; // @[PTW.scala 342:11:freechips.rocketchip.system.DefaultRV32Config.fir@146060.6]
  assign _T_796 = _T_795 == 1'h0; // @[PTW.scala 342:11:freechips.rocketchip.system.DefaultRV32Config.fir@146061.6]
  assign ae = res_v & invalid_paddr; // @[PTW.scala 348:22:freechips.rocketchip.system.DefaultRV32Config.fir@146078.8]
  assign _GEN_78 = traverse ? 3'h1 : 3'h0; // @[PTW.scala 343:21:freechips.rocketchip.system.DefaultRV32Config.fir@146066.6]
  assign _GEN_84 = mem_resp_valid ? _GEN_78 : _GEN_60; // @[PTW.scala 341:25:freechips.rocketchip.system.DefaultRV32Config.fir@146057.4]
  assign _T_809 = state == 3'h4; // @[PTW.scala 359:18:freechips.rocketchip.system.DefaultRV32Config.fir@146096.6]
  assign _T_811 = _T_809 | reset; // @[PTW.scala 359:11:freechips.rocketchip.system.DefaultRV32Config.fir@146098.6]
  assign _T_812 = _T_811 == 1'h0; // @[PTW.scala 359:11:freechips.rocketchip.system.DefaultRV32Config.fir@146099.6]
  assign io_requestor_0_req_ready = arb_io_in_0_ready; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145062.4]
  assign io_requestor_0_resp_valid = resp_valid_0; // @[PTW.scala 268:32:freechips.rocketchip.system.DefaultRV32Config.fir@145917.4]
  assign io_requestor_0_resp_bits_ae = resp_ae; // @[PTW.scala 269:34:freechips.rocketchip.system.DefaultRV32Config.fir@145918.4]
  assign io_requestor_0_resp_bits_pte_ppn = r_pte_ppn; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_d = r_pte_d; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_a = r_pte_a; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_g = r_pte_g; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_u = r_pte_u; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_x = r_pte_x; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_w = r_pte_w; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_r = r_pte_r; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_pte_v = r_pte_v; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145919.4]
  assign io_requestor_0_resp_bits_level = count; // @[PTW.scala 271:37:freechips.rocketchip.system.DefaultRV32Config.fir@145920.4]
  assign io_requestor_0_resp_bits_homogeneous = pmaHomogeneous & pmpHomogeneous; // @[PTW.scala 272:43:freechips.rocketchip.system.DefaultRV32Config.fir@145922.4]
  assign io_requestor_0_ptbr_mode = io_dpath_ptbr_mode; // @[PTW.scala 274:26:freechips.rocketchip.system.DefaultRV32Config.fir@145925.4]
  assign io_requestor_0_status_debug = io_dpath_status_debug; // @[PTW.scala 276:28:freechips.rocketchip.system.DefaultRV32Config.fir@145927.4]
  assign io_requestor_0_status_dprv = io_dpath_status_dprv; // @[PTW.scala 276:28:freechips.rocketchip.system.DefaultRV32Config.fir@145927.4]
  assign io_requestor_0_status_mxr = io_dpath_status_mxr; // @[PTW.scala 276:28:freechips.rocketchip.system.DefaultRV32Config.fir@145927.4]
  assign io_requestor_0_status_sum = io_dpath_status_sum; // @[PTW.scala 276:28:freechips.rocketchip.system.DefaultRV32Config.fir@145927.4]
  assign io_requestor_0_pmp_0_cfg_l = io_dpath_pmp_0_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_0_cfg_a = io_dpath_pmp_0_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_0_cfg_x = io_dpath_pmp_0_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_0_cfg_w = io_dpath_pmp_0_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_0_cfg_r = io_dpath_pmp_0_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_0_addr = io_dpath_pmp_0_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_0_mask = io_dpath_pmp_0_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_cfg_l = io_dpath_pmp_1_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_cfg_a = io_dpath_pmp_1_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_cfg_x = io_dpath_pmp_1_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_cfg_w = io_dpath_pmp_1_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_cfg_r = io_dpath_pmp_1_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_addr = io_dpath_pmp_1_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_1_mask = io_dpath_pmp_1_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_cfg_l = io_dpath_pmp_2_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_cfg_a = io_dpath_pmp_2_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_cfg_x = io_dpath_pmp_2_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_cfg_w = io_dpath_pmp_2_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_cfg_r = io_dpath_pmp_2_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_addr = io_dpath_pmp_2_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_2_mask = io_dpath_pmp_2_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_cfg_l = io_dpath_pmp_3_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_cfg_a = io_dpath_pmp_3_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_cfg_x = io_dpath_pmp_3_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_cfg_w = io_dpath_pmp_3_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_cfg_r = io_dpath_pmp_3_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_addr = io_dpath_pmp_3_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_3_mask = io_dpath_pmp_3_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_cfg_l = io_dpath_pmp_4_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_cfg_a = io_dpath_pmp_4_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_cfg_x = io_dpath_pmp_4_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_cfg_w = io_dpath_pmp_4_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_cfg_r = io_dpath_pmp_4_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_addr = io_dpath_pmp_4_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_4_mask = io_dpath_pmp_4_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_cfg_l = io_dpath_pmp_5_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_cfg_a = io_dpath_pmp_5_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_cfg_x = io_dpath_pmp_5_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_cfg_w = io_dpath_pmp_5_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_cfg_r = io_dpath_pmp_5_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_addr = io_dpath_pmp_5_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_5_mask = io_dpath_pmp_5_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_cfg_l = io_dpath_pmp_6_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_cfg_a = io_dpath_pmp_6_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_cfg_x = io_dpath_pmp_6_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_cfg_w = io_dpath_pmp_6_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_cfg_r = io_dpath_pmp_6_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_addr = io_dpath_pmp_6_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_6_mask = io_dpath_pmp_6_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_cfg_l = io_dpath_pmp_7_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_cfg_a = io_dpath_pmp_7_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_cfg_x = io_dpath_pmp_7_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_cfg_w = io_dpath_pmp_7_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_cfg_r = io_dpath_pmp_7_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_addr = io_dpath_pmp_7_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_0_pmp_7_mask = io_dpath_pmp_7_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145928.4]
  assign io_requestor_1_req_ready = arb_io_in_1_ready; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145063.4]
  assign io_requestor_1_resp_valid = resp_valid_1; // @[PTW.scala 268:32:freechips.rocketchip.system.DefaultRV32Config.fir@145929.4]
  assign io_requestor_1_resp_bits_ae = resp_ae; // @[PTW.scala 269:34:freechips.rocketchip.system.DefaultRV32Config.fir@145930.4]
  assign io_requestor_1_resp_bits_pte_ppn = r_pte_ppn; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_d = r_pte_d; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_a = r_pte_a; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_g = r_pte_g; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_u = r_pte_u; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_x = r_pte_x; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_w = r_pte_w; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_r = r_pte_r; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_pte_v = r_pte_v; // @[PTW.scala 270:35:freechips.rocketchip.system.DefaultRV32Config.fir@145931.4]
  assign io_requestor_1_resp_bits_level = count; // @[PTW.scala 271:37:freechips.rocketchip.system.DefaultRV32Config.fir@145932.4]
  assign io_requestor_1_resp_bits_homogeneous = pmaHomogeneous & pmpHomogeneous; // @[PTW.scala 272:43:freechips.rocketchip.system.DefaultRV32Config.fir@145934.4]
  assign io_requestor_1_ptbr_mode = io_dpath_ptbr_mode; // @[PTW.scala 274:26:freechips.rocketchip.system.DefaultRV32Config.fir@145937.4]
  assign io_requestor_1_status_debug = io_dpath_status_debug; // @[PTW.scala 276:28:freechips.rocketchip.system.DefaultRV32Config.fir@145939.4]
  assign io_requestor_1_status_prv = io_dpath_status_prv; // @[PTW.scala 276:28:freechips.rocketchip.system.DefaultRV32Config.fir@145939.4]
  assign io_requestor_1_pmp_0_cfg_l = io_dpath_pmp_0_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_0_cfg_a = io_dpath_pmp_0_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_0_cfg_x = io_dpath_pmp_0_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_0_cfg_w = io_dpath_pmp_0_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_0_cfg_r = io_dpath_pmp_0_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_0_addr = io_dpath_pmp_0_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_0_mask = io_dpath_pmp_0_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_cfg_l = io_dpath_pmp_1_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_cfg_a = io_dpath_pmp_1_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_cfg_x = io_dpath_pmp_1_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_cfg_w = io_dpath_pmp_1_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_cfg_r = io_dpath_pmp_1_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_addr = io_dpath_pmp_1_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_1_mask = io_dpath_pmp_1_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_cfg_l = io_dpath_pmp_2_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_cfg_a = io_dpath_pmp_2_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_cfg_x = io_dpath_pmp_2_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_cfg_w = io_dpath_pmp_2_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_cfg_r = io_dpath_pmp_2_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_addr = io_dpath_pmp_2_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_2_mask = io_dpath_pmp_2_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_cfg_l = io_dpath_pmp_3_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_cfg_a = io_dpath_pmp_3_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_cfg_x = io_dpath_pmp_3_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_cfg_w = io_dpath_pmp_3_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_cfg_r = io_dpath_pmp_3_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_addr = io_dpath_pmp_3_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_3_mask = io_dpath_pmp_3_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_cfg_l = io_dpath_pmp_4_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_cfg_a = io_dpath_pmp_4_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_cfg_x = io_dpath_pmp_4_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_cfg_w = io_dpath_pmp_4_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_cfg_r = io_dpath_pmp_4_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_addr = io_dpath_pmp_4_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_4_mask = io_dpath_pmp_4_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_cfg_l = io_dpath_pmp_5_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_cfg_a = io_dpath_pmp_5_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_cfg_x = io_dpath_pmp_5_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_cfg_w = io_dpath_pmp_5_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_cfg_r = io_dpath_pmp_5_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_addr = io_dpath_pmp_5_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_5_mask = io_dpath_pmp_5_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_cfg_l = io_dpath_pmp_6_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_cfg_a = io_dpath_pmp_6_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_cfg_x = io_dpath_pmp_6_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_cfg_w = io_dpath_pmp_6_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_cfg_r = io_dpath_pmp_6_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_addr = io_dpath_pmp_6_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_6_mask = io_dpath_pmp_6_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_cfg_l = io_dpath_pmp_7_cfg_l; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_cfg_a = io_dpath_pmp_7_cfg_a; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_cfg_x = io_dpath_pmp_7_cfg_x; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_cfg_w = io_dpath_pmp_7_cfg_w; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_cfg_r = io_dpath_pmp_7_cfg_r; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_addr = io_dpath_pmp_7_addr; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_requestor_1_pmp_7_mask = io_dpath_pmp_7_mask; // @[PTW.scala 277:25:freechips.rocketchip.system.DefaultRV32Config.fir@145940.4]
  assign io_mem_req_valid = _T_82 | _T_132; // @[PTW.scala 244:20:freechips.rocketchip.system.DefaultRV32Config.fir@145279.4]
  assign io_mem_req_bits_addr = pte_addr[31:0]; // @[PTW.scala 249:24:freechips.rocketchip.system.DefaultRV32Config.fir@145284.4]
  assign io_mem_s1_kill = state != 3'h2; // @[PTW.scala 250:18:freechips.rocketchip.system.DefaultRV32Config.fir@145287.4]
  assign arb_clock = clock; // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145060.4]
  assign arb_io_in_0_valid = io_requestor_0_req_valid; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145062.4]
  assign arb_io_in_0_bits_bits_addr = io_requestor_0_req_bits_bits_addr; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145062.4]
  assign arb_io_in_1_valid = io_requestor_1_req_valid; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145063.4]
  assign arb_io_in_1_bits_valid = io_requestor_1_req_bits_valid; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145063.4]
  assign arb_io_in_1_bits_bits_addr = io_requestor_1_req_bits_bits_addr; // @[PTW.scala 89:13:freechips.rocketchip.system.DefaultRV32Config.fir@145063.4]
  assign arb_io_out_ready = state == 3'h0; // @[PTW.scala 90:20:freechips.rocketchip.system.DefaultRV32Config.fir@145065.4]
  assign _2_io_x = io_mem_s2_nack ? 3'h1 : _GEN_84; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@145948.4]
  assign _2_1_io_x_ppn = mem_resp_valid ? res_ppn : _T_780_ppn; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_d = mem_resp_valid ? tmp_d : _T_780_d; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_a = mem_resp_valid ? tmp_a : _T_780_a; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_g = mem_resp_valid ? tmp_g : _T_780_g; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_u = mem_resp_valid ? tmp_u : _T_780_u; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_x = mem_resp_valid ? tmp_x : _T_780_x; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_w = mem_resp_valid ? tmp_w : _T_780_w; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_r = mem_resp_valid ? tmp_r : _T_780_r; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
  assign _2_1_io_x_v = mem_resp_valid ? res_v : _T_780_v; // @[package.scala 220:14:freechips.rocketchip.system.DefaultRV32Config.fir@146035.4]
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
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  resp_valid_0 = _RAND_1[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  resp_valid_1 = _RAND_2[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {1{`RANDOM}};
  invalidated = _RAND_3[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {1{`RANDOM}};
  count = _RAND_4[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  resp_ae = _RAND_5[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_6 = {1{`RANDOM}};
  r_req_addr = _RAND_6[19:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_7 = {1{`RANDOM}};
  r_req_dest = _RAND_7[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_8 = {2{`RANDOM}};
  r_pte_ppn = _RAND_8[53:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_9 = {1{`RANDOM}};
  r_pte_d = _RAND_9[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_10 = {1{`RANDOM}};
  r_pte_a = _RAND_10[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_11 = {1{`RANDOM}};
  r_pte_g = _RAND_11[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_12 = {1{`RANDOM}};
  r_pte_u = _RAND_12[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_13 = {1{`RANDOM}};
  r_pte_x = _RAND_13[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_14 = {1{`RANDOM}};
  r_pte_w = _RAND_14[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_15 = {1{`RANDOM}};
  r_pte_r = _RAND_15[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_16 = {1{`RANDOM}};
  r_pte_v = _RAND_16[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_17 = {1{`RANDOM}};
  mem_resp_valid = _RAND_17[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_18 = {1{`RANDOM}};
  mem_resp_data = _RAND_18[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_19 = {1{`RANDOM}};
  _T_42 = _RAND_19[2:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_20 = {1{`RANDOM}};
  valid = _RAND_20[3:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_21 = {1{`RANDOM}};
  tags_0 = _RAND_21[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_22 = {1{`RANDOM}};
  tags_1 = _RAND_22[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_23 = {1{`RANDOM}};
  tags_2 = _RAND_23[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_24 = {1{`RANDOM}};
  tags_3 = _RAND_24[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_25 = {1{`RANDOM}};
  data_0 = _RAND_25[19:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_26 = {1{`RANDOM}};
  data_1 = _RAND_26[19:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_27 = {1{`RANDOM}};
  data_2 = _RAND_27[19:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_28 = {1{`RANDOM}};
  data_3 = _RAND_28[19:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end
  always @(posedge clock) begin
    if (reset) begin
      state <= 3'h0;
    end else begin
      state <= _2_io_y;
    end
    if (mem_resp_valid) begin
      if (traverse) begin
        if (_T_752) begin
          resp_valid_0 <= 1'h0;
        end else begin
          if (_T_757) begin
            resp_valid_0 <= 1'h0;
          end else begin
            if (_T_761) begin
              resp_valid_0 <= 1'h0;
            end else begin
              if (_T_763) begin
                resp_valid_0 <= _GEN_30;
              end else begin
                resp_valid_0 <= _GEN_37;
              end
            end
          end
        end
      end else begin
        resp_valid_0 <= _GEN_66;
      end
    end else begin
      if (_T_752) begin
        resp_valid_0 <= 1'h0;
      end else begin
        if (_T_757) begin
          resp_valid_0 <= 1'h0;
        end else begin
          if (_T_761) begin
            resp_valid_0 <= 1'h0;
          end else begin
            if (_T_763) begin
              resp_valid_0 <= _GEN_30;
            end else begin
              resp_valid_0 <= _GEN_37;
            end
          end
        end
      end
    end
    if (mem_resp_valid) begin
      if (traverse) begin
        if (_T_752) begin
          resp_valid_1 <= 1'h0;
        end else begin
          if (_T_757) begin
            resp_valid_1 <= 1'h0;
          end else begin
            if (_T_761) begin
              resp_valid_1 <= 1'h0;
            end else begin
              if (_T_763) begin
                resp_valid_1 <= _GEN_31;
              end else begin
                resp_valid_1 <= _GEN_38;
              end
            end
          end
        end
      end else begin
        resp_valid_1 <= _GEN_67;
      end
    end else begin
      if (_T_752) begin
        resp_valid_1 <= 1'h0;
      end else begin
        if (_T_757) begin
          resp_valid_1 <= 1'h0;
        end else begin
          if (_T_761) begin
            resp_valid_1 <= 1'h0;
          end else begin
            if (_T_763) begin
              resp_valid_1 <= _GEN_31;
            end else begin
              resp_valid_1 <= _GEN_38;
            end
          end
        end
      end
    end
    invalidated <= io_dpath_sfence_valid | _T_129;
    if (mem_resp_valid) begin
      if (traverse) begin
        count <= _T_759;
      end else begin
        if (_T_752) begin
          count <= _T_756;
        end else begin
          if (_T_757) begin
            if (pte_cache_hit) begin
              count <= _T_759;
            end
          end else begin
            if (!(_T_761)) begin
              if (!(_T_763)) begin
                if (_T_766) begin
                  count <= _GEN_34;
                end
              end
            end
          end
        end
      end
    end else begin
      if (_T_752) begin
        count <= _T_756;
      end else begin
        if (_T_757) begin
          if (pte_cache_hit) begin
            count <= _T_759;
          end
        end else begin
          if (!(_T_761)) begin
            if (!(_T_763)) begin
              if (_T_766) begin
                count <= _GEN_34;
              end
            end
          end
        end
      end
    end
    if (mem_resp_valid) begin
      if (traverse) begin
        if (_T_752) begin
          resp_ae <= 1'h0;
        end else begin
          if (_T_757) begin
            resp_ae <= 1'h0;
          end else begin
            if (_T_761) begin
              resp_ae <= 1'h0;
            end else begin
              resp_ae <= _GEN_43;
            end
          end
        end
      end else begin
        resp_ae <= ae;
      end
    end else begin
      if (_T_752) begin
        resp_ae <= 1'h0;
      end else begin
        if (_T_757) begin
          resp_ae <= 1'h0;
        end else begin
          if (_T_761) begin
            resp_ae <= 1'h0;
          end else begin
            resp_ae <= _GEN_43;
          end
        end
      end
    end
    if (_T_41) begin
      r_req_addr <= arb_io_out_bits_bits_addr;
    end
    if (_T_41) begin
      r_req_dest <= arb_io_chosen;
    end
    r_pte_ppn <= _2_1_io_y_ppn;
    r_pte_d <= _2_1_io_y_d;
    r_pte_a <= _2_1_io_y_a;
    r_pte_g <= _2_1_io_y_g;
    r_pte_u <= _2_1_io_y_u;
    r_pte_x <= _2_1_io_y_x;
    r_pte_w <= _2_1_io_y_w;
    r_pte_r <= _2_1_io_y_r;
    r_pte_v <= _2_1_io_y_v;
    mem_resp_valid <= io_mem_resp_valid;
    mem_resp_data <= io_mem_resp_bits_data;
    if (_T_83) begin
      _T_42 <= _T_109;
    end
    if (reset) begin
      valid <= 4'h0;
    end else begin
      if (_T_111) begin
        valid <= 4'h0;
      end else begin
        if (_T_54) begin
          valid <= _T_81;
        end
      end
    end
    if (_T_54) begin
      if (2'h0 == r) begin
        tags_0 <= _tags_r;
      end
    end
    if (_T_54) begin
      if (2'h1 == r) begin
        tags_1 <= _tags_r;
      end
    end
    if (_T_54) begin
      if (2'h2 == r) begin
        tags_2 <= _tags_r;
      end
    end
    if (_T_54) begin
      if (2'h3 == r) begin
        tags_3 <= _tags_r;
      end
    end
    if (_T_54) begin
      if (2'h0 == r) begin
        data_0 <= _data_r;
      end
    end
    if (_T_54) begin
      if (2'h1 == r) begin
        data_1 <= _data_r;
      end
    end
    if (_T_54) begin
      if (2'h2 == r) begin
        data_2 <= _data_r;
      end
    end
    if (_T_54) begin
      if (2'h3 == r) begin
        data_3 <= _data_r;
      end
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (mem_resp_valid & _T_796) begin
          $fwrite(32'h80000002,"Assertion failed\n    at PTW.scala:342 assert(state === s_wait3)\n"); // @[PTW.scala 342:11:freechips.rocketchip.system.DefaultRV32Config.fir@146063.8]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (mem_resp_valid & _T_796) begin
          $fatal; // @[PTW.scala 342:11:freechips.rocketchip.system.DefaultRV32Config.fir@146064.8]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (io_mem_s2_nack & _T_812) begin
          $fwrite(32'h80000002,"Assertion failed\n    at PTW.scala:359 assert(state === s_wait2)\n"); // @[PTW.scala 359:11:freechips.rocketchip.system.DefaultRV32Config.fir@146101.8]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (io_mem_s2_nack & _T_812) begin
          $fatal; // @[PTW.scala 359:11:freechips.rocketchip.system.DefaultRV32Config.fir@146102.8]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
  end
endmodule

module RRArbiter( // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144989.2]
  input         clock, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144990.4]
  output        io_in_0_ready, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  input         io_in_0_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  input  [19:0] io_in_0_bits_bits_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  output        io_in_1_ready, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  input         io_in_1_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  input         io_in_1_bits_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  input  [19:0] io_in_1_bits_bits_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  input         io_out_ready, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  output        io_out_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  output        io_out_bits_valid, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  output [19:0] io_out_bits_bits_addr, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
  output        io_chosen // @[:freechips.rocketchip.system.DefaultRV32Config.fir@144992.4]
);
  wire  _T; // @[Decoupled.scala 40:37:freechips.rocketchip.system.DefaultRV32Config.fir@145000.4]
  reg  _T_1; // @[Reg.scala 15:16:freechips.rocketchip.system.DefaultRV32Config.fir@145001.4]
  reg [31:0] _RAND_0;
  wire  _T_3; // @[Arbiter.scala 67:57:freechips.rocketchip.system.DefaultRV32Config.fir@145006.4]
  wire  _T_5; // @[Arbiter.scala 68:83:freechips.rocketchip.system.DefaultRV32Config.fir@145008.4]
  wire  _T_7; // @[Arbiter.scala 31:68:freechips.rocketchip.system.DefaultRV32Config.fir@145010.4]
  wire  _T_9; // @[Arbiter.scala 31:78:freechips.rocketchip.system.DefaultRV32Config.fir@145012.4]
  wire  _T_10; // @[Arbiter.scala 31:78:freechips.rocketchip.system.DefaultRV32Config.fir@145013.4]
  wire  _T_14; // @[Arbiter.scala 72:50:freechips.rocketchip.system.DefaultRV32Config.fir@145017.4]
  wire  _GEN_9; // @[Arbiter.scala 77:27:freechips.rocketchip.system.DefaultRV32Config.fir@145022.4]
  assign _T = io_out_ready & io_out_valid; // @[Decoupled.scala 40:37:freechips.rocketchip.system.DefaultRV32Config.fir@145000.4]
  assign _T_3 = 1'h1 > _T_1; // @[Arbiter.scala 67:57:freechips.rocketchip.system.DefaultRV32Config.fir@145006.4]
  assign _T_5 = io_in_1_valid & _T_3; // @[Arbiter.scala 68:83:freechips.rocketchip.system.DefaultRV32Config.fir@145008.4]
  assign _T_7 = _T_5 | io_in_0_valid; // @[Arbiter.scala 31:68:freechips.rocketchip.system.DefaultRV32Config.fir@145010.4]
  assign _T_9 = _T_5 == 1'h0; // @[Arbiter.scala 31:78:freechips.rocketchip.system.DefaultRV32Config.fir@145012.4]
  assign _T_10 = _T_7 == 1'h0; // @[Arbiter.scala 31:78:freechips.rocketchip.system.DefaultRV32Config.fir@145013.4]
  assign _T_14 = _T_3 | _T_10; // @[Arbiter.scala 72:50:freechips.rocketchip.system.DefaultRV32Config.fir@145017.4]
  assign _GEN_9 = io_in_0_valid ? 1'h0 : 1'h1; // @[Arbiter.scala 77:27:freechips.rocketchip.system.DefaultRV32Config.fir@145022.4]
  assign io_in_0_ready = _T_9 & io_out_ready; // @[Arbiter.scala 60:16:freechips.rocketchip.system.DefaultRV32Config.fir@145019.4]
  assign io_in_1_ready = _T_14 & io_out_ready; // @[Arbiter.scala 60:16:freechips.rocketchip.system.DefaultRV32Config.fir@145021.4]
  assign io_out_valid = io_chosen ? io_in_1_valid : io_in_0_valid; // @[Arbiter.scala 41:16:freechips.rocketchip.system.DefaultRV32Config.fir@144997.4]
  assign io_out_bits_valid = io_chosen ? io_in_1_bits_valid : 1'h1; // @[Arbiter.scala 42:15:freechips.rocketchip.system.DefaultRV32Config.fir@144999.4]
  assign io_out_bits_bits_addr = io_chosen ? io_in_1_bits_bits_addr : io_in_0_bits_bits_addr; // @[Arbiter.scala 42:15:freechips.rocketchip.system.DefaultRV32Config.fir@144998.4]
  assign io_chosen = _T_5 | _GEN_9; // @[Arbiter.scala 40:13:freechips.rocketchip.system.DefaultRV32Config.fir@144996.4]
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
  _T_1 = _RAND_0[0:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end
  always @(posedge clock) begin
    if (_T) begin
      _T_1 <= io_chosen;
    end
  end
endmodule
module _2_79( // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145029.2]
  input  [2:0] io_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145032.4]
  output [2:0] io_y // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145032.4]
);
  assign io_y = io_x; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145037.4]
endmodule
module _2_80( // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145039.2]
  input  [53:0] io_x_ppn, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_d, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_g, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_u, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  input         io_x_v, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output [53:0] io_y_ppn, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_d, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_a, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_g, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_u, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_x, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_w, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_r, // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
  output        io_y_v // @[:freechips.rocketchip.system.DefaultRV32Config.fir@145042.4]
);
  assign io_y_ppn = io_x_ppn; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_d = io_x_d; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_a = io_x_a; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_g = io_x_g; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_u = io_x_u; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_x = io_x_x; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_w = io_x_w; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_r = io_x_r; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
  assign io_y_v = io_x_v; // @[package.scala 218:12:freechips.rocketchip.system.DefaultRV32Config.fir@145047.4]
endmodule
