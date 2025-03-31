// ******************************************** //
// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //
// *** Desrp : UVM TB Europa NOC            *** //
// ******************************************** //

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ps;

  `include "../uvm/enoc_tb_macros.svh"
  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;
  import enoc_uvm_pkg::*;
  // Axi Checkers
  `include "axi4pc/bind_axi_europa_noc.svh"
  // Axi Performance tracker
  `include "axi_perf_tracker/bind_axi_europa_noc.svh"

  // CLK & RST declaration
  bit clk_1_2GHz;
  bit clk_800MHz;
  bit clk_600MHz;
  bit clk_100MHz;
  bit clk_50MHz;
  bit enoc_clk, enoc_rst_n, rst_n;
  realtime CLK_PERIOD_1200  = 0.83ns;   // 1200MHz  --> 0.83ns
  realtime CLK_PERIOD_800   = 1.25ns;   // 800MHz   --> 1.25ns
  realtime CLK_PERIOD_600   = 1.66ns;   // 600MHz   --> 1.66ns
  realtime CLK_PERIOD_100   = 10ns;     // 100Mhz   --> slow_clk
  realtime CLK_PERIOD_50    = 20ns;     // 50Mhz   --> ref_clk
  // TB Interface instance
  enoc_tb_intf  tb_intf();
  // VIP Interface instance
  svt_axi_if          axi_if();
  axi_reset_if        axi_reset_if();
  svt_apb_if          apb_if[`NUM_APB3_TARGETS + `NUM_APB4_TARGETS]();

  //Misc signals
  bit test_mode                         ;
  bit scan_en                           ;
  bit o_irq;
  bit[15:0] o_obs;
  logic [sdma_pkg::NUM_CHNLS-1:0] o_sdma_0_int;
  logic [sdma_pkg::NUM_CHNLS-1:0] o_sdma_1_int;
  bit i_sdma_inter_core_sync            ;
  bit i_sdma_0_clock_throttle           ;
  bit i_sdma_1_clock_throttle           ;
  bit i_aic_0_clken                     ;
  bit i_aic_1_clken                     ;
  bit i_aic_2_clken                     ;
  bit i_aic_3_clken                     ;
  bit i_aic_4_clken                     ;
  bit i_aic_5_clken                     ;
  bit i_aic_6_clken                     ;
  bit i_aic_7_clken                     ;
  bit i_apu_x_clken                     ;
  bit i_dcd_codec_clken                 ;
  bit i_dcd_mcu_clken                   ;
  bit i_l2_0_clken                      ;
  bit i_l2_1_clken                      ;
  bit i_l2_2_clken                      ;
  bit i_l2_3_clken                      ;
  bit i_l2_4_clken                      ;
  bit i_l2_5_clken                      ;
  bit i_l2_6_clken                      ;
  bit i_l2_7_clken                      ;
  bit i_lpddr_graph_0_clken             ;
  bit i_lpddr_graph_1_clken             ;
  bit i_lpddr_graph_2_clken             ;
  bit i_lpddr_graph_3_clken             ;
  bit i_lpddr_ppp_0_clken               ;
  bit i_lpddr_ppp_1_clken               ;
  bit i_lpddr_ppp_2_clken               ;
  bit i_lpddr_ppp_3_clken               ;
  bit i_pcie_init_mt_clken              ;
  bit i_pcie_targ_mt_clken              ;
  bit i_pcie_targ_cfg_clken             ;
  bit i_pcie_targ_cfg_dbi_clken         ;
  bit i_pve_0_clken                     ;
  bit i_pve_1_clken                     ;
  bit i_soc_mgmt_clken                  ;
  bit i_soc_periph_clken                ;
  bit i_sys_spm_clken                   ;
  bit i_l2_addr_mode_port_b0;
  bit i_l2_addr_mode_port_b1;
  bit i_l2_intr_mode_port_b0;
  bit i_l2_intr_mode_port_b1;
  bit i_lpddr_graph_addr_mode_port_b0;
  bit i_lpddr_graph_addr_mode_port_b1;
  bit i_lpddr_graph_intr_mode_port_b0;
  bit i_lpddr_graph_intr_mode_port_b1;
  bit i_lpddr_ppp_addr_mode_port_b0;
  bit i_lpddr_ppp_addr_mode_port_b1;
  bit i_lpddr_ppp_intr_mode_port_b0;
  bit i_lpddr_ppp_intr_mode_port_b1;
  bit o_aic_0_pwr_idle_val              ;
  bit o_aic_0_pwr_idle_ack              ;
  bit i_aic_0_pwr_idle_req              ;
  bit o_aic_1_pwr_idle_val              ;
  bit o_aic_1_pwr_idle_ack              ;
  bit i_aic_1_pwr_idle_req              ;
  bit o_aic_2_pwr_idle_val              ;
  bit o_aic_2_pwr_idle_ack              ;
  bit i_aic_2_pwr_idle_req              ;
  bit o_aic_3_pwr_idle_val              ;
  bit o_aic_3_pwr_idle_ack              ;
  bit i_aic_3_pwr_idle_req              ;
  bit o_aic_4_pwr_idle_val              ;
  bit o_aic_4_pwr_idle_ack              ;
  bit i_aic_4_pwr_idle_req              ;
  bit o_aic_5_pwr_idle_val              ;
  bit o_aic_5_pwr_idle_ack              ;
  bit i_aic_5_pwr_idle_req              ;
  bit o_aic_6_pwr_idle_val              ;
  bit o_aic_6_pwr_idle_ack              ;
  bit i_aic_6_pwr_idle_req              ;
  bit o_aic_7_pwr_idle_val              ;
  bit o_aic_7_pwr_idle_ack              ;
  bit i_aic_7_pwr_idle_req              ;
  bit o_apu_pwr_idle_val                ;
  bit o_apu_pwr_idle_ack                ;
  bit i_apu_pwr_idle_req                ;
  bit o_dcd_mcu_pwr_idle_val            ;
  bit o_dcd_mcu_pwr_idle_ack            ;
  bit i_dcd_mcu_pwr_idle_req            ;
  bit o_dcd_pwr_idle_val                ;
  bit o_dcd_pwr_idle_ack                ;
  bit i_dcd_pwr_idle_req                ;
  bit o_l2_0_pwr_idle_val               ;
  bit o_l2_0_pwr_idle_ack               ;
  bit i_l2_0_pwr_idle_req               ;
  bit o_l2_1_pwr_idle_val               ;
  bit o_l2_1_pwr_idle_ack               ;
  bit i_l2_1_pwr_idle_req               ;
  bit o_l2_2_pwr_idle_val               ;
  bit o_l2_2_pwr_idle_ack               ;
  bit i_l2_2_pwr_idle_req               ;
  bit o_l2_3_pwr_idle_val               ;
  bit o_l2_3_pwr_idle_ack               ;
  bit i_l2_3_pwr_idle_req               ;
  bit o_l2_4_pwr_idle_val               ;
  bit o_l2_4_pwr_idle_ack               ;
  bit i_l2_4_pwr_idle_req               ;
  bit o_l2_5_pwr_idle_val               ;
  bit o_l2_5_pwr_idle_ack               ;
  bit i_l2_5_pwr_idle_req               ;
  bit o_l2_6_pwr_idle_val               ;
  bit o_l2_6_pwr_idle_ack               ;
  bit i_l2_6_pwr_idle_req               ;
  bit o_l2_7_pwr_idle_val               ;
  bit o_l2_7_pwr_idle_ack               ;
  bit i_l2_7_pwr_idle_req               ;
  bit[1:0] o_lpddr_graph_0_pwr_idle_vec_val  ;
  bit[1:0] o_lpddr_graph_0_pwr_idle_vec_ack  ;
  bit[1:0] i_lpddr_graph_0_pwr_idle_vec_req  ;
  bit[1:0] o_lpddr_graph_1_pwr_idle_vec_val  ;
  bit[1:0] o_lpddr_graph_1_pwr_idle_vec_ack  ;
  bit[1:0] i_lpddr_graph_1_pwr_idle_vec_req  ;
  bit[1:0] o_lpddr_graph_2_pwr_idle_vec_val  ;
  bit[1:0] o_lpddr_graph_2_pwr_idle_vec_ack  ;
  bit[1:0] i_lpddr_graph_2_pwr_idle_vec_req  ;
  bit[1:0] o_lpddr_graph_3_pwr_idle_vec_val  ;
  bit[1:0] o_lpddr_graph_3_pwr_idle_vec_ack  ;
  bit[1:0] i_lpddr_graph_3_pwr_idle_vec_req  ;
  bit[1:0] o_lpddr_ppp_0_pwr_idle_vec_val    ;
  bit[1:0] o_lpddr_ppp_0_pwr_idle_vec_ack    ;
  bit[1:0] i_lpddr_ppp_0_pwr_idle_vec_req    ;
  bit[1:0] o_lpddr_ppp_1_pwr_idle_vec_val    ;
  bit[1:0] o_lpddr_ppp_1_pwr_idle_vec_ack    ;
  bit[1:0] i_lpddr_ppp_1_pwr_idle_vec_req    ;
  bit[1:0] o_lpddr_ppp_2_pwr_idle_vec_val    ;
  bit[1:0] o_lpddr_ppp_2_pwr_idle_vec_ack    ;
  bit[1:0] i_lpddr_ppp_2_pwr_idle_vec_req    ;
  bit[1:0] o_lpddr_ppp_3_pwr_idle_vec_val    ;
  bit[1:0] o_lpddr_ppp_3_pwr_idle_vec_ack    ;
  bit[1:0] i_lpddr_ppp_3_pwr_idle_vec_req    ;
  bit o_pve_0_pwr_idle_val              ;
  bit o_pve_0_pwr_idle_ack              ;
  bit i_pve_0_pwr_idle_req              ;
  bit o_pve_1_pwr_idle_val              ;
  bit o_pve_1_pwr_idle_ack              ;
  bit i_pve_1_pwr_idle_req              ;
  bit o_soc_mgmt_pwr_idle_val           ;
  bit o_soc_mgmt_pwr_idle_ack           ;
  bit i_soc_mgmt_pwr_idle_req           ;
  bit o_soc_periph_pwr_idle_val         ;
  bit o_soc_periph_pwr_idle_ack         ;
  bit i_soc_periph_pwr_idle_req         ;
  bit o_sys_spm_pwr_idle_val            ;
  bit o_sys_spm_pwr_idle_ack            ;
  bit i_sys_spm_pwr_idle_req            ;
  bit o_pcie_init_mt_pwr_idle_val            ;
  bit o_pcie_init_mt_pwr_idle_ack            ;
  bit i_pcie_init_mt_pwr_idle_req            ;
  bit o_pcie_targ_mt_pwr_idle_val            ;
  bit o_pcie_targ_mt_pwr_idle_ack            ;
  bit i_pcie_targ_mt_pwr_idle_req            ;
  bit o_pcie_targ_cfg_pwr_idle_val            ;
  bit o_pcie_targ_cfg_pwr_idle_ack            ;
  bit i_pcie_targ_cfg_pwr_idle_req            ;
  bit o_pcie_targ_cfg_dbi_pwr_idle_val            ;
  bit o_pcie_targ_cfg_dbi_pwr_idle_ack            ;
  bit i_pcie_targ_cfg_dbi_pwr_idle_req            ;
  bit o_aic_0_pwr_tok_idle_val          ;
  bit o_aic_0_pwr_tok_idle_ack          ;
  bit i_aic_0_pwr_tok_idle_req          ;
  bit o_aic_1_pwr_tok_idle_val          ;
  bit o_aic_1_pwr_tok_idle_ack          ;
  bit i_aic_1_pwr_tok_idle_req          ;
  bit o_aic_2_pwr_tok_idle_val          ;
  bit o_aic_2_pwr_tok_idle_ack          ;
  bit i_aic_2_pwr_tok_idle_req          ;
  bit o_aic_3_pwr_tok_idle_val          ;
  bit o_aic_3_pwr_tok_idle_ack          ;
  bit i_aic_3_pwr_tok_idle_req          ;
  bit o_aic_4_pwr_tok_idle_val          ;
  bit o_aic_4_pwr_tok_idle_ack          ;
  bit i_aic_4_pwr_tok_idle_req          ;
  bit o_aic_5_pwr_tok_idle_val          ;
  bit o_aic_5_pwr_tok_idle_ack          ;
  bit i_aic_5_pwr_tok_idle_req          ;
  bit o_aic_6_pwr_tok_idle_val          ;
  bit o_aic_6_pwr_tok_idle_ack          ;
  bit i_aic_6_pwr_tok_idle_req          ;
  bit o_aic_7_pwr_tok_idle_val          ;
  bit o_aic_7_pwr_tok_idle_ack          ;
  bit i_aic_7_pwr_tok_idle_req          ;
  bit o_apu_pwr_tok_idle_val            ;
  bit o_apu_pwr_tok_idle_ack            ;
  bit i_apu_pwr_tok_idle_req            ;

  // =============================================================================================================
  // CLK connection from VIP <-> RTL
  // ARGS - (rtl_signal_name, vip_intf)
  // =============================================================================================================
  `create_and_bind_clk(i_ref                , axi_if.master_if[e_sdma_0_init_lt])
  `create_and_bind_clk(i_sdma_0             , axi_if.master_if[e_sdma_0_init_lt])
  `create_and_bind_clk(i_sdma_1             , axi_if.master_if[e_sdma_1_init_lt])
  `create_and_bind_clk(i_aic_0              , axi_if.master_if[e_aic_0_init_lt])
  `create_and_bind_clk(i_aic_1              , axi_if.master_if[e_aic_1_init_lt])
  `create_and_bind_clk(i_aic_2              , axi_if.master_if[e_aic_2_init_lt])
  `create_and_bind_clk(i_aic_3              , axi_if.master_if[e_aic_3_init_lt])
  `create_and_bind_clk(i_aic_4              , axi_if.master_if[e_aic_4_init_lt])
  `create_and_bind_clk(i_aic_5              , axi_if.master_if[e_aic_5_init_lt])
  `create_and_bind_clk(i_aic_6              , axi_if.master_if[e_aic_6_init_lt])
  `create_and_bind_clk(i_aic_7              , axi_if.master_if[e_aic_7_init_lt])
  `create_and_bind_clk(i_apu_x              , axi_if.master_if[e_apu_init_lt])
  `create_and_bind_clk(i_dcd_codec          , axi_if.master_if[e_dcd_dec_0_init_mt])
  `create_and_bind_clk(i_dcd_mcu            , axi_if.master_if[e_dcd_mcu_init_lt])
  `create_and_bind_clk(i_noc                , axi_if.master_if[e_aic_0_init_ht])
  `create_and_bind_clk(i_pcie_init_mt       , axi_if.master_if[e_pcie_init_mt])
  `create_and_bind_clk(i_pve_0              , axi_if.master_if[e_pve_0_init_lt])
  `create_and_bind_clk(i_pve_1              , axi_if.master_if[e_pve_1_init_lt])
  `create_and_bind_clk(i_soc_mgmt           , axi_if.master_if[e_soc_mgmt_init_lt])
  `create_and_bind_clk(i_soc_periph         , axi_if.master_if[e_soc_periph_init_lt])
  `create_and_bind_clk(i_pcie_targ_mt       , axi_if.slave_if[e_pcie_targ_mt])
  `create_and_bind_clk(i_pcie_targ_cfg      , axi_if.slave_if[e_pcie_targ_cfg])
  `create_and_bind_clk(i_pcie_targ_cfg_dbi  , axi_if.slave_if[e_pcie_targ_cfg_dbi])
  `create_and_bind_clk(i_l2_0               , axi_if.slave_if[e_l2_0_targ_ht])
  `create_and_bind_clk(i_l2_1               , axi_if.slave_if[e_l2_1_targ_ht])
  `create_and_bind_clk(i_l2_2               , axi_if.slave_if[e_l2_2_targ_ht])
  `create_and_bind_clk(i_l2_3               , axi_if.slave_if[e_l2_3_targ_ht])
  `create_and_bind_clk(i_l2_4               , axi_if.slave_if[e_l2_4_targ_ht])
  `create_and_bind_clk(i_l2_5               , axi_if.slave_if[e_l2_5_targ_ht])
  `create_and_bind_clk(i_l2_6               , axi_if.slave_if[e_l2_6_targ_ht])
  `create_and_bind_clk(i_l2_7               , axi_if.slave_if[e_l2_7_targ_ht])
  `create_and_bind_clk(i_lpddr_graph_0      , axi_if.slave_if[e_lpddr_graph_0_targ_ht])
  `create_and_bind_clk(i_lpddr_graph_1      , axi_if.slave_if[e_lpddr_graph_1_targ_ht])
  `create_and_bind_clk(i_lpddr_graph_2      , axi_if.slave_if[e_lpddr_graph_2_targ_ht])
  `create_and_bind_clk(i_lpddr_graph_3      , axi_if.slave_if[e_lpddr_graph_3_targ_ht])
  `create_and_bind_clk(i_lpddr_ppp_0        , axi_if.slave_if[e_lpddr_ppp_0_targ_mt])
  `create_and_bind_clk(i_lpddr_ppp_1        , axi_if.slave_if[e_lpddr_ppp_1_targ_mt])
  `create_and_bind_clk(i_lpddr_ppp_2        , axi_if.slave_if[e_lpddr_ppp_2_targ_mt])
  `create_and_bind_clk(i_lpddr_ppp_3        , axi_if.slave_if[e_lpddr_ppp_3_targ_mt])
  `create_and_bind_clk(i_sys_spm            , axi_if.slave_if[e_sys_spm_targ_lt])


  // =============================================================================================================
  // RST connection from VIP <-> RTL
  // ARGS - (rtl_signal_name, vip_intf) //TODO: exercise asyn_rst
  // =============================================================================================================
  bit i_sdma_0_ao_rst_n;
  bit i_sdma_1_ao_rst_n;
  bit i_sdma_0_global_rst_n;
  bit i_sdma_1_global_rst_n;
  assign  i_sdma_0_ao_rst_n        = axi_if.master_if[e_sdma_0_init_lt].aresetn;
  assign  i_sdma_1_ao_rst_n        = axi_if.master_if[e_sdma_1_init_lt].aresetn;
  assign  i_sdma_0_global_rst_n    = axi_if.master_if[e_sdma_0_init_lt].aresetn;
  assign  i_sdma_1_global_rst_n    = axi_if.master_if[e_sdma_1_init_lt].aresetn;

  `create_and_bind_rst(i_aic_0          , axi_if.master_if[e_aic_0_init_lt])
  `create_and_bind_rst(i_aic_1          , axi_if.master_if[e_aic_1_init_lt])
  `create_and_bind_rst(i_aic_2          , axi_if.master_if[e_aic_2_init_lt])
  `create_and_bind_rst(i_aic_3          , axi_if.master_if[e_aic_3_init_lt])
  `create_and_bind_rst(i_aic_4          , axi_if.master_if[e_aic_4_init_lt])
  `create_and_bind_rst(i_aic_5          , axi_if.master_if[e_aic_5_init_lt])
  `create_and_bind_rst(i_aic_6          , axi_if.master_if[e_aic_6_init_lt])
  `create_and_bind_rst(i_aic_7          , axi_if.master_if[e_aic_7_init_lt])
  `create_and_bind_rst(i_apu_x          , axi_if.master_if[e_apu_init_lt])
  `create_and_bind_rst(i_dcd_mcu        , axi_if.master_if[e_dcd_mcu_init_lt])
  `create_and_bind_rst(i_dcd_codec      , axi_if.master_if[e_dcd_dec_0_init_mt])
  `create_and_bind_rst(i_noc            , axi_if.master_if[e_aic_0_init_ht])
  `create_and_bind_rst(i_pcie_init_mt      , axi_if.master_if[e_pcie_init_mt])
  `create_and_bind_rst(i_pcie_targ_mt      , axi_if.master_if[e_pcie_targ_mt])
  `create_and_bind_rst(i_pcie_targ_cfg      , axi_if.master_if[e_pcie_targ_cfg])
  `create_and_bind_rst(i_pcie_targ_cfg_dbi      , axi_if.master_if[e_pcie_targ_cfg_dbi])
  `create_and_bind_rst(i_pve_0          , axi_if.master_if[e_pve_0_init_lt])
  `create_and_bind_rst(i_pve_1          , axi_if.master_if[e_pve_1_init_lt])
  `create_and_bind_rst(i_soc_mgmt       , axi_if.master_if[e_soc_mgmt_init_lt])
  `create_and_bind_rst(i_soc_periph     , axi_if.master_if[e_soc_periph_init_lt])
  `create_and_bind_rst(i_l2_0           , axi_if.slave_if[e_l2_0_targ_ht])
  `create_and_bind_rst(i_l2_1           , axi_if.slave_if[e_l2_1_targ_ht])
  `create_and_bind_rst(i_l2_2           , axi_if.slave_if[e_l2_2_targ_ht])
  `create_and_bind_rst(i_l2_3           , axi_if.slave_if[e_l2_3_targ_ht])
  `create_and_bind_rst(i_l2_4           , axi_if.slave_if[e_l2_4_targ_ht])
  `create_and_bind_rst(i_l2_5           , axi_if.slave_if[e_l2_5_targ_ht])
  `create_and_bind_rst(i_l2_6           , axi_if.slave_if[e_l2_6_targ_ht])
  `create_and_bind_rst(i_l2_7           , axi_if.slave_if[e_l2_7_targ_ht])
  `create_and_bind_rst(i_lpddr_graph_0  , axi_if.slave_if[e_lpddr_graph_0_targ_ht])
  `create_and_bind_rst(i_lpddr_graph_1  , axi_if.slave_if[e_lpddr_graph_1_targ_ht])
  `create_and_bind_rst(i_lpddr_graph_2  , axi_if.slave_if[e_lpddr_graph_2_targ_ht])
  `create_and_bind_rst(i_lpddr_graph_3  , axi_if.slave_if[e_lpddr_graph_3_targ_ht])
  `create_and_bind_rst(i_lpddr_ppp_0    , axi_if.slave_if[e_lpddr_ppp_0_targ_mt])
  `create_and_bind_rst(i_lpddr_ppp_1    , axi_if.slave_if[e_lpddr_ppp_1_targ_mt])
  `create_and_bind_rst(i_lpddr_ppp_2    , axi_if.slave_if[e_lpddr_ppp_2_targ_mt])
  `create_and_bind_rst(i_lpddr_ppp_3    , axi_if.slave_if[e_lpddr_ppp_3_targ_mt])
  `create_and_bind_rst(i_sys_spm        , axi_if.slave_if[e_sys_spm_targ_lt])

  // =============================================================================================================
  // Always-ON RST connection from VIP <-> RTL
  // ARGS - (rtl_signal_name, vip_intf)
  // =============================================================================================================
  `create_and_bind_aorst(i_aic_0         , axi_if.master_if[e_aic_0_init_lt])
  `create_and_bind_aorst(i_aic_1         , axi_if.master_if[e_aic_1_init_lt])
  `create_and_bind_aorst(i_aic_2         , axi_if.master_if[e_aic_2_init_lt])
  `create_and_bind_aorst(i_aic_3         , axi_if.master_if[e_aic_3_init_lt])
  `create_and_bind_aorst(i_aic_4         , axi_if.master_if[e_aic_4_init_lt])
  `create_and_bind_aorst(i_aic_5         , axi_if.master_if[e_aic_5_init_lt])
  `create_and_bind_aorst(i_aic_6         , axi_if.master_if[e_aic_6_init_lt])
  `create_and_bind_aorst(i_aic_7         , axi_if.master_if[e_aic_7_init_lt])
  `create_and_bind_aorst(i_apu           , axi_if.master_if[e_apu_init_lt])
  `create_and_bind_aorst(i_dcd           , axi_if.master_if[e_dcd_mcu_init_lt])
  `create_and_bind_aorst(i_pcie          , axi_if.master_if[e_pcie_init_mt])
  `create_and_bind_aorst(i_pve_0         , axi_if.master_if[e_pve_0_init_lt])
  `create_and_bind_aorst(i_pve_1         , axi_if.master_if[e_pve_1_init_lt])
  `create_and_bind_aorst(i_soc_mgmt      , axi_if.master_if[e_soc_mgmt_init_lt])
  `create_and_bind_aorst(i_soc_periph    , axi_if.master_if[e_soc_periph_init_lt])
  `create_and_bind_aorst(i_l2_0          , axi_if.slave_if[e_l2_0_targ_ht])
  `create_and_bind_aorst(i_l2_1          , axi_if.slave_if[e_l2_1_targ_ht])
  `create_and_bind_aorst(i_l2_2          , axi_if.slave_if[e_l2_2_targ_ht])
  `create_and_bind_aorst(i_l2_3          , axi_if.slave_if[e_l2_3_targ_ht])
  `create_and_bind_aorst(i_l2_4          , axi_if.slave_if[e_l2_4_targ_ht])
  `create_and_bind_aorst(i_l2_5          , axi_if.slave_if[e_l2_5_targ_ht])
  `create_and_bind_aorst(i_l2_6          , axi_if.slave_if[e_l2_6_targ_ht])
  `create_and_bind_aorst(i_l2_7          , axi_if.slave_if[e_l2_7_targ_ht])
  // TODO(srinivas/psarras; do this properly)
  bit i_ddr_wpll_aon_rst_n;
  assign i_ddr_wpll_aon_rst_n = rst_n;
  `create_and_bind_aorst(i_lpddr_graph_0 , axi_if.slave_if[e_lpddr_graph_0_targ_ht])
  `create_and_bind_aorst(i_lpddr_graph_1 , axi_if.slave_if[e_lpddr_graph_1_targ_ht])
  `create_and_bind_aorst(i_lpddr_graph_2 , axi_if.slave_if[e_lpddr_graph_2_targ_ht])
  `create_and_bind_aorst(i_lpddr_graph_3 , axi_if.slave_if[e_lpddr_graph_3_targ_ht])
  `create_and_bind_aorst(i_lpddr_ppp_0   , axi_if.slave_if[e_lpddr_ppp_0_targ_mt])
  `create_and_bind_aorst(i_lpddr_ppp_1   , axi_if.slave_if[e_lpddr_ppp_1_targ_mt])
  `create_and_bind_aorst(i_lpddr_ppp_2   , axi_if.slave_if[e_lpddr_ppp_2_targ_mt])
  `create_and_bind_aorst(i_lpddr_ppp_3   , axi_if.slave_if[e_lpddr_ppp_3_targ_mt])
  `create_and_bind_aorst(i_sys_spm       , axi_if.slave_if[e_sys_spm_targ_lt])

  // =============================================================================================================
  // OCP connection from INTF <-> RTL
  // ARGS - (rtl_signal_name, tb_intf)
  // =============================================================================================================
  `create_and_bind_ocp(aic_0 , tb_intf)
  `create_and_bind_ocp(aic_1 , tb_intf)
  `create_and_bind_ocp(aic_2 , tb_intf)
  `create_and_bind_ocp(aic_3 , tb_intf)
  `create_and_bind_ocp(aic_4 , tb_intf)
  `create_and_bind_ocp(aic_5 , tb_intf)
  `create_and_bind_ocp(aic_6 , tb_intf)
  `create_and_bind_ocp(aic_7 , tb_intf)
  `create_and_bind_ocp(apu   , tb_intf)

  // =============================================================================================================
  // RTL <-> MVIP connections
  // ARGS - (is_master, rtl_signal_name, addr_w, data_w, id_w, len_w, vip_intf)
  // =============================================================================================================
  //TODO: Check pcie_init_mt AxLen width which is 4bits
  // X8 AIC_HT //
  `create_and_bind_axi_mst  ( aic_0_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_0_init_ht] )
  `create_and_bind_axi_mst  ( aic_1_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_1_init_ht] )
  `create_and_bind_axi_mst  ( aic_2_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_2_init_ht] )
  `create_and_bind_axi_mst  ( aic_3_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_3_init_ht] )
  `create_and_bind_axi_mst  ( aic_4_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_4_init_ht] )
  `create_and_bind_axi_mst  ( aic_5_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_5_init_ht] )
  `create_and_bind_axi_mst  ( aic_6_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_6_init_ht] )
  `create_and_bind_axi_mst  ( aic_7_init_ht   , 40, 512, 9, 8, axi_if.master_if[e_aic_7_init_ht] )
  // X8 AIC_LT //
  `create_and_bind_axi_mst  ( aic_0_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_0_init_lt] )
  `create_and_bind_axi_mst  ( aic_1_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_1_init_lt] )
  `create_and_bind_axi_mst  ( aic_2_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_2_init_lt] )
  `create_and_bind_axi_mst  ( aic_3_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_3_init_lt] )
  `create_and_bind_axi_mst  ( aic_4_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_4_init_lt] )
  `create_and_bind_axi_mst  ( aic_5_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_5_init_lt] )
  `create_and_bind_axi_mst  ( aic_6_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_6_init_lt] )
  `create_and_bind_axi_mst  ( aic_7_init_lt   , 40, 64 , 9, 8, axi_if.master_if[e_aic_7_init_lt] )
  // X6 SDMA_HT_LT //
  `create_and_bind_axi_mst  ( sdma_0_init_ht_0  , 40, 512, 8, 8, axi_if.master_if[e_sdma_0_init_ht_0] )
  `create_and_bind_axi_mst  ( sdma_0_init_ht_1  , 40, 512, 8, 8, axi_if.master_if[e_sdma_0_init_ht_1] )
  `create_and_bind_axi_mst  ( sdma_0_init_lt    , 40, 64 , 4, 8, axi_if.master_if[e_sdma_0_init_lt  ] )
  `create_and_bind_axi_mst  ( sdma_1_init_ht_0  , 40, 512, 8, 8, axi_if.master_if[e_sdma_1_init_ht_0] )
  `create_and_bind_axi_mst  ( sdma_1_init_ht_1  , 40, 512, 8, 8, axi_if.master_if[e_sdma_1_init_ht_1] )
  `create_and_bind_axi_mst  ( sdma_1_init_lt    , 40, 64 , 4, 8, axi_if.master_if[e_sdma_1_init_lt  ] )
  // X4 PVE_LT_HT //
  `create_and_bind_axi_mst  ( pve_0_init_lt    , 40, 64 , 8,  8, axi_if.master_if[e_pve_0_init_lt] )
  `create_and_bind_axi_mst  ( pve_0_init_ht    , 40, 512, 11, 8, axi_if.master_if[e_pve_0_init_ht] )
  `create_and_bind_axi_mst  ( pve_1_init_lt    , 40, 64 , 8,  8, axi_if.master_if[e_pve_1_init_lt] )
  `create_and_bind_axi_mst  ( pve_1_init_ht    , 40, 512, 11, 8, axi_if.master_if[e_pve_1_init_ht] )
  // X3 DCD_MT //
  `create_and_bind_axi_mst  ( dcd_dec_0_init_mt    , 40, 128, 5, 8, axi_if.master_if[e_dcd_dec_0_init_mt] )
  `create_and_bind_axi_mst  ( dcd_dec_1_init_mt    , 40, 128, 5, 8, axi_if.master_if[e_dcd_dec_1_init_mt] )
  `create_and_bind_axi_mst  ( dcd_dec_2_init_mt    , 40, 128, 5, 8, axi_if.master_if[e_dcd_dec_2_init_mt] )
  `create_and_bind_axi_mst  ( dcd_mcu_init_lt      , 40, 128, 5, 8, axi_if.master_if[e_dcd_mcu_init_lt  ] )
  // X2 APU_LT_MT //
  `create_and_bind_axi_mst  ( apu_init_lt  , 40, 64, 10, 8,  axi_if.master_if[e_apu_init_lt] )
  `create_and_bind_axi_mst  ( apu_init_mt  , 40, 256, 9, 8, axi_if.master_if[e_apu_init_mt] )
  // X1 PCIE_MT //
  `create_and_bind_axi_mst  ( pcie_init_mt    , 40, 128, 7, 8, axi_if.master_if[e_pcie_init_mt] )
  // X1 SOC_MGMT_LT  //
  `create_and_bind_axi_mst  ( soc_mgmt_init_lt  , 40, 64, 4, 8, axi_if.master_if[e_soc_mgmt_init_lt] )
  // X1 SOC_PERIPH_LT //
  `create_and_bind_axi_mst  ( soc_periph_init_lt  , 40, 64, 4, 8, axi_if.master_if[e_soc_periph_init_lt] )
  // =============================================================================================================
  // RTL <-> SVIP AXI connections (74??)
  // ARGS - (is_master, rtl_signal_name, addr_w, data_w, id_w, len_w, vip_intf)
  // =============================================================================================================
  // X8 AIC_LT //
  `create_and_bind_axi_slv  ( aic_0_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_0_targ_lt] )
  `create_and_bind_axi_slv  ( aic_1_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_1_targ_lt] )
  `create_and_bind_axi_slv  ( aic_2_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_2_targ_lt] )
  `create_and_bind_axi_slv  ( aic_3_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_3_targ_lt] )
  `create_and_bind_axi_slv  ( aic_4_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_4_targ_lt] )
  `create_and_bind_axi_slv  ( aic_5_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_5_targ_lt] )
  `create_and_bind_axi_slv  ( aic_6_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_6_targ_lt] )
  `create_and_bind_axi_slv  ( aic_7_targ_lt  , 40, 64, 6, 8, axi_if.slave_if[e_aic_7_targ_lt] )
  // X2 SDMA_LT
  `create_and_bind_axi_slv  ( sdma_0_targ_lt  , 40, 64, 4, 8, axi_if.slave_if[e_sdma_0_targ_lt] )
  `create_and_bind_axi_slv  ( sdma_1_targ_lt  , 40, 64, 4, 8, axi_if.slave_if[e_sdma_1_targ_lt] )
  // X2 PVE_LT //
  `create_and_bind_axi_slv  ( pve_0_targ_lt,  40, 64, 4, 8, axi_if.slave_if[e_pve_0_targ_lt] )
  `create_and_bind_axi_slv  ( pve_1_targ_lt,  40, 64, 4, 8, axi_if.slave_if[e_pve_1_targ_lt] )
  // X1 APU_LT
  `create_and_bind_axi_slv  ( apu_targ_lt,    40, 64, 8, 8, axi_if.slave_if[e_apu_targ_lt] )
  // X1 SOC_MGMT_LT
  `create_and_bind_axi_slv  ( soc_mgmt_targ_lt   , 40, 64, 4, 8, axi_if.slave_if[e_soc_mgmt_targ_lt] )
  // X1 SOC_PERIPH_LT
  `create_and_bind_axi_slv  ( soc_periph_targ_lt , 40, 64, 4, 8, axi_if.slave_if[e_soc_periph_targ_lt] )
  // X1 SYS_SPM_LT
  `create_and_bind_axi_slv  ( sys_spm_targ_lt    , 40, 64, 4, 8, axi_if.slave_if[e_sys_spm_targ_lt] )
  // X4 LPDDR_GRAPH_MT_slv
  `create_and_bind_axi_slv  ( lpddr_graph_0_targ_ht , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_graph_0_targ_ht] )
  `create_and_bind_axi_slv  ( lpddr_graph_1_targ_ht , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_graph_1_targ_ht] )
  `create_and_bind_axi_slv  ( lpddr_graph_2_targ_ht , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_graph_2_targ_ht] )
  `create_and_bind_axi_slv  ( lpddr_graph_3_targ_ht , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_graph_3_targ_ht] )
  // X2 PCIE_LT_MT // _slv
  `create_and_bind_axi_slv  ( pcie_targ_cfg_dbi , 40, 32,  4, 8, axi_if.slave_if[e_pcie_targ_cfg_dbi] )
  `create_and_bind_axi_slv  ( pcie_targ_mt , 40, 128, 6, 8, axi_if.slave_if[e_pcie_targ_mt] )
  // X8 L2_HT //
  `create_and_bind_axi_slv  ( l2_0_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_0_targ_ht] )
  `create_and_bind_axi_slv  ( l2_1_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_1_targ_ht] )
  `create_and_bind_axi_slv  ( l2_2_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_2_targ_ht] )
  `create_and_bind_axi_slv  ( l2_3_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_3_targ_ht] )
  `create_and_bind_axi_slv  ( l2_4_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_4_targ_ht] )
  `create_and_bind_axi_slv  ( l2_5_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_5_targ_ht] )
  `create_and_bind_axi_slv  ( l2_6_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_6_targ_ht] )
  `create_and_bind_axi_slv  ( l2_7_targ_ht  , 40, 512, 4, 8, axi_if.slave_if[e_l2_7_targ_ht] )
  // X4 LPDDR_PPP_HT // TODO: its _MT in baseband_intf.md #1297
  `create_and_bind_axi_slv  ( lpddr_ppp_0_targ_mt , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_ppp_0_targ_mt] )
  `create_and_bind_axi_slv  ( lpddr_ppp_1_targ_mt , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_ppp_1_targ_mt] )
  `create_and_bind_axi_slv  ( lpddr_ppp_2_targ_mt , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_ppp_2_targ_mt] )
  `create_and_bind_axi_slv  ( lpddr_ppp_3_targ_mt , 40, 256, 8, 8, axi_if.slave_if[e_lpddr_ppp_3_targ_mt] )
  // =============================================================================================================
  // RTL <-> SVIP APB4 connections TODO: confirm addr_w
  // ARGS - (is_master, rtl_signal_name, addr_w, data_w, id_w, len_w, vip_intf)
  // =============================================================================================================
  // X8 L2_SYSCFG //
  `create_and_bind_apb4  ( aic_0_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_0_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_1_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_1_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_2_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_2_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_3_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_3_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_4_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_4_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_5_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_5_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_6_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_6_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( aic_7_targ_syscfg_apb_m, 16, 32, apb_if[e_aic_7_targ_syscfg].slave_if[0])
  // X8 L2_SYSCFG //
  `create_and_bind_apb4  ( l2_0_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_0_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_1_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_1_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_2_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_2_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_3_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_3_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_4_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_4_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_5_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_5_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_6_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_6_targ_syscfg].slave_if[0])
  `create_and_bind_apb4  ( l2_7_targ_syscfg_apb_m , 16, 32, apb_if[e_l2_7_targ_syscfg].slave_if[0])
  // X4 LPDDR_GRAPH_SYSCFG //
  `create_and_bind_apb4  ( lpddr_graph_0_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_graph_0_targ_syscfg].slave_if[0] )
  `create_and_bind_apb4  ( lpddr_graph_1_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_graph_1_targ_syscfg].slave_if[0] )
  `create_and_bind_apb4  ( lpddr_graph_2_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_graph_2_targ_syscfg].slave_if[0] )
  `create_and_bind_apb4  ( lpddr_graph_3_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_graph_3_targ_syscfg].slave_if[0] )
  // X4 LPDDR_PPP_SYSCFG //
  `create_and_bind_apb4  ( lpddr_ppp_0_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_ppp_0_targ_syscfg].slave_if[0] )
  `create_and_bind_apb4  ( lpddr_ppp_1_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_ppp_1_targ_syscfg].slave_if[0] )
  `create_and_bind_apb4  ( lpddr_ppp_2_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_ppp_2_targ_syscfg].slave_if[0] )
  `create_and_bind_apb4  ( lpddr_ppp_3_targ_syscfg_apb_m , 16, 32, apb_if[e_lpddr_ppp_3_targ_syscfg].slave_if[0] )
  // X2 PVE_SYSCFG //
  `create_and_bind_apb4  ( pve_0_targ_syscfg_apb_m , 16, 32, apb_if[e_pve_0_syscfg_lt].slave_if[0] )
  `create_and_bind_apb4  ( pve_1_targ_syscfg_apb_m , 16, 32, apb_if[e_pve_1_syscfg_lt].slave_if[0] )
  // X1 PCIE_SYSCFG
  `create_and_bind_apb4  ( pcie_targ_syscfg_apb_m , 16, 32, apb_if[e_pcie_targ_syscfg].slave_if[0] )
  // X1 DCD_SYSCFG
  `create_and_bind_apb4  ( dcd_targ_syscfg_apb_m  , 16, 32, apb_if[e_dcd_targ_syscfg].slave_if[0] )
  // X1 APU_SYSCFG
  `create_and_bind_apb4  ( apu_targ_syscfg_apb_m  , 16, 32, apb_if[e_apu_targ_syscfg].slave_if[0] )
  // X1 SOC_MGMT_SYSCFG
  `create_and_bind_apb4  ( soc_mgmt_targ_syscfg_apb_m , 19, 32, apb_if[e_soc_mgmt_targ_syscfg].slave_if[0] )
  // X1 SOC_PERIPH_SYSCFG
  `create_and_bind_apb4  ( soc_periph_targ_syscfg_apb_m , 16, 32, apb_if[e_soc_periph_targ_syscfg].slave_if[0] )
  // X1 SYS_SPM_SYSCFG
  `create_and_bind_apb4  ( sys_spm_targ_syscfg_apb_m , 16, 32, apb_if[e_sys_spm_targ_syscfg].slave_if[0] )
  // X1 DCD_TARG_CFG
  `create_and_bind_apb4  ( dcd_targ_cfg_apb_m  , 20, 32, apb_if[e_dcd_targ_cfg].slave_if[0])
  // X1 DDR_WEST_PLL_SYSCFG 
  `create_and_bind_apb4  ( ddr_wpll_targ_syscfg_apb_m  , 16, 32, apb_if[ddr_wpll_targ_syscfg].slave_if[0]) //TODO: check conn_matrix legality
  
  // =============================================================================================================
  // RTL <-> SVIP APB3 connections
  // ARGS - (is_master, rtl_signal_name, addr_w, data_w, id_w, len_w, vip_intf)
  // =============================================================================================================
  //TODO: change apb4 -> apb3 after RTL removes pprot & pstrb from these 3 intfs
  // X4 LPDDR_GRAPH_TARG_CFG //
  `create_and_bind_apb4  ( lpddr_graph_0_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_graph_0_targ_cfg].slave_if[0])
  `create_and_bind_apb4  ( lpddr_graph_1_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_graph_1_targ_cfg].slave_if[0])
  `create_and_bind_apb4  ( lpddr_graph_2_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_graph_2_targ_cfg].slave_if[0])
  `create_and_bind_apb4  ( lpddr_graph_3_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_graph_3_targ_cfg].slave_if[0])
  // X4 LPDDR_PPP_TARG_CFG //
  `create_and_bind_apb4  ( lpddr_ppp_0_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_ppp_0_targ_cfg].slave_if[0])
  `create_and_bind_apb4  ( lpddr_ppp_1_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_ppp_1_targ_cfg].slave_if[0])
  `create_and_bind_apb4  ( lpddr_ppp_2_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_ppp_2_targ_cfg].slave_if[0])
  `create_and_bind_apb4  ( lpddr_ppp_3_targ_cfg_apb_m , 32, 32, apb_if[e_lpddr_ppp_3_targ_cfg].slave_if[0])
  // X1 PCIE_TARG_CFG //
  `create_and_bind_apb4  ( pcie_targ_cfg_apb_m , 20, 32, apb_if[e_pcie_targ_cfg].slave_if[0] )

  // SysCfg AON clocks
  logic i_aic_0_aon_clk;
  logic i_aic_1_aon_clk;
  logic i_aic_2_aon_clk;
  logic i_aic_3_aon_clk;
  logic i_aic_4_aon_clk;
  logic i_aic_5_aon_clk;
  logic i_aic_6_aon_clk;
  logic i_aic_7_aon_clk;
  logic i_apu_aon_clk;
  logic i_dcd_aon_clk;
  logic i_l2_0_aon_clk;
  logic i_l2_1_aon_clk;
  logic i_l2_2_aon_clk;
  logic i_l2_3_aon_clk;
  logic i_l2_4_aon_clk;
  logic i_l2_5_aon_clk;
  logic i_l2_6_aon_clk;
  logic i_l2_7_aon_clk;
  logic i_ddr_wpll_aon_clk;
  logic i_lpddr_graph_0_aon_clk;
  logic i_lpddr_graph_1_aon_clk;
  logic i_lpddr_graph_2_aon_clk;
  logic i_lpddr_graph_3_aon_clk;
  logic i_lpddr_ppp_0_aon_clk;
  logic i_lpddr_ppp_1_aon_clk;
  logic i_lpddr_ppp_2_aon_clk;
  logic i_lpddr_ppp_3_aon_clk;
  logic i_pcie_aon_clk;
  logic i_pve_0_aon_clk;
  logic i_pve_1_aon_clk;
  logic i_soc_mgmt_aon_clk;
  logic i_soc_periph_aon_clk;
  logic i_sys_spm_aon_clk;

  assign i_aic_0_aon_clk = clk_50MHz;
  assign i_aic_1_aon_clk = clk_50MHz;
  assign i_aic_2_aon_clk = clk_50MHz;
  assign i_aic_3_aon_clk = clk_50MHz;
  assign i_aic_4_aon_clk = clk_50MHz;
  assign i_aic_5_aon_clk = clk_50MHz;
  assign i_aic_6_aon_clk = clk_50MHz;
  assign i_aic_7_aon_clk = clk_50MHz;
  assign i_apu_aon_clk = clk_50MHz;
  assign i_dcd_aon_clk = clk_50MHz;
  assign i_l2_0_aon_clk = clk_50MHz;
  assign i_l2_1_aon_clk = clk_50MHz;
  assign i_l2_2_aon_clk = clk_50MHz;
  assign i_l2_3_aon_clk = clk_50MHz;
  assign i_l2_4_aon_clk = clk_50MHz;
  assign i_l2_5_aon_clk = clk_50MHz;
  assign i_l2_6_aon_clk = clk_50MHz;
  assign i_l2_7_aon_clk = clk_50MHz;
  assign i_ddr_wpll_aon_clk = clk_50MHz;
  assign i_lpddr_graph_0_aon_clk = clk_50MHz;
  assign i_lpddr_graph_1_aon_clk = clk_50MHz;
  assign i_lpddr_graph_2_aon_clk = clk_50MHz;
  assign i_lpddr_graph_3_aon_clk = clk_50MHz;
  assign i_lpddr_ppp_0_aon_clk = clk_50MHz;
  assign i_lpddr_ppp_1_aon_clk = clk_50MHz;
  assign i_lpddr_ppp_2_aon_clk = clk_50MHz;
  assign i_lpddr_ppp_3_aon_clk = clk_50MHz;
  assign i_pcie_aon_clk = clk_50MHz;
  assign i_pve_0_aon_clk = clk_50MHz;
  assign i_pve_1_aon_clk = clk_50MHz;
  assign i_soc_mgmt_aon_clk = clk_50MHz;
  assign i_soc_periph_aon_clk = clk_50MHz;
  assign i_sys_spm_aon_clk = clk_50MHz;

  // =============================================================================================================
  // Assign the VIP reset and clock pins
  // =============================================================================================================
  assign enoc_clk              = clk_1_2GHz;
  assign enoc_rst_n            = axi_reset_if.reset;
  assign rst_n                 = axi_reset_if.reset;
  assign axi_reset_if.clk      = clk_1_2GHz;
  //Assign CLK & RST for all AXI INITs
  genvar i;
  generate
    for (i = 0; i < `NUM_AXI_INITIATORS; i++) begin : AXI_INIT_CLK_ASSIGNMENTS //{
      if(i == e_dcd_dec_0_init_mt || i == e_dcd_dec_1_init_mt ||
         i == e_dcd_dec_2_init_mt || i == e_dcd_mcu_init_lt   ||
         i == e_pcie_init_mt)
        assign axi_if.master_if[i].aclk  = clk_600MHz;
      else
        assign axi_if.master_if[i].aclk  = clk_1_2GHz;

      assign axi_if.master_if[i].aresetn  = rst_n;
    end //}
  endgenerate
  //Assign CLK & RST for all AXI TARGs
  genvar j;
  generate
    for (j = 0; j < `NUM_AXI_TARGETS; j++) begin : AXI_TARG_CLK_ASSIGNMENTS //{
      if((j == e_lpddr_graph_0_targ_ht) || (j == e_lpddr_ppp_0_targ_mt) ||
         (j == e_lpddr_graph_1_targ_ht) || (j == e_lpddr_ppp_1_targ_mt) ||
         (j == e_lpddr_graph_2_targ_ht) || (j == e_lpddr_ppp_2_targ_mt) ||
         (j == e_lpddr_graph_3_targ_ht) || (j == e_lpddr_ppp_3_targ_mt))
        assign axi_if.slave_if[j].aclk   = clk_800MHz;
      else if(j == e_pcie_targ_mt) 
        assign axi_if.slave_if[j].aclk   = clk_600MHz;
      else if(j == e_pcie_targ_cfg_dbi) 
        assign axi_if.slave_if[j].aclk   = clk_100MHz;
      else
        assign axi_if.slave_if[j].aclk   = clk_1_2GHz;

      assign axi_if.slave_if[j].aresetn   = rst_n;
    end //}
  endgenerate
  //Assign CLK & RST for all APB TARGs
  genvar k;
  generate
    for (k = 0; k < (`NUM_APB3_TARGETS + `NUM_APB4_TARGETS); k++) begin : APB_CLK_RST_ASSIGNMENTS //{
      assign apb_if[k].slave_if[0].pclk = clk_1_2GHz; //TODO: fix specific clk to correct targ
      assign apb_if[k].slave_if[0].presetn = rst_n;
    end //}
  endgenerate

  // =============================================================================================================
  // Initialization of misc signals
  // =============================================================================================================
  initial begin //{
    i_aic_0_clken                   = 1;
    i_aic_1_clken                   = 1;
    i_aic_2_clken                   = 1;
    i_aic_3_clken                   = 1;
    i_aic_4_clken                   = 1;
    i_aic_5_clken                   = 1;
    i_aic_6_clken                   = 1;
    i_aic_7_clken                   = 1;
    i_apu_x_clken                   = 1;
    i_dcd_codec_clken               = 1;
    i_dcd_mcu_clken                 = 1;
    i_l2_0_clken                    = 1;
    i_l2_1_clken                    = 1;
    i_l2_2_clken                    = 1;
    i_l2_3_clken                    = 1;
    i_l2_4_clken                    = 1;
    i_l2_5_clken                    = 1;
    i_l2_6_clken                    = 1;
    i_l2_7_clken                    = 1;
    i_lpddr_graph_0_clken           = 1;
    i_lpddr_graph_1_clken           = 1;
    i_lpddr_graph_2_clken           = 1;
    i_lpddr_graph_3_clken           = 1;
    i_lpddr_ppp_0_clken             = 1;
    i_lpddr_ppp_1_clken             = 1;
    i_lpddr_ppp_2_clken             = 1;
    i_lpddr_ppp_3_clken             = 1;
    i_pcie_init_mt_clken            = 1;
    i_pcie_targ_mt_clken            = 1;
    i_pcie_targ_cfg_clken           = 1;
    i_pcie_targ_cfg_dbi_clken       = 1;
    i_pve_0_clken                   = 1;
    i_pve_1_clken                   = 1;
    i_soc_mgmt_clken                = 1;
    i_soc_periph_clken              = 1;
    i_sys_spm_clken                 = 1;
    i_l2_addr_mode_port_b0          = 1;
    i_l2_addr_mode_port_b1          = 0;
    i_l2_intr_mode_port_b0          = 1;
    i_l2_intr_mode_port_b1          = 1;
    i_lpddr_graph_addr_mode_port_b0 = 1;
    i_lpddr_graph_addr_mode_port_b1 = 0;
    i_lpddr_graph_intr_mode_port_b0 = 1;
    i_lpddr_graph_intr_mode_port_b1 = 1;
    i_lpddr_ppp_addr_mode_port_b0   = 1;
    i_lpddr_ppp_addr_mode_port_b1   = 0;
    i_lpddr_ppp_intr_mode_port_b0   = 1;
    i_lpddr_ppp_intr_mode_port_b1   = 1;
    // DFT
    test_mode = 0;
    scan_en = 0;
  end //}

  // =============================================================================================================
  // clock generation for different frequencies
  // =============================================================================================================
  // Generate the fast clock
  always begin //{
    clk_1_2GHz <= 1;
    #(CLK_PERIOD_1200 / 2);
    clk_1_2GHz <= 0;
    #(CLK_PERIOD_1200 / 2);
  end //}
  // Generate DDR East/West clock
  always begin //{
    clk_800MHz <= 1;
    #(CLK_PERIOD_800 / 2);
    clk_800MHz <= 0;
    #(CLK_PERIOD_800 / 2);
  end //}
  // Generate Codec clock
  always begin //{
    clk_600MHz <= 1;
    #(CLK_PERIOD_600 / 2);
    clk_600MHz <= 0;
    #(CLK_PERIOD_600 / 2);
  end //}
  // Generate the slow clock
  always begin //{
    clk_100MHz <= 1;
    #(CLK_PERIOD_100 / 2);
    clk_100MHz <= 0;
    #(CLK_PERIOD_100 / 2);
  end //}
  // Generate the ref clock
  always begin //{
    clk_50MHz <= 1;
    #(CLK_PERIOD_50 / 2);
    clk_50MHz <= 0;
    #(CLK_PERIOD_50 / 2);
  end //}

  // =============================================================================================================
  // Assignments of power domain and other misc signals from DUT to user defined interface
  // =============================================================================================================
  assign tb_intf.enoc_clk                         = dut.i_noc_clk                           ;
  assign tb_intf.enoc_rst_n                       = dut.i_noc_rst_n                         ;
  assign i_aic_0_pwr_idle_req                     = tb_intf.i_aic_0_pwr_idle_req            ;
  assign i_aic_1_pwr_idle_req                     = tb_intf.i_aic_1_pwr_idle_req            ;
  assign i_aic_2_pwr_idle_req                     = tb_intf.i_aic_2_pwr_idle_req            ;
  assign i_aic_3_pwr_idle_req                     = tb_intf.i_aic_3_pwr_idle_req            ;
  assign i_aic_4_pwr_idle_req                     = tb_intf.i_aic_4_pwr_idle_req            ;
  assign i_aic_5_pwr_idle_req                     = tb_intf.i_aic_5_pwr_idle_req            ;
  assign i_aic_6_pwr_idle_req                     = tb_intf.i_aic_6_pwr_idle_req            ;
  assign i_aic_7_pwr_idle_req                     = tb_intf.i_aic_7_pwr_idle_req            ;
  assign i_apu_pwr_idle_req                       = tb_intf.i_apu_pwr_idle_req              ;
  assign i_dcd_mcu_pwr_idle_req                   = tb_intf.i_dcd_mcu_pwr_idle_req          ;
  assign i_dcd_pwr_idle_req                       = tb_intf.i_dcd_pwr_idle_req              ;
  assign i_l2_0_pwr_idle_req                      = tb_intf.i_l2_0_pwr_idle_req             ;
  assign i_l2_1_pwr_idle_req                      = tb_intf.i_l2_1_pwr_idle_req             ;
  assign i_l2_2_pwr_idle_req                      = tb_intf.i_l2_2_pwr_idle_req             ;
  assign i_l2_3_pwr_idle_req                      = tb_intf.i_l2_3_pwr_idle_req             ;
  assign i_l2_4_pwr_idle_req                      = tb_intf.i_l2_4_pwr_idle_req             ;
  assign i_l2_5_pwr_idle_req                      = tb_intf.i_l2_5_pwr_idle_req             ;
  assign i_l2_6_pwr_idle_req                      = tb_intf.i_l2_6_pwr_idle_req             ;
  assign i_l2_7_pwr_idle_req                      = tb_intf.i_l2_7_pwr_idle_req             ;
  assign i_lpddr_graph_0_pwr_idle_vec_req         = tb_intf.i_lpddr_graph_0_pwr_idle_vec_req;
  assign i_lpddr_graph_1_pwr_idle_vec_req         = tb_intf.i_lpddr_graph_1_pwr_idle_vec_req;
  assign i_lpddr_graph_2_pwr_idle_vec_req         = tb_intf.i_lpddr_graph_2_pwr_idle_vec_req;
  assign i_lpddr_graph_3_pwr_idle_vec_req         = tb_intf.i_lpddr_graph_3_pwr_idle_vec_req;
  assign i_lpddr_ppp_0_pwr_idle_vec_req           = tb_intf.i_lpddr_ppp_0_pwr_idle_vec_req  ;
  assign i_lpddr_ppp_1_pwr_idle_vec_req           = tb_intf.i_lpddr_ppp_1_pwr_idle_vec_req  ;
  assign i_lpddr_ppp_2_pwr_idle_vec_req           = tb_intf.i_lpddr_ppp_2_pwr_idle_vec_req  ;
  assign i_lpddr_ppp_3_pwr_idle_vec_req           = tb_intf.i_lpddr_ppp_3_pwr_idle_vec_req  ;
  assign i_pcie_init_mt_pwr_idle_req              = tb_intf.i_pcie_init_mt_pwr_idle_req     ;
  assign i_pcie_targ_mt_pwr_idle_req              = tb_intf.i_pcie_targ_mt_pwr_idle_req     ;
  assign i_pcie_targ_cfg_pwr_idle_req             = tb_intf.i_pcie_targ_cfg_pwr_idle_req    ;
  assign i_pcie_targ_cfg_dbi_pwr_idle_req         = tb_intf.i_pcie_targ_cfg_dbi_pwr_idle_req;
  assign i_pve_0_pwr_idle_req                     = tb_intf.i_pve_0_pwr_idle_req            ;
  assign i_pve_1_pwr_idle_req                     = tb_intf.i_pve_1_pwr_idle_req            ;
  assign i_soc_mgmt_pwr_idle_req                  = tb_intf.i_soc_mgmt_pwr_idle_req         ;
  assign i_soc_periph_pwr_idle_req                = tb_intf.i_soc_periph_pwr_idle_req       ;
  assign i_sys_spm_pwr_idle_req                   = tb_intf.i_sys_spm_pwr_idle_req          ;
  assign i_aic_0_pwr_tok_idle_req                 = tb_intf.i_aic_0_pwr_tok_idle_req        ;
  assign i_aic_1_pwr_tok_idle_req                 = tb_intf.i_aic_1_pwr_tok_idle_req        ;
  assign i_aic_2_pwr_tok_idle_req                 = tb_intf.i_aic_2_pwr_tok_idle_req        ;
  assign i_aic_3_pwr_tok_idle_req                 = tb_intf.i_aic_3_pwr_tok_idle_req        ;
  assign i_aic_4_pwr_tok_idle_req                 = tb_intf.i_aic_4_pwr_tok_idle_req        ;
  assign i_aic_5_pwr_tok_idle_req                 = tb_intf.i_aic_5_pwr_tok_idle_req        ;
  assign i_aic_6_pwr_tok_idle_req                 = tb_intf.i_aic_6_pwr_tok_idle_req        ;
  assign i_aic_7_pwr_tok_idle_req                 = tb_intf.i_aic_7_pwr_tok_idle_req        ;
  assign i_apu_pwr_tok_idle_req                   = tb_intf.i_apu_pwr_tok_idle_req          ;

  assign tb_intf.o_aic_0_pwr_tok_idle_val         = o_aic_0_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_1_pwr_tok_idle_val         = o_aic_1_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_2_pwr_tok_idle_val         = o_aic_2_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_3_pwr_tok_idle_val         = o_aic_3_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_4_pwr_tok_idle_val         = o_aic_4_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_5_pwr_tok_idle_val         = o_aic_5_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_6_pwr_tok_idle_val         = o_aic_6_pwr_tok_idle_val                ;
  assign tb_intf.o_aic_7_pwr_tok_idle_val         = o_aic_7_pwr_tok_idle_val                ;
  assign tb_intf.o_apu_pwr_tok_idle_val           = o_apu_pwr_tok_idle_val                  ;
  assign tb_intf.o_aic_0_pwr_idle_val             = o_aic_0_pwr_idle_val                    ;
  assign tb_intf.o_aic_1_pwr_idle_val             = o_aic_1_pwr_idle_val                    ;
  assign tb_intf.o_aic_2_pwr_idle_val             = o_aic_2_pwr_idle_val                    ;
  assign tb_intf.o_aic_3_pwr_idle_val             = o_aic_3_pwr_idle_val                    ;
  assign tb_intf.o_aic_4_pwr_idle_val             = o_aic_4_pwr_idle_val                    ;
  assign tb_intf.o_aic_5_pwr_idle_val             = o_aic_5_pwr_idle_val                    ;
  assign tb_intf.o_aic_6_pwr_idle_val             = o_aic_6_pwr_idle_val                    ;
  assign tb_intf.o_aic_7_pwr_idle_val             = o_aic_7_pwr_idle_val                    ;
  assign tb_intf.o_apu_pwr_idle_val               = o_apu_pwr_idle_val                      ;
  assign tb_intf.o_dcd_mcu_pwr_idle_val           = o_dcd_mcu_pwr_idle_val                  ;
  assign tb_intf.o_dcd_pwr_idle_val               = o_dcd_pwr_idle_val                      ;
  assign tb_intf.o_l2_0_pwr_idle_val              = o_l2_0_pwr_idle_val                     ;
  assign tb_intf.o_l2_1_pwr_idle_val              = o_l2_1_pwr_idle_val                     ;
  assign tb_intf.o_l2_2_pwr_idle_val              = o_l2_2_pwr_idle_val                     ;
  assign tb_intf.o_l2_3_pwr_idle_val              = o_l2_3_pwr_idle_val                     ;
  assign tb_intf.o_l2_4_pwr_idle_val              = o_l2_4_pwr_idle_val                     ;
  assign tb_intf.o_l2_5_pwr_idle_val              = o_l2_5_pwr_idle_val                     ;
  assign tb_intf.o_l2_6_pwr_idle_val              = o_l2_6_pwr_idle_val                     ;
  assign tb_intf.o_l2_7_pwr_idle_val              = o_l2_7_pwr_idle_val                     ;
  assign tb_intf.o_lpddr_graph_0_pwr_idle_vec_val = o_lpddr_graph_0_pwr_idle_vec_val        ;
  assign tb_intf.o_lpddr_graph_1_pwr_idle_vec_val = o_lpddr_graph_1_pwr_idle_vec_val        ;
  assign tb_intf.o_lpddr_graph_2_pwr_idle_vec_val = o_lpddr_graph_2_pwr_idle_vec_val        ;
  assign tb_intf.o_lpddr_graph_3_pwr_idle_vec_val = o_lpddr_graph_3_pwr_idle_vec_val        ;
  assign tb_intf.o_lpddr_ppp_0_pwr_idle_vec_val   = o_lpddr_ppp_0_pwr_idle_vec_val          ;
  assign tb_intf.o_lpddr_ppp_1_pwr_idle_vec_val   = o_lpddr_ppp_1_pwr_idle_vec_val          ;
  assign tb_intf.o_lpddr_ppp_2_pwr_idle_vec_val   = o_lpddr_ppp_2_pwr_idle_vec_val          ;
  assign tb_intf.o_lpddr_ppp_3_pwr_idle_vec_val   = o_lpddr_ppp_3_pwr_idle_vec_val          ;
  assign tb_intf.o_pcie_init_mt_pwr_idle_val      = o_pcie_init_mt_pwr_idle_val             ;
  assign tb_intf.o_pcie_targ_mt_pwr_idle_val      = o_pcie_targ_mt_pwr_idle_val             ;
  assign tb_intf.o_pcie_targ_cfg_pwr_idle_val     = o_pcie_targ_cfg_pwr_idle_val            ;
  assign tb_intf.o_pcie_targ_cfg_dbi_pwr_idle_val = o_pcie_targ_cfg_dbi_pwr_idle_val        ;
  assign tb_intf.o_pve_0_pwr_idle_val             = o_pve_0_pwr_idle_val                    ;
  assign tb_intf.o_pve_1_pwr_idle_val             = o_pve_1_pwr_idle_val                    ;
  assign tb_intf.o_soc_mgmt_pwr_idle_val          = o_soc_mgmt_pwr_idle_val                 ;
  assign tb_intf.o_soc_periph_pwr_idle_val        = o_soc_periph_pwr_idle_val               ;
  assign tb_intf.o_sys_spm_pwr_idle_val           = o_sys_spm_pwr_idle_val                  ;

  assign tb_intf.o_aic_0_pwr_idle_ack             = o_aic_0_pwr_idle_ack                    ;
  assign tb_intf.o_aic_1_pwr_idle_ack             = o_aic_1_pwr_idle_ack                    ;
  assign tb_intf.o_aic_2_pwr_idle_ack             = o_aic_2_pwr_idle_ack                    ;
  assign tb_intf.o_aic_3_pwr_idle_ack             = o_aic_3_pwr_idle_ack                    ;
  assign tb_intf.o_aic_4_pwr_idle_ack             = o_aic_4_pwr_idle_ack                    ;
  assign tb_intf.o_aic_5_pwr_idle_ack             = o_aic_5_pwr_idle_ack                    ;
  assign tb_intf.o_aic_6_pwr_idle_ack             = o_aic_6_pwr_idle_ack                    ;
  assign tb_intf.o_aic_7_pwr_idle_ack             = o_aic_7_pwr_idle_ack                    ;
  assign tb_intf.o_apu_pwr_idle_ack               = o_apu_pwr_idle_ack                      ;
  assign tb_intf.o_dcd_mcu_pwr_idle_ack           = o_dcd_mcu_pwr_idle_ack                  ;
  assign tb_intf.o_dcd_pwr_idle_ack               = o_dcd_pwr_idle_ack                      ;
  assign tb_intf.o_l2_0_pwr_idle_ack              = o_l2_0_pwr_idle_ack                     ;
  assign tb_intf.o_l2_1_pwr_idle_ack              = o_l2_1_pwr_idle_ack                     ;
  assign tb_intf.o_l2_2_pwr_idle_ack              = o_l2_2_pwr_idle_ack                     ;
  assign tb_intf.o_l2_3_pwr_idle_ack              = o_l2_3_pwr_idle_ack                     ;
  assign tb_intf.o_l2_4_pwr_idle_ack              = o_l2_4_pwr_idle_ack                     ;
  assign tb_intf.o_l2_5_pwr_idle_ack              = o_l2_5_pwr_idle_ack                     ;
  assign tb_intf.o_l2_6_pwr_idle_ack              = o_l2_6_pwr_idle_ack                     ;
  assign tb_intf.o_l2_7_pwr_idle_ack              = o_l2_7_pwr_idle_ack                     ;
  assign tb_intf.o_lpddr_graph_0_pwr_idle_vec_ack = o_lpddr_graph_0_pwr_idle_vec_ack        ;
  assign tb_intf.o_lpddr_graph_1_pwr_idle_vec_ack = o_lpddr_graph_1_pwr_idle_vec_ack        ;
  assign tb_intf.o_lpddr_graph_2_pwr_idle_vec_ack = o_lpddr_graph_2_pwr_idle_vec_ack        ;
  assign tb_intf.o_lpddr_graph_3_pwr_idle_vec_ack = o_lpddr_graph_3_pwr_idle_vec_ack        ;
  assign tb_intf.o_lpddr_ppp_0_pwr_idle_vec_ack   = o_lpddr_ppp_0_pwr_idle_vec_ack          ;
  assign tb_intf.o_lpddr_ppp_1_pwr_idle_vec_ack   = o_lpddr_ppp_1_pwr_idle_vec_ack          ;
  assign tb_intf.o_lpddr_ppp_2_pwr_idle_vec_ack   = o_lpddr_ppp_2_pwr_idle_vec_ack          ;
  assign tb_intf.o_lpddr_ppp_3_pwr_idle_vec_ack   = o_lpddr_ppp_3_pwr_idle_vec_ack          ;
  assign tb_intf.o_pcie_init_mt_pwr_idle_ack      = o_pcie_init_mt_pwr_idle_ack             ;
  assign tb_intf.o_pcie_targ_mt_pwr_idle_ack      = o_pcie_targ_mt_pwr_idle_ack             ;
  assign tb_intf.o_pcie_targ_cfg_pwr_idle_ack     = o_pcie_targ_cfg_pwr_idle_ack            ;
  assign tb_intf.o_pcie_targ_cfg_dbi_pwr_idle_ack = o_pcie_targ_cfg_dbi_pwr_idle_ack        ;
  assign tb_intf.o_pve_0_pwr_idle_ack             = o_pve_0_pwr_idle_ack                    ;
  assign tb_intf.o_pve_1_pwr_idle_ack             = o_pve_1_pwr_idle_ack                    ;
  assign tb_intf.o_soc_mgmt_pwr_idle_ack          = o_soc_mgmt_pwr_idle_ack                 ;
  assign tb_intf.o_soc_periph_pwr_idle_ack        = o_soc_periph_pwr_idle_ack               ;
  assign tb_intf.o_sys_spm_pwr_idle_ack           = o_sys_spm_pwr_idle_ack                  ;
  assign tb_intf.o_aic_0_pwr_tok_idle_ack         = o_aic_0_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_1_pwr_tok_idle_ack         = o_aic_1_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_2_pwr_tok_idle_ack         = o_aic_2_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_3_pwr_tok_idle_ack         = o_aic_3_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_4_pwr_tok_idle_ack         = o_aic_4_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_5_pwr_tok_idle_ack         = o_aic_5_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_6_pwr_tok_idle_ack         = o_aic_6_pwr_tok_idle_ack                ;
  assign tb_intf.o_aic_7_pwr_tok_idle_ack         = o_aic_7_pwr_tok_idle_ack                ;
  assign tb_intf.o_apu_pwr_tok_idle_ack           = o_apu_pwr_tok_idle_ack                  ;

  // =============================================================================================================
  // Instantiate DUT
  // =============================================================================================================
  `DUT dut (.*);
  // =============================================================================================================
  // Bind DUT with AXI Protocol Checker
  // ARGS - (clk_rst, inst_name, log1, log2, clk_period_ns, addr_w, data_w, id_w, is_init, is_pcie, is_sdma)
  // =============================================================================================================
  // INIT side
  // =============================================================================================================
  // X8 AIC_HT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_0,  aic_0_init_ht     , "wr_aic_0_init_ht_wr_txns.txt"       , "rd_aic_0_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_1,  aic_1_init_ht     , "wr_aic_1_init_ht_wr_txns.txt"       , "rd_aic_1_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_2,  aic_2_init_ht     , "wr_aic_2_init_ht_wr_txns.txt"       , "rd_aic_2_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_3,  aic_3_init_ht     , "wr_aic_3_init_ht_wr_txns.txt"       , "rd_aic_3_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_4,  aic_4_init_ht     , "wr_aic_4_init_ht_wr_txns.txt"       , "rd_aic_4_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_5,  aic_5_init_ht     , "wr_aic_5_init_ht_wr_txns.txt"       , "rd_aic_5_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_6,  aic_6_init_ht     , "wr_aic_6_init_ht_wr_txns.txt"       , "rd_aic_6_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_7,  aic_7_init_ht     , "wr_aic_7_init_ht_wr_txns.txt"       , "rd_aic_7_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  //// X8 AIC_LT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_0,  aic_0_init_lt     , "wr_aic_0_init_lt_wr_txns.txt"       , "rd_aic_0_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_1,  aic_1_init_lt     , "wr_aic_1_init_lt_wr_txns.txt"       , "rd_aic_1_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_2,  aic_2_init_lt     , "wr_aic_2_init_lt_wr_txns.txt"       , "rd_aic_2_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_3,  aic_3_init_lt     , "wr_aic_3_init_lt_wr_txns.txt"       , "rd_aic_3_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_4,  aic_4_init_lt     , "wr_aic_4_init_lt_wr_txns.txt"       , "rd_aic_4_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_5,  aic_5_init_lt     , "wr_aic_5_init_lt_wr_txns.txt"       , "rd_aic_5_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_6,  aic_6_init_lt     , "wr_aic_6_init_lt_wr_txns.txt"       , "rd_aic_6_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_7,  aic_7_init_lt     , "wr_aic_7_init_lt_wr_txns.txt"       , "rd_aic_7_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  //// X6 SDMA_HT_LT //
  ////`DECLARE_AND_BIND_AXI_CHECKER  (sdma_0, sdma_0_init_ht_0  , "wr_sdma_0_init_ht_0_wr_txns.txt"    , "rd_sdma_0_init_ht_0_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 ) //TODO: en after SDMA_PPMU_INIT
  ////`DECLARE_AND_BIND_AXI_CHECKER  (sdma_0, sdma_0_init_ht_1  , "wr_sdma_0_init_ht_1_wr_txns.txt"    , "rd_sdma_0_init_ht_1_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  ////`DECLARE_AND_BIND_AXI_CHECKER  (sdma_0, sdma_0_init_lt    , "wr_sdma_0_init_lt_wr_txns.txt"      , "rd_sdma_0_init_lt_rd_txns.txt"    , 0.83   , 40, 64 , 4, 1, 1, 0 )
  ////`DECLARE_AND_BIND_AXI_CHECKER  (sdma_1, sdma_1_init_ht_0  , "wr_sdma_1_init_ht_0_wr_txns.txt"    , "rd_sdma_1_init_ht_0_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  ////`DECLARE_AND_BIND_AXI_CHECKER  (sdma_1, sdma_1_init_ht_1  , "wr_sdma_1_init_ht_1_wr_txns.txt"    , "rd_sdma_1_init_ht_1_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  ////`DECLARE_AND_BIND_AXI_CHECKER  (sdma_1, sdma_1_init_lt    , "wr_sdma_1_init_lt_wr_txns.txt"      , "rd_sdma_1_init_lt_rd_txns.txt"    , 0.83   , 40, 64 , 4, 1, 1, 0 )
  //// X4 PVE_LT_HT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (pve_0, pve_0_init_lt     , "wr_pve_0_init_lt_wr_txns.txt"       , "rd_pve_0_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 8  , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (pve_0, pve_0_init_ht     , "wr_pve_0_init_ht_wr_txns.txt"       , "rd_pve_0_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 11 , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (pve_1, pve_1_init_lt     , "wr_pve_1_init_lt_wr_txns.txt"       , "rd_pve_1_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 8  , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (pve_1, pve_1_init_ht     , "wr_pve_1_init_ht_wr_txns.txt"       , "rd_pve_1_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 11 , 1, 0, 0 )
  //// X3 DCD_MT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (dcd_mcu, dcd_dec_0_init_mt , "wr_dcd_dec_0_init_mt_wr_txns.txt"   , "rd_dcd_dec_0_init_mt_rd_txns.txt" , 0.83   , 40, 128, 5  , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (dcd_mcu, dcd_dec_1_init_mt , "wr_dcd_dec_1_init_mt_wr_txns.txt"   , "rd_dcd_dec_1_init_mt_rd_txns.txt" , 0.83   , 40, 128, 5  , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (dcd_mcu, dcd_dec_2_init_mt , "wr_dcd_dec_2_init_mt_wr_txns.txt"   , "rd_dcd_dec_2_init_mt_rd_txns.txt" , 0.83   , 40, 128, 5  , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (dcd_mcu, dcd_mcu_init_lt   , "wr_dcd_mcu_init_lt_wr_txns.txt"     , "rd_dcd_mcu_init_lt_rd_txns.txt"   , 0.83   , 40, 128, 5  , 1, 0, 0 )
  //// X2 APU_LT_MT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (apu, apu_init_lt       , "wr_apu_init_lt_wr_txns.txt"         , "rd_apu_init_lt_rd_txns.txt"       , 0.83   , 40, 64, 8   , 1, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (apu, apu_init_mt       , "wr_apu_init_mt_wr_txns.txt"         , "rd_apu_init_mt_rd_txns.txt"       , 0.83   , 40, 256, 9  , 1, 0, 0 )
  //// X1 PCIE_MT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (pcie, pcie_init_mt      , "wr_pcie_init_mt_wr_txns.txt"        , "rd_pcie_init_mt_rd_txns.txt"      , 0.83   , 40, 128, 7  , 1, 0, 1 )
  //// X1 SOC_MGMT_LT  //
  //`DECLARE_AND_BIND_AXI_CHECKER  (soc_mgmt, soc_mgmt_init_lt  , "wr_soc_mgmt_init_lt_wr_txns.txt"    , "rd_soc_mgmt_init_lt_rd_txns.txt"  , 0.83   , 40, 64, 4   , 1, 0, 0 )
  //// X1 SOC_PERIPH_LT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (soc_periph, soc_periph_init_lt, "wr_soc_periph_init_lt_wr_txns.txt"  , "rd_soc_mgmt_init_lt_rd_txns.txt"  , 0.83   , 40, 64, 4   , 1, 0, 0 )
  //
  //// =============================================================================================================
  //// TARG side
  //// =============================================================================================================
  //// X8 AIC_LT //
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_0, aic_0_targ_lt         , "wr_aic_0_targ_lt_wr_txns.txt"        , "rd_aic_0_targ_lt_rd_txns.txt"         , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_1, aic_1_targ_lt         , "wr_aic_1_targ_lt_wr_txns.txt"        , "rd_aic_1_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_2, aic_2_targ_lt         , "wr_aic_2_targ_lt_wr_txns.txt"        , "rd_aic_2_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_3, aic_3_targ_lt         , "wr_aic_3_targ_lt_wr_txns.txt"        , "rd_aic_3_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_4, aic_4_targ_lt         , "wr_aic_4_targ_lt_wr_txns.txt"        , "rd_aic_4_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_5, aic_5_targ_lt         , "wr_aic_5_targ_lt_wr_txns.txt"        , "rd_aic_5_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_6, aic_6_targ_lt         , "wr_aic_6_targ_lt_wr_txns.txt"        , "rd_aic_6_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //`DECLARE_AND_BIND_AXI_CHECKER  (aic_7, aic_7_targ_lt         , "wr_aic_7_targ_lt_wr_txns.txt"        , "rd_aic_7_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  //// X2 SDMA_LT
  ////`DECLARE_AND_BIND_AXI_CHECKER  ( sdma_0, sdma_0_targ_lt        , "wr_sdma_0_targ_lt_wr_txns.txt"       , "rd_sdma_0_targ_lt_rd_txns.txt"       , 0.83 , 40, 64, 4, 0, 1, 0) //TODO: en after SDMA_PPMU_INIT
  ////`DECLARE_AND_BIND_AXI_CHECKER  ( sdma_0, sdma_1_targ_lt        , "wr_sdma_1_targ_lt_wr_txns.txt"       , "rd_sdma_1_targ_lt_rd_txns.txt"       , 0.83 , 40, 64, 4, 0, 1, 0)
  //// X2 PVE_LT //
  //`DECLARE_AND_BIND_AXI_CHECKER  ( pve_0, pve_0_targ_lt         , "wr_pve_0_targ_lt_wr_txns.txt"        , "rd_pve_0_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( pve_1, pve_1_targ_lt         , "wr_pve_1_targ_lt_wr_txns.txt"        , "rd_pve_1_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 4, 0, 0, 0)
  //// X1 APU_LT
  //`DECLARE_AND_BIND_AXI_CHECKER  ( apu, apu_targ_lt           , "wr_apu_targ_lt_wr_txns.txt"          , "rd_apu_targ_lt_rd_txns.txt"          , 0.83 , 40, 64, 10, 0, 0, 0 )
  //// X1 SOC_MGMT_LT
  //`DECLARE_AND_BIND_AXI_CHECKER  ( soc_mgmt, soc_mgmt_targ_lt      , "wr_soc_mgmt_targ_lt_wr_txns.txt"     , "rd_soc_mgmt_targ_lt_rd_txns.txt"     , 0.83 , 40, 64, 4, 0, 0, 0 )
  //// X1 SOC_PERIPH_LT
  //`DECLARE_AND_BIND_AXI_CHECKER  ( soc_periph, soc_periph_targ_lt    , "wr_soc_periph_targ_lt_wr_txns.txt"   , "rd_soc_periph_targ_lt_rd_txns.txt"   , 0.83 , 40, 64, 4, 0, 0, 0 )
  //// X1 SYS_SPM_LT
  //`DECLARE_AND_BIND_AXI_CHECKER  ( sys_spm, sys_spm_targ_lt       , "wr_sys_spm_targ_lt_wr_txns.txt"      , "rd_sys_spm_targ_lt_rd_txns.txt"      , 0.83 , 40, 64, 4, 0, 0, 0 )
  //// X4 LPDDR_GRAPH_MT_slv
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_graph_0, lpddr_graph_0_targ_ht , "wr_lpddr_graph_0_targ_ht_wr_txns.txt", "rd_lpddr_graph_0_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_graph_1, lpddr_graph_1_targ_ht , "wr_lpddr_graph_1_targ_ht_wr_txns.txt", "rd_lpddr_graph_1_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_graph_2, lpddr_graph_2_targ_ht , "wr_lpddr_graph_2_targ_ht_wr_txns.txt", "rd_lpddr_graph_2_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_graph_3, lpddr_graph_3_targ_ht , "wr_lpddr_graph_3_targ_ht_wr_txns.txt", "rd_lpddr_graph_3_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  //// X2 PCIE_LT_MT // _slv
  //`DECLARE_AND_BIND_AXI_CHECKER  ( pcie, pcie_targ_cfg_dbi     , "wr_pcie_targ_cfg_dbi_wr_txns.txt"    , "rd_pcie_targ_cfg_dbi_rd_txns.txt"    , 0.83 , 40, 32,  4, 0, 0, 1 )
  //`DECLARE_AND_BIND_AXI_CHECKER  ( pcie, pcie_targ_mt          , "wr_pcie_targ_mt_wr_txns.txt"         , "rd_pcie_targ_mt_rd_txns.txt"         , 0.83 , 40, 128, 6, 0, 0, 1 )
  //// X8 L2_HT //
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_0, l2_0_targ_ht          , "wr_l2_0_targ_ht_wr_txns.txt"         , "rd_l2_0_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_1, l2_1_targ_ht          , "wr_l2_1_targ_ht_wr_txns.txt"         , "rd_l2_1_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_2, l2_2_targ_ht          , "wr_l2_2_targ_ht_wr_txns.txt"         , "rd_l2_2_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_3, l2_3_targ_ht          , "wr_l2_3_targ_ht_wr_txns.txt"         , "rd_l2_3_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_4, l2_4_targ_ht          , "wr_l2_4_targ_ht_wr_txns.txt"         , "rd_l2_4_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_5, l2_5_targ_ht          , "wr_l2_5_targ_ht_wr_txns.txt"         , "rd_l2_5_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_6, l2_6_targ_ht          , "wr_l2_6_targ_ht_wr_txns.txt"         , "rd_l2_6_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( l2_7, l2_7_targ_ht          , "wr_l2_7_targ_ht_wr_txns.txt"         , "rd_l2_7_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  //// X4 LPDDR_PPP_HT
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_ppp_0, lpddr_ppp_0_targ_mt   , "wr_lpddr_ppp_0_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_0_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_ppp_1, lpddr_ppp_1_targ_mt   , "wr_lpddr_ppp_1_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_1_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_ppp_2, lpddr_ppp_2_targ_mt   , "wr_lpddr_ppp_2_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_2_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)
  //`DECLARE_AND_BIND_AXI_CHECKER  ( lpddr_ppp_3, lpddr_ppp_3_targ_mt   , "wr_lpddr_ppp_3_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_3_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)

  // =============================================================================================================
  // Bind DUT with AXI Performance Tracker
  // ARGS - (clk_rst, inst_name, log1, log2, clk_period_ns, addr_w, data_w, id_w, is_init, is_pcie, is_sdma)
  // =============================================================================================================
  // INIT side
  // =============================================================================================================
  // X8 AIC_HT //
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_0,  aic_0_init_ht     , "wr_aic_0_init_ht_wr_txns.txt"       , "rd_aic_0_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_1,  aic_1_init_ht     , "wr_aic_1_init_ht_wr_txns.txt"       , "rd_aic_1_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_2,  aic_2_init_ht     , "wr_aic_2_init_ht_wr_txns.txt"       , "rd_aic_2_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_3,  aic_3_init_ht     , "wr_aic_3_init_ht_wr_txns.txt"       , "rd_aic_3_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_4,  aic_4_init_ht     , "wr_aic_4_init_ht_wr_txns.txt"       , "rd_aic_4_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_5,  aic_5_init_ht     , "wr_aic_5_init_ht_wr_txns.txt"       , "rd_aic_5_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_6,  aic_6_init_ht     , "wr_aic_6_init_ht_wr_txns.txt"       , "rd_aic_6_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_7,  aic_7_init_ht     , "wr_aic_7_init_ht_wr_txns.txt"       , "rd_aic_7_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 9, 1, 0, 0 )
  // X8 AIC_LT //
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_0,  aic_0_init_lt     , "wr_aic_0_init_lt_wr_txns.txt"       , "rd_aic_0_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_1,  aic_1_init_lt     , "wr_aic_1_init_lt_wr_txns.txt"       , "rd_aic_1_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_2,  aic_2_init_lt     , "wr_aic_2_init_lt_wr_txns.txt"       , "rd_aic_2_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_3,  aic_3_init_lt     , "wr_aic_3_init_lt_wr_txns.txt"       , "rd_aic_3_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_4,  aic_4_init_lt     , "wr_aic_4_init_lt_wr_txns.txt"       , "rd_aic_4_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_5,  aic_5_init_lt     , "wr_aic_5_init_lt_wr_txns.txt"       , "rd_aic_5_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_6,  aic_6_init_lt     , "wr_aic_6_init_lt_wr_txns.txt"       , "rd_aic_6_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_7,  aic_7_init_lt     , "wr_aic_7_init_lt_wr_txns.txt"       , "rd_aic_7_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 9, 1, 0, 0 )
  // X6 SDMA_HT_LT //
  `DECLARE_AND_BIND_AXI_TRACKER  (sdma_0, sdma_0_init_ht_0  , "wr_sdma_0_init_ht_0_wr_txns.txt"    , "rd_sdma_0_init_ht_0_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (sdma_0, sdma_0_init_ht_1  , "wr_sdma_0_init_ht_1_wr_txns.txt"    , "rd_sdma_0_init_ht_1_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (sdma_0, sdma_0_init_lt    , "wr_sdma_0_init_lt_wr_txns.txt"      , "rd_sdma_0_init_lt_rd_txns.txt"    , 0.83   , 40, 64 , 4, 1, 1, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (sdma_1, sdma_1_init_ht_0  , "wr_sdma_1_init_ht_0_wr_txns.txt"    , "rd_sdma_1_init_ht_0_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (sdma_1, sdma_1_init_ht_1  , "wr_sdma_1_init_ht_1_wr_txns.txt"    , "rd_sdma_1_init_ht_1_rd_txns.txt"  , 0.83   , 40, 512, 8, 1, 1, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (sdma_1, sdma_1_init_lt    , "wr_sdma_1_init_lt_wr_txns.txt"      , "rd_sdma_1_init_lt_rd_txns.txt"    , 0.83   , 40, 64 , 4, 1, 1, 0 )
  // X4 PVE_LT_HT //
  `DECLARE_AND_BIND_AXI_TRACKER  (pve_0, pve_0_init_lt     , "wr_pve_0_init_lt_wr_txns.txt"       , "rd_pve_0_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 8  , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (pve_0, pve_0_init_ht     , "wr_pve_0_init_ht_wr_txns.txt"       , "rd_pve_0_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 11 , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (pve_1, pve_1_init_lt     , "wr_pve_1_init_lt_wr_txns.txt"       , "rd_pve_1_init_lt_rd_txns.txt"     , 0.83   , 40, 64 , 8  , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (pve_1, pve_1_init_ht     , "wr_pve_1_init_ht_wr_txns.txt"       , "rd_pve_1_init_ht_rd_txns.txt"     , 0.83   , 40, 512, 11 , 1, 0, 0 )
  // X3 DCD_MT //
  `DECLARE_AND_BIND_AXI_TRACKER  (dcd_mcu, dcd_dec_0_init_mt , "wr_dcd_dec_0_init_mt_wr_txns.txt"   , "rd_dcd_dec_0_init_mt_rd_txns.txt" , 0.83   , 40, 128, 5  , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (dcd_mcu, dcd_dec_1_init_mt , "wr_dcd_dec_1_init_mt_wr_txns.txt"   , "rd_dcd_dec_1_init_mt_rd_txns.txt" , 0.83   , 40, 128, 5  , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (dcd_mcu, dcd_dec_2_init_mt , "wr_dcd_dec_2_init_mt_wr_txns.txt"   , "rd_dcd_dec_2_init_mt_rd_txns.txt" , 0.83   , 40, 128, 5  , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (dcd_mcu, dcd_mcu_init_lt   , "wr_dcd_mcu_init_lt_wr_txns.txt"     , "rd_dcd_mcu_init_lt_rd_txns.txt"   , 0.83   , 40, 128, 5  , 1, 0, 0 )
  // X2 APU_LT_MT //
  `DECLARE_AND_BIND_AXI_TRACKER  (apu, apu_init_lt       , "wr_apu_init_lt_wr_txns.txt"         , "rd_apu_init_lt_rd_txns.txt"       , 0.83   , 40, 64, 8   , 1, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (apu, apu_init_mt       , "wr_apu_init_mt_wr_txns.txt"         , "rd_apu_init_mt_rd_txns.txt"       , 0.83   , 40, 256, 9  , 1, 0, 0 )
  // X1 PCIE_MT //
  `DECLARE_AND_BIND_AXI_TRACKER  (pcie, pcie_init_mt      , "wr_pcie_init_mt_wr_txns.txt"        , "rd_pcie_init_mt_rd_txns.txt"      , 0.83   , 40, 128, 7  , 1, 0, 1 )
  // X1 SOC_MGMT_LT  //
  `DECLARE_AND_BIND_AXI_TRACKER  (soc_mgmt, soc_mgmt_init_lt  , "wr_soc_mgmt_init_lt_wr_txns.txt"    , "rd_soc_mgmt_init_lt_rd_txns.txt"  , 0.83   , 40, 64, 4   , 1, 0, 0 )
  // X1 SOC_PERIPH_LT //
  `DECLARE_AND_BIND_AXI_TRACKER  (soc_periph, soc_periph_init_lt, "wr_soc_periph_init_lt_wr_txns.txt"  , "rd_soc_mgmt_init_lt_rd_txns.txt"  , 0.83   , 40, 64, 4   , 1, 0, 0 )

  // =============================================================================================================
  // TARG side
  // =============================================================================================================
  // X8 AIC_LT //
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_0, aic_0_targ_lt         , "wr_aic_0_targ_lt_wr_txns.txt"        , "rd_aic_0_targ_lt_rd_txns.txt"         , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_1, aic_1_targ_lt         , "wr_aic_1_targ_lt_wr_txns.txt"        , "rd_aic_1_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_2, aic_2_targ_lt         , "wr_aic_2_targ_lt_wr_txns.txt"        , "rd_aic_2_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_3, aic_3_targ_lt         , "wr_aic_3_targ_lt_wr_txns.txt"        , "rd_aic_3_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_4, aic_4_targ_lt         , "wr_aic_4_targ_lt_wr_txns.txt"        , "rd_aic_4_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_5, aic_5_targ_lt         , "wr_aic_5_targ_lt_wr_txns.txt"        , "rd_aic_5_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_6, aic_6_targ_lt         , "wr_aic_6_targ_lt_wr_txns.txt"        , "rd_aic_6_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  `DECLARE_AND_BIND_AXI_TRACKER  (aic_7, aic_7_targ_lt         , "wr_aic_7_targ_lt_wr_txns.txt"        , "rd_aic_7_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 6, 0, 0, 0 )
  // X2 SDMA_LT
  `DECLARE_AND_BIND_AXI_TRACKER  ( sdma_0, sdma_0_targ_lt        , "wr_sdma_0_targ_lt_wr_txns.txt"       , "rd_sdma_0_targ_lt_rd_txns.txt"       , 0.83 , 40, 64, 4, 0, 1, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( sdma_0, sdma_1_targ_lt        , "wr_sdma_1_targ_lt_wr_txns.txt"       , "rd_sdma_1_targ_lt_rd_txns.txt"       , 0.83 , 40, 64, 4, 0, 1, 0)
  // X2 PVE_LT //
  `DECLARE_AND_BIND_AXI_TRACKER  ( pve_0, pve_0_targ_lt         , "wr_pve_0_targ_lt_wr_txns.txt"        , "rd_pve_0_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( pve_1, pve_1_targ_lt         , "wr_pve_1_targ_lt_wr_txns.txt"        , "rd_pve_1_targ_lt_rd_txns.txt"        , 0.83 , 40, 64, 4, 0, 0, 0)
  // X1 APU_LT
  `DECLARE_AND_BIND_AXI_TRACKER  ( apu, apu_targ_lt           , "wr_apu_targ_lt_wr_txns.txt"          , "rd_apu_targ_lt_rd_txns.txt"          , 0.83 , 40, 64, 10, 0, 0, 0 )
  // X1 SOC_MGMT_LT
  `DECLARE_AND_BIND_AXI_TRACKER  ( soc_mgmt, soc_mgmt_targ_lt      , "wr_soc_mgmt_targ_lt_wr_txns.txt"     , "rd_soc_mgmt_targ_lt_rd_txns.txt"     , 0.83 , 40, 64, 4, 0, 0, 0 )
  // X1 SOC_PERIPH_LT
  `DECLARE_AND_BIND_AXI_TRACKER  ( soc_periph, soc_periph_targ_lt    , "wr_soc_periph_targ_lt_wr_txns.txt"   , "rd_soc_periph_targ_lt_rd_txns.txt"   , 0.83 , 40, 64, 4, 0, 0, 0 )
  // X1 SYS_SPM_LT
  `DECLARE_AND_BIND_AXI_TRACKER  ( sys_spm, sys_spm_targ_lt       , "wr_sys_spm_targ_lt_wr_txns.txt"      , "rd_sys_spm_targ_lt_rd_txns.txt"      , 0.83 , 40, 64, 4, 0, 0, 0 )
  // X4 LPDDR_GRAPH_MT_slv
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_graph_0, lpddr_graph_0_targ_ht , "wr_lpddr_graph_0_targ_ht_wr_txns.txt", "rd_lpddr_graph_0_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_graph_1, lpddr_graph_1_targ_ht , "wr_lpddr_graph_1_targ_ht_wr_txns.txt", "rd_lpddr_graph_1_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_graph_2, lpddr_graph_2_targ_ht , "wr_lpddr_graph_2_targ_ht_wr_txns.txt", "rd_lpddr_graph_2_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_graph_3, lpddr_graph_3_targ_ht , "wr_lpddr_graph_3_targ_ht_wr_txns.txt", "rd_lpddr_graph_3_targ_ht_rd_txns.txt", 0.83 , 40, 256, 8, 0, 0, 0)
  // X2 PCIE_LT_MT // _slv
  `DECLARE_AND_BIND_AXI_TRACKER  ( pcie_targ_cfg_dbi, pcie_targ_cfg_dbi     , "wr_pcie_targ_cfg_dbi_wr_txns.txt"    , "rd_pcie_targ_cfg_dbi_rd_txns.txt"    , 0.83 , 40, 32,  4, 0, 0, 1 )
  `DECLARE_AND_BIND_AXI_TRACKER  ( pcie_targ_mt, pcie_targ_mt          , "wr_pcie_targ_mt_wr_txns.txt"         , "rd_pcie_targ_mt_rd_txns.txt"         , 0.83 , 40, 128, 6, 0, 0, 1 )
  // X8 L2_HT //
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_0, l2_0_targ_ht          , "wr_l2_0_targ_ht_wr_txns.txt"         , "rd_l2_0_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_1, l2_1_targ_ht          , "wr_l2_1_targ_ht_wr_txns.txt"         , "rd_l2_1_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_2, l2_2_targ_ht          , "wr_l2_2_targ_ht_wr_txns.txt"         , "rd_l2_2_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_3, l2_3_targ_ht          , "wr_l2_3_targ_ht_wr_txns.txt"         , "rd_l2_3_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_4, l2_4_targ_ht          , "wr_l2_4_targ_ht_wr_txns.txt"         , "rd_l2_4_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_5, l2_5_targ_ht          , "wr_l2_5_targ_ht_wr_txns.txt"         , "rd_l2_5_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_6, l2_6_targ_ht          , "wr_l2_6_targ_ht_wr_txns.txt"         , "rd_l2_6_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( l2_7, l2_7_targ_ht          , "wr_l2_7_targ_ht_wr_txns.txt"         , "rd_l2_7_targ_ht_rd_txns.txt"         , 0.83 , 40, 512, 4, 0, 0, 0)
  // X4 LPDDR_PPP_HT
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_ppp_0, lpddr_ppp_0_targ_mt   , "wr_lpddr_ppp_0_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_0_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_ppp_1, lpddr_ppp_1_targ_mt   , "wr_lpddr_ppp_1_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_1_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_ppp_2, lpddr_ppp_2_targ_mt   , "wr_lpddr_ppp_2_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_2_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)
  `DECLARE_AND_BIND_AXI_TRACKER  ( lpddr_ppp_3, lpddr_ppp_3_targ_mt   , "wr_lpddr_ppp_3_targ_mt_wr_txns.txt"  , "rd_lpddr_ppp_3_targ_mt_rd_txns.txt"  , 0.83 , 40, 256, 8, 0, 0, 0)

  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
    // Set the reset interface on the virtual sequencer
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(
    uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "*", "vif", axi_if);
    uvm_config_db#(virtual enoc_tb_intf)::set(uvm_root::get(), "*", "tb_intf", tb_intf);
  end

  genvar m;
  generate
    for (m = 0; m < (`NUM_APB3_TARGETS + `NUM_APB4_TARGETS); m++) begin : APB_INTF_PASSING
      initial begin
        enoc_apb_targs_e enoc_targ;
        enoc_targ = enoc_apb_targs_e'(m);
        uvm_config_db#(svt_apb_vif)::set(uvm_root::get(), $sformatf("uvm_test_top.env.apb_system_env_%s",enoc_targ.name()), "vif", apb_if[m]);
      end
    end
  endgenerate

  // =============================================================================================================
  // Invoking the test
  // Run test
  // =============================================================================================================
  initial
  begin
    run_test ();
  end

endmodule : hdl_top

