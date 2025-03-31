`define AXI_VIP


`define CVA6V_PATH hdl_top.dut.u_ai_core_cva6v
module hdl_top;
  // Time unit and precision
  timeunit      1ns;
  timeprecision 1ns;

  `include "../uvm/env/ai_core_infra_tb_define.svh"
  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import ai_core_infra_test_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  //`include "axi4pc/bind_ai_core_infra.svh"

  // Clock and reset signals
  logic                               clk;
  bit                                 rst_n;
  bit [11:0]                          core_id;
  logic                               clk_en;
  int 				                  aic_infra_freq_mhz = 1200;
  time 			                      aic_infra_tol_ps   = 10;

  // =============================================================================================================
  // Instantiate interfaces and BFMs and assignments
  // =============================================================================================================
  // TB Interface instance to provide access to the reset signal
  axi_reset_if axi_reset_if ();
  assign axi_reset_if.clk = clk;
  assign rst_n            = axi_reset_if.reset;

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
  svt_axi_if   axi_if ();

  // =============================================================================================================
  // CLK RST & Assertion Instantitation
  // =============================================================================================================
  axe_clk_generator u_axe_clk_generator(
    .i_enable ( clk_en ) ,
    .o_clk    ( clk    )
  );

  axe_clk_assert u_axe_clk_assert(
    .clk        ( clk                  ) ,
    .rst_n      ( rst_n                ) ,
    .freq_mhz   ( aic_infra_freq_mhz   ) ,
    .tol_ps     ( aic_infra_tol_ps     )
  );

  assign axi_if.common_aclk = clk;;
  genvar i;
  generate
    for (i=0; i < `SLV_NUM; i++) begin
      assign axi_if.slave_if[i].aresetn = rst_n;
      assign axi_if.slave_if[i].aclk    = clk;
    end

    for (i=0; i < `MST_NUM; i++) begin
      assign axi_if.master_if[i].aresetn = rst_n;
      assign axi_if.master_if[i].aclk    = clk;
    end
  endgenerate

  //dut instantiation
  aic_infra dut (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_scan_en(1'b0),
    .i_cid(core_id),  // ID of AI Core
    .o_reserved(),    // backup pins for HOTFIX
    .i_inter_core_sync(0),
    .i_thermal_warning_async(0),
    .i_reserved('0),  // backup pins for HOTFIX
    //--------------------------------------------------
    // Obervability
    //--------------------------------------------------
    .i_mvm_exe_obs('0),
    .i_mvm_prg_obs('0),
    .i_m_iau_obs('0),
    .i_m_dpu_obs('0),
    .i_tu_obs('0),
    .i_dwpu_obs('0),
    .i_d_iau_obs('0),
    .i_d_dpu_obs('0),
    .i_dmc_obs('0),
    .o_aic_obs(),   // ai_core observability pins //output

    ///// Timestamp:
    .i_dmc_ts_start('0),
    .i_dmc_ts_end('0),
    .i_did_ts_start('0),
    .i_did_ts_end('0),
    .i_mid_ts_start('0),
    .i_mid_ts_end('0),
    ///// ACD sync:
    .i_dmc_acd_sync('0),
    .i_did_acd_sync('0),
    .i_mid_acd_sync('0),

    // CVA6 Core ctrl and debug interface //
    .i_cva6v_boot_addr('0),
    .i_cva6v_debug_req_async('0),
    .i_cva6v_debug_rst_halt_req_async('0),
    .i_mtip_async('0),
    .i_msip_async('0),

    // infra AXI HP dlock
    // .infra_hp_dlock(),
    // infra AXI LP dlock
    //.infra_lp_dlock(),

    //--------------------------------------------------
    // Core ctrl interface
    //--------------------------------------------------
    // TODO: CVA6 interface requirements
    // RVV part:
    .o_rvv_0_req_valid(),
    .i_rvv_0_req_ready(8'b0000_0000),
    .o_rvv_0_req_addr(),
    .o_rvv_0_req_we(),
    .o_rvv_0_req_be(),
    .o_rvv_0_req_wdata(),
    .i_rvv_0_res_valid(8'b0000_0000),
    .i_rvv_0_res_rdata('0),
    .i_rvv_0_res_err(8'b0000_0000),

    .o_rvv_1_req_valid(),
    .i_rvv_1_req_ready(8'b0000_0000),
    .o_rvv_1_req_addr(),
    .o_rvv_1_req_we(),
    .o_rvv_1_req_be(),
    .o_rvv_1_req_wdata(),
    .i_rvv_1_res_valid(8'b0000_0000),
    .i_rvv_1_res_rdata('0),
    .i_rvv_1_res_err(8'b0000_0000),

    .o_rvv_2_req_valid(),
    .i_rvv_2_req_ready(8'b0000_0000),
    .o_rvv_2_req_addr(),
    .o_rvv_2_req_we(),
    .o_rvv_2_req_be(),
    .o_rvv_2_req_wdata(),
    .i_rvv_2_res_valid(8'b0000_0000),
    .i_rvv_2_res_rdata('0),
    .i_rvv_2_res_err(8'b0000_0000),

    .o_rvv_3_req_valid(),
    .i_rvv_3_req_ready(8'b0000_0000),
    .o_rvv_3_req_addr(),
    .o_rvv_3_req_we(),
    .o_rvv_3_req_be(),
    .o_rvv_3_req_wdata(),
    .i_rvv_3_res_valid(8'b0000_0000),
    .i_rvv_3_res_rdata('0),
    .i_rvv_3_res_err(8'b0000_0000),

    .o_rvv_4_req_valid(),
    .i_rvv_4_req_ready(8'b0000_0000),
    .o_rvv_4_req_addr(),
    .o_rvv_4_req_we(),
    .o_rvv_4_req_be(),
    .o_rvv_4_req_wdata(),
    .i_rvv_4_res_valid(8'b0000_0000),
    .i_rvv_4_res_rdata('0),
    .i_rvv_4_res_err(8'b0000_0000),

    .o_rvv_5_req_valid(),
    .i_rvv_5_req_ready(8'b0000_0000),
    .o_rvv_5_req_addr(),
    .o_rvv_5_req_we(),
    .o_rvv_5_req_be(),
    .o_rvv_5_req_wdata(),
    .i_rvv_5_res_valid(8'b0000_0000),
    .i_rvv_5_res_rdata('0),
    .i_rvv_5_res_err(8'b0000_0000),

    .o_rvv_6_req_valid(),
    .i_rvv_6_req_ready(8'b0000_0000),
    .o_rvv_6_req_addr(),
    .o_rvv_6_req_we(),
    .o_rvv_6_req_be(),
    .o_rvv_6_req_wdata(),
    .i_rvv_6_res_valid(8'b0000_0000),
    .i_rvv_6_res_rdata('0),
    .i_rvv_6_res_err(8'b0000_0000),

    .o_rvv_7_req_valid(),
    .i_rvv_7_req_ready(8'b0000_0000),
    .o_rvv_7_req_addr(),
    .o_rvv_7_req_we(),
    .o_rvv_7_req_be(),
    .o_rvv_7_req_wdata(),
    .i_rvv_7_res_valid(8'b0000_0000),
    .i_rvv_7_res_rdata('0),
    .i_rvv_7_res_err(8'b0000_0000),

    //--------------------------------------------------
    // IRQ ai_core subips
    //--------------------------------------------------
    .i_irq_dmc('h0),
    .i_irq_aic_mid('h0),
    .i_irq_aic_did('h0),

    `connect_master_axi_interface(noc_lt, noc_lt_s)

    //external interfaces
    `connect_slave_axi_interface(noc_ht, noc_ht)
    `connect_slave_axi_interface(noc_lt, noc_lt)
    `connect_slave_axi_interface(dmc_l1_ht, dmc_l1_ht)
    `connect_slave_axi_interface_slim(dmc_l1_lt, dmc_l1_lt)

    //--------------------------------------------------
    //SRAM config signals
    //--------------------------------------------------
    /// Margin adjustment control selection
    .i_sram_mcs('h1),
    /// Margin adjustment control selection write
    .i_sram_mcsw('h0),
    /// Retention mode enable input pin (power gating)
    .i_sram_ret('h0),
    /// Power down enable, active high (power gating)
    .i_sram_pde('h0),
    /// Scan enable, active high
    .i_sram_se('h0),
    /// Margin adjustment for urbance margin enhancement (Vmin Feature Control Pins)
    .i_sram_adme('h4),
    /// Power up ready negative
    .o_sram_prn()


  );
  initial begin
     force `CVA6V_PATH.o_axi_m_araddr  = axi_if.master_if[u_ai_core_cva6v].araddr;
     force `CVA6V_PATH.o_axi_m_arburst = axi_if.master_if[u_ai_core_cva6v].arburst;
     force `CVA6V_PATH.o_axi_m_arcache = axi_if.master_if[u_ai_core_cva6v].arcache;
     force `CVA6V_PATH.o_axi_m_arid    = axi_if.master_if[u_ai_core_cva6v].arid;
     force `CVA6V_PATH.o_axi_m_arlen   = axi_if.master_if[u_ai_core_cva6v].arlen;
     force `CVA6V_PATH.o_axi_m_arlock  = axi_if.master_if[u_ai_core_cva6v].arlock;
     force `CVA6V_PATH.o_axi_m_arprot  = axi_if.master_if[u_ai_core_cva6v].arprot;
     force `CVA6V_PATH.o_axi_m_arsize  = axi_if.master_if[u_ai_core_cva6v].arsize;
     force `CVA6V_PATH.o_axi_m_arvalid = axi_if.master_if[u_ai_core_cva6v].arvalid;
     force `CVA6V_PATH.o_axi_m_awaddr  = axi_if.master_if[u_ai_core_cva6v].awaddr;
     force `CVA6V_PATH.o_axi_m_awburst = axi_if.master_if[u_ai_core_cva6v].awburst;
     force `CVA6V_PATH.o_axi_m_awcache = axi_if.master_if[u_ai_core_cva6v].awcache;
     force `CVA6V_PATH.o_axi_m_awid    = axi_if.master_if[u_ai_core_cva6v].awid;
     force `CVA6V_PATH.o_axi_m_awlen   = axi_if.master_if[u_ai_core_cva6v].awlen;
     force `CVA6V_PATH.o_axi_m_awlock  = axi_if.master_if[u_ai_core_cva6v].awlock;
     force `CVA6V_PATH.o_axi_m_awprot  = axi_if.master_if[u_ai_core_cva6v].awprot;
     force `CVA6V_PATH.o_axi_m_awsize  = axi_if.master_if[u_ai_core_cva6v].awsize;
     force `CVA6V_PATH.o_axi_m_awvalid = axi_if.master_if[u_ai_core_cva6v].awvalid;
     force `CVA6V_PATH.o_axi_m_bready  = axi_if.master_if[u_ai_core_cva6v].bready;
     force `CVA6V_PATH.o_axi_m_rready  = axi_if.master_if[u_ai_core_cva6v].rready;
     force `CVA6V_PATH.o_axi_m_wdata   = axi_if.master_if[u_ai_core_cva6v].wdata;
     force `CVA6V_PATH.o_axi_m_wlast   = axi_if.master_if[u_ai_core_cva6v].wlast;
     force `CVA6V_PATH.o_axi_m_wstrb   = axi_if.master_if[u_ai_core_cva6v].wstrb;
     force `CVA6V_PATH.o_axi_m_wvalid  = axi_if.master_if[u_ai_core_cva6v].wvalid;

     force axi_if.master_if[u_ai_core_cva6v].arready = `CVA6V_PATH.i_axi_m_arready;
     force axi_if.master_if[u_ai_core_cva6v].awready = `CVA6V_PATH.i_axi_m_awready;
     force axi_if.master_if[u_ai_core_cva6v].wready  = `CVA6V_PATH.i_axi_m_wready ;
     force axi_if.master_if[u_ai_core_cva6v].rresp   = `CVA6V_PATH.i_axi_m_rresp  ;
     force axi_if.master_if[u_ai_core_cva6v].rvalid  = `CVA6V_PATH.i_axi_m_rvalid ;
     force axi_if.master_if[u_ai_core_cva6v].bresp   = `CVA6V_PATH.i_axi_m_bresp  ;
     force axi_if.master_if[u_ai_core_cva6v].bvalid  = `CVA6V_PATH.i_axi_m_bvalid ;
     force axi_if.master_if[u_ai_core_cva6v].rdata   = `CVA6V_PATH.i_axi_m_rdata  ;
     force axi_if.master_if[u_ai_core_cva6v].rid     = `CVA6V_PATH.i_axi_m_rid    ;
     force axi_if.master_if[u_ai_core_cva6v].rlast   = `CVA6V_PATH.i_axi_m_rlast  ;
     force axi_if.master_if[u_ai_core_cva6v].bid     = `CVA6V_PATH.i_axi_m_bid    ;
   end

  assign axi_if.slave_if[dmc_l1_lt].awlock  = 0;
  assign axi_if.slave_if[dmc_l1_lt].awcache = 0;
  assign axi_if.slave_if[dmc_l1_lt].awprot  = 0;
  assign axi_if.slave_if[dmc_l1_lt].arlock  = 0;
  assign axi_if.slave_if[dmc_l1_lt].arcache = 0;
  assign axi_if.slave_if[dmc_l1_lt].arprot  = 0;

  assign axi_if.slave_if[u_aic_csr_reg_top].awid    = dut.u_aic_csr_reg_top.axi_aw_i.id;
  assign axi_if.slave_if[u_aic_csr_reg_top].awaddr  = dut.u_aic_csr_reg_top.axi_aw_i.addr;
  assign axi_if.slave_if[u_aic_csr_reg_top].awlen   = dut.u_aic_csr_reg_top.axi_aw_i.len;
  assign axi_if.slave_if[u_aic_csr_reg_top].awsize  = dut.u_aic_csr_reg_top.axi_aw_i.size;
  assign axi_if.slave_if[u_aic_csr_reg_top].awburst = dut.u_aic_csr_reg_top.axi_aw_i.burst;
  assign axi_if.slave_if[u_aic_csr_reg_top].awvalid = dut.u_aic_csr_reg_top.axi_aw_i.valid;
  assign axi_if.slave_if[u_aic_csr_reg_top].awready = dut.u_aic_csr_reg_top.axi_awready;
  assign axi_if.slave_if[u_aic_csr_reg_top].arid    = dut.u_aic_csr_reg_top.axi_ar_i.id;
  assign axi_if.slave_if[u_aic_csr_reg_top].araddr  = dut.u_aic_csr_reg_top.axi_ar_i.addr;
  assign axi_if.slave_if[u_aic_csr_reg_top].arlen   = dut.u_aic_csr_reg_top.axi_ar_i.len;
  assign axi_if.slave_if[u_aic_csr_reg_top].arsize  = dut.u_aic_csr_reg_top.axi_ar_i.size;
  assign axi_if.slave_if[u_aic_csr_reg_top].arburst = dut.u_aic_csr_reg_top.axi_ar_i.burst;
  assign axi_if.slave_if[u_aic_csr_reg_top].arvalid = dut.u_aic_csr_reg_top.axi_ar_i.valid;
  assign axi_if.slave_if[u_aic_csr_reg_top].arready = dut.u_aic_csr_reg_top.axi_arready;
  assign axi_if.slave_if[u_aic_csr_reg_top].wdata   = dut.u_aic_csr_reg_top.axi_w_i.data;
  assign axi_if.slave_if[u_aic_csr_reg_top].wstrb   = dut.u_aic_csr_reg_top.axi_w_i.strb;
  assign axi_if.slave_if[u_aic_csr_reg_top].wlast   = dut.u_aic_csr_reg_top.axi_w_i.last;
  assign axi_if.slave_if[u_aic_csr_reg_top].wvalid  = dut.u_aic_csr_reg_top.axi_w_i.valid;
  assign axi_if.slave_if[u_aic_csr_reg_top].wready  = dut.u_aic_csr_reg_top.axi_wready;
  assign axi_if.slave_if[u_aic_csr_reg_top].rid     = dut.u_aic_csr_reg_top.axi_r_o.id;
  assign axi_if.slave_if[u_aic_csr_reg_top].rdata   = dut.u_aic_csr_reg_top.axi_r_o.data;
  assign axi_if.slave_if[u_aic_csr_reg_top].rresp   = dut.u_aic_csr_reg_top.axi_r_o.resp;
  assign axi_if.slave_if[u_aic_csr_reg_top].rlast   = dut.u_aic_csr_reg_top.axi_r_o.last;
  assign axi_if.slave_if[u_aic_csr_reg_top].rvalid  = dut.u_aic_csr_reg_top.axi_r_o.valid;
  assign axi_if.slave_if[u_aic_csr_reg_top].rready  = dut.u_aic_csr_reg_top.axi_rready;
  assign axi_if.slave_if[u_aic_csr_reg_top].bid     = dut.u_aic_csr_reg_top.axi_b_o.id;
  assign axi_if.slave_if[u_aic_csr_reg_top].bresp   = dut.u_aic_csr_reg_top.axi_b_o.resp;
  assign axi_if.slave_if[u_aic_csr_reg_top].bvalid  = dut.u_aic_csr_reg_top.axi_b_o.valid;
  assign axi_if.slave_if[u_aic_csr_reg_top].bready  = dut.u_aic_csr_reg_top.axi_bready;
  assign axi_if.slave_if[u_aic_csr_reg_top].awlock  = 0;
  assign axi_if.slave_if[u_aic_csr_reg_top].awcache = 0;
  assign axi_if.slave_if[u_aic_csr_reg_top].awprot  = 0;
  assign axi_if.slave_if[u_aic_csr_reg_top].arlock  = 0;
  assign axi_if.slave_if[u_aic_csr_reg_top].arcache = 0;
  assign axi_if.slave_if[u_aic_csr_reg_top].arprot  = 0;

  assign axi_if.slave_if[u_aic_rv_plic].awid    = dut.u_aic_rv_plic.axi_aw_i.id;
  assign axi_if.slave_if[u_aic_rv_plic].awaddr  = dut.u_aic_rv_plic.axi_aw_i.addr;
  assign axi_if.slave_if[u_aic_rv_plic].awlen   = dut.u_aic_rv_plic.axi_aw_i.len;
  assign axi_if.slave_if[u_aic_rv_plic].awsize  = dut.u_aic_rv_plic.axi_aw_i.size;
  assign axi_if.slave_if[u_aic_rv_plic].awburst = dut.u_aic_rv_plic.axi_aw_i.burst;
  assign axi_if.slave_if[u_aic_rv_plic].awvalid = dut.u_aic_rv_plic.axi_aw_i.valid;
  assign axi_if.slave_if[u_aic_rv_plic].awready = dut.u_aic_rv_plic.axi_awready;
  assign axi_if.slave_if[u_aic_rv_plic].arid    = dut.u_aic_rv_plic.axi_ar_i.id;
  assign axi_if.slave_if[u_aic_rv_plic].araddr  = dut.u_aic_rv_plic.axi_ar_i.addr;
  assign axi_if.slave_if[u_aic_rv_plic].arlen   = dut.u_aic_rv_plic.axi_ar_i.len;
  assign axi_if.slave_if[u_aic_rv_plic].arsize  = dut.u_aic_rv_plic.axi_ar_i.size;
  assign axi_if.slave_if[u_aic_rv_plic].arburst = dut.u_aic_rv_plic.axi_ar_i.burst;
  assign axi_if.slave_if[u_aic_rv_plic].arvalid = dut.u_aic_rv_plic.axi_ar_i.valid;
  assign axi_if.slave_if[u_aic_rv_plic].arready = dut.u_aic_rv_plic.axi_arready;
  assign axi_if.slave_if[u_aic_rv_plic].wdata   = dut.u_aic_rv_plic.axi_w_i.data;
  assign axi_if.slave_if[u_aic_rv_plic].wstrb   = dut.u_aic_rv_plic.axi_w_i.strb;
  assign axi_if.slave_if[u_aic_rv_plic].wlast   = dut.u_aic_rv_plic.axi_w_i.last;
  assign axi_if.slave_if[u_aic_rv_plic].wvalid  = dut.u_aic_rv_plic.axi_w_i.valid;
  assign axi_if.slave_if[u_aic_rv_plic].wready  = dut.u_aic_rv_plic.axi_wready;
  assign axi_if.slave_if[u_aic_rv_plic].rid     = dut.u_aic_rv_plic.axi_r_o.id;
  assign axi_if.slave_if[u_aic_rv_plic].rdata   = dut.u_aic_rv_plic.axi_r_o.data;
  assign axi_if.slave_if[u_aic_rv_plic].rresp   = dut.u_aic_rv_plic.axi_r_o.resp;
  assign axi_if.slave_if[u_aic_rv_plic].rlast   = dut.u_aic_rv_plic.axi_r_o.last;
  assign axi_if.slave_if[u_aic_rv_plic].rvalid  = dut.u_aic_rv_plic.axi_r_o.valid;
  assign axi_if.slave_if[u_aic_rv_plic].rready  = dut.u_aic_rv_plic.axi_rready;
  assign axi_if.slave_if[u_aic_rv_plic].bid     = dut.u_aic_rv_plic.axi_b_o.id;
  assign axi_if.slave_if[u_aic_rv_plic].bresp   = dut.u_aic_rv_plic.axi_b_o.resp;
  assign axi_if.slave_if[u_aic_rv_plic].bvalid  = dut.u_aic_rv_plic.axi_b_o.valid;
  assign axi_if.slave_if[u_aic_rv_plic].bready  = dut.u_aic_rv_plic.axi_bready;
  assign axi_if.slave_if[u_aic_rv_plic].awlock  = 0;
  assign axi_if.slave_if[u_aic_rv_plic].awcache = 0;
  assign axi_if.slave_if[u_aic_rv_plic].awprot  = 0;
  assign axi_if.slave_if[u_aic_rv_plic].arlock  = 0;
  assign axi_if.slave_if[u_aic_rv_plic].arcache = 0;
  assign axi_if.slave_if[u_aic_rv_plic].arprot  = 0;


  assign axi_if.slave_if[u_aic_spm].awvalid = dut.u_aic_spm.i_axi_s_awvalid;
  assign axi_if.slave_if[u_aic_spm].awaddr  = dut.u_aic_spm.i_axi_s_awaddr;
  assign axi_if.slave_if[u_aic_spm].awid    = dut.u_aic_spm.i_axi_s_awid;
  assign axi_if.slave_if[u_aic_spm].awlen   = dut.u_aic_spm.i_axi_s_awlen;
  assign axi_if.slave_if[u_aic_spm].awsize  = dut.u_aic_spm.i_axi_s_awsize;
  assign axi_if.slave_if[u_aic_spm].awburst = dut.u_aic_spm.i_axi_s_awburst;
  assign axi_if.slave_if[u_aic_spm].awlock  = dut.u_aic_spm.i_axi_s_awlock;
  assign axi_if.slave_if[u_aic_spm].awcache = dut.u_aic_spm.i_axi_s_awcache;
  assign axi_if.slave_if[u_aic_spm].awprot  = dut.u_aic_spm.i_axi_s_awprot;
  assign axi_if.slave_if[u_aic_spm].awready = dut.u_aic_spm.o_axi_s_awready;
  assign axi_if.slave_if[u_aic_spm].wvalid  = dut.u_aic_spm.i_axi_s_wvalid;
  assign axi_if.slave_if[u_aic_spm].wlast   = dut.u_aic_spm.i_axi_s_wlast;
  assign axi_if.slave_if[u_aic_spm].wstrb   = dut.u_aic_spm.i_axi_s_wstrb;
  assign axi_if.slave_if[u_aic_spm].wdata   = dut.u_aic_spm.i_axi_s_wdata;
  assign axi_if.slave_if[u_aic_spm].wready  = dut.u_aic_spm.o_axi_s_wready;
  assign axi_if.slave_if[u_aic_spm].bvalid  = dut.u_aic_spm.o_axi_s_bvalid;
  assign axi_if.slave_if[u_aic_spm].bid     = dut.u_aic_spm.o_axi_s_bid;
  assign axi_if.slave_if[u_aic_spm].bresp   = dut.u_aic_spm.o_axi_s_bresp;
  assign axi_if.slave_if[u_aic_spm].bready  = dut.u_aic_spm.i_axi_s_bready;
  assign axi_if.slave_if[u_aic_spm].arvalid = dut.u_aic_spm.i_axi_s_arvalid;
  assign axi_if.slave_if[u_aic_spm].araddr  = dut.u_aic_spm.i_axi_s_araddr;
  assign axi_if.slave_if[u_aic_spm].arid    = dut.u_aic_spm.i_axi_s_arid;
  assign axi_if.slave_if[u_aic_spm].arlen   = dut.u_aic_spm.i_axi_s_arlen;
  assign axi_if.slave_if[u_aic_spm].arsize  = dut.u_aic_spm.i_axi_s_arsize;
  assign axi_if.slave_if[u_aic_spm].arburst = dut.u_aic_spm.i_axi_s_arburst;
  assign axi_if.slave_if[u_aic_spm].arlock  = dut.u_aic_spm.i_axi_s_arlock;
  assign axi_if.slave_if[u_aic_spm].arcache = dut.u_aic_spm.i_axi_s_arcache;
  assign axi_if.slave_if[u_aic_spm].arprot  = dut.u_aic_spm.i_axi_s_arprot;
  assign axi_if.slave_if[u_aic_spm].arready = dut.u_aic_spm.o_axi_s_arready;
  assign axi_if.slave_if[u_aic_spm].rvalid  = dut.u_aic_spm.o_axi_s_rvalid;
  assign axi_if.slave_if[u_aic_spm].rlast   = dut.u_aic_spm.o_axi_s_rlast;
  assign axi_if.slave_if[u_aic_spm].rid     = dut.u_aic_spm.o_axi_s_rid;
  assign axi_if.slave_if[u_aic_spm].rdata   = dut.u_aic_spm.o_axi_s_rdata;
  assign axi_if.slave_if[u_aic_spm].rresp   = dut.u_aic_spm.o_axi_s_rresp;
  assign axi_if.slave_if[u_aic_spm].rready  = dut.u_aic_spm.i_axi_s_rready;

  assign axi_if.slave_if[u_axi_mailbox].awid    = dut.u_axi_mailbox.i_axi_s_aw.id;
  assign axi_if.slave_if[u_axi_mailbox].awaddr  = dut.u_axi_mailbox.i_axi_s_aw.addr;
  assign axi_if.slave_if[u_axi_mailbox].awlen   = dut.u_axi_mailbox.i_axi_s_aw.len;
  assign axi_if.slave_if[u_axi_mailbox].awsize  = dut.u_axi_mailbox.i_axi_s_aw.size;
  assign axi_if.slave_if[u_axi_mailbox].awburst = dut.u_axi_mailbox.i_axi_s_aw.burst;
  assign axi_if.slave_if[u_axi_mailbox].awvalid = dut.u_axi_mailbox.i_axi_s_aw.valid;
  assign axi_if.slave_if[u_axi_mailbox].awready = dut.u_axi_mailbox.o_axi_s_aw_ready;
  assign axi_if.slave_if[u_axi_mailbox].arid    = dut.u_axi_mailbox.i_axi_s_ar.id;
  assign axi_if.slave_if[u_axi_mailbox].araddr  = dut.u_axi_mailbox.i_axi_s_ar.addr;
  assign axi_if.slave_if[u_axi_mailbox].arlen   = dut.u_axi_mailbox.i_axi_s_ar.len;
  assign axi_if.slave_if[u_axi_mailbox].arsize  = dut.u_axi_mailbox.i_axi_s_ar.size;
  assign axi_if.slave_if[u_axi_mailbox].arburst = dut.u_axi_mailbox.i_axi_s_ar.burst;
  assign axi_if.slave_if[u_axi_mailbox].arvalid = dut.u_axi_mailbox.i_axi_s_ar.valid;
  assign axi_if.slave_if[u_axi_mailbox].arready = dut.u_axi_mailbox.o_axi_s_ar_ready;
  assign axi_if.slave_if[u_axi_mailbox].wdata   = dut.u_axi_mailbox.i_axi_s_w.data;
  assign axi_if.slave_if[u_axi_mailbox].wstrb   = dut.u_axi_mailbox.i_axi_s_w.strb;
  assign axi_if.slave_if[u_axi_mailbox].wlast   = dut.u_axi_mailbox.i_axi_s_w.last;
  assign axi_if.slave_if[u_axi_mailbox].wvalid  = dut.u_axi_mailbox.i_axi_s_w.valid;
  assign axi_if.slave_if[u_axi_mailbox].wready  = dut.u_axi_mailbox.o_axi_s_w_ready;
  assign axi_if.slave_if[u_axi_mailbox].rid     = dut.u_axi_mailbox.o_axi_s_r.id;
  assign axi_if.slave_if[u_axi_mailbox].rdata   = dut.u_axi_mailbox.o_axi_s_r.data;
  assign axi_if.slave_if[u_axi_mailbox].rresp   = dut.u_axi_mailbox.o_axi_s_r.resp;
  assign axi_if.slave_if[u_axi_mailbox].rlast   = dut.u_axi_mailbox.o_axi_s_r.last;
  assign axi_if.slave_if[u_axi_mailbox].rvalid  = dut.u_axi_mailbox.o_axi_s_r.valid;
  assign axi_if.slave_if[u_axi_mailbox].rready  = dut.u_axi_mailbox.i_axi_s_r_ready;
  assign axi_if.slave_if[u_axi_mailbox].bid     = dut.u_axi_mailbox.o_axi_s_b.id;
  assign axi_if.slave_if[u_axi_mailbox].bresp   = dut.u_axi_mailbox.o_axi_s_b.resp;
  assign axi_if.slave_if[u_axi_mailbox].bvalid  = dut.u_axi_mailbox.o_axi_s_b.valid;
  assign axi_if.slave_if[u_axi_mailbox].bready  = dut.u_axi_mailbox.i_axi_s_b_ready;
  assign axi_if.slave_if[u_axi_mailbox].awlock  = 0;
  assign axi_if.slave_if[u_axi_mailbox].awcache = 0;
  assign axi_if.slave_if[u_axi_mailbox].awprot  = 0;
  assign axi_if.slave_if[u_axi_mailbox].arlock  = 0;
  assign axi_if.slave_if[u_axi_mailbox].arcache = 0;
  assign axi_if.slave_if[u_axi_mailbox].arprot  = 0;


  assign axi_if.slave_if[u_ht_aic_dma].awvalid = dut.u_ht_aic_dma.i_axi_s_awvalid;
  assign axi_if.slave_if[u_ht_aic_dma].awaddr  = dut.u_ht_aic_dma.i_axi_s_awaddr;
  assign axi_if.slave_if[u_ht_aic_dma].awid    = dut.u_ht_aic_dma.i_axi_s_awid;
  assign axi_if.slave_if[u_ht_aic_dma].awlen   = dut.u_ht_aic_dma.i_axi_s_awlen;
  assign axi_if.slave_if[u_ht_aic_dma].awsize  = dut.u_ht_aic_dma.i_axi_s_awsize;
  assign axi_if.slave_if[u_ht_aic_dma].awburst = dut.u_ht_aic_dma.i_axi_s_awburst;
  assign axi_if.slave_if[u_ht_aic_dma].awready = dut.u_ht_aic_dma.o_axi_s_awready;
  assign axi_if.slave_if[u_ht_aic_dma].wvalid  = dut.u_ht_aic_dma.i_axi_s_wvalid;
  assign axi_if.slave_if[u_ht_aic_dma].wlast   = dut.u_ht_aic_dma.i_axi_s_wlast;
  assign axi_if.slave_if[u_ht_aic_dma].wstrb   = dut.u_ht_aic_dma.i_axi_s_wstrb;
  assign axi_if.slave_if[u_ht_aic_dma].wdata   = dut.u_ht_aic_dma.i_axi_s_wdata;
  assign axi_if.slave_if[u_ht_aic_dma].wready  = dut.u_ht_aic_dma.o_axi_s_wready;
  assign axi_if.slave_if[u_ht_aic_dma].bvalid  = dut.u_ht_aic_dma.o_axi_s_bvalid;
  assign axi_if.slave_if[u_ht_aic_dma].bid     = dut.u_ht_aic_dma.o_axi_s_bid;
  assign axi_if.slave_if[u_ht_aic_dma].bresp   = dut.u_ht_aic_dma.o_axi_s_bresp;
  assign axi_if.slave_if[u_ht_aic_dma].bready  = dut.u_ht_aic_dma.i_axi_s_bready;
  assign axi_if.slave_if[u_ht_aic_dma].arvalid = dut.u_ht_aic_dma.i_axi_s_arvalid;
  assign axi_if.slave_if[u_ht_aic_dma].araddr  = dut.u_ht_aic_dma.i_axi_s_araddr;
  assign axi_if.slave_if[u_ht_aic_dma].arid    = dut.u_ht_aic_dma.i_axi_s_arid;
  assign axi_if.slave_if[u_ht_aic_dma].arlen   = dut.u_ht_aic_dma.i_axi_s_arlen;
  assign axi_if.slave_if[u_ht_aic_dma].arsize  = dut.u_ht_aic_dma.i_axi_s_arsize;
  assign axi_if.slave_if[u_ht_aic_dma].arburst = dut.u_ht_aic_dma.i_axi_s_arburst;
  assign axi_if.slave_if[u_ht_aic_dma].arready = dut.u_ht_aic_dma.o_axi_s_arready;
  assign axi_if.slave_if[u_ht_aic_dma].rvalid  = dut.u_ht_aic_dma.o_axi_s_rvalid;
  assign axi_if.slave_if[u_ht_aic_dma].rlast   = dut.u_ht_aic_dma.o_axi_s_rlast;
  assign axi_if.slave_if[u_ht_aic_dma].rid     = dut.u_ht_aic_dma.o_axi_s_rid;
  assign axi_if.slave_if[u_ht_aic_dma].rdata   = dut.u_ht_aic_dma.o_axi_s_rdata;
  assign axi_if.slave_if[u_ht_aic_dma].rresp   = dut.u_ht_aic_dma.o_axi_s_rresp;
  assign axi_if.slave_if[u_ht_aic_dma].rready  = dut.u_ht_aic_dma.i_axi_s_rready;
  assign axi_if.slave_if[u_ht_aic_dma].awlock  = 0;
  assign axi_if.slave_if[u_ht_aic_dma].awcache = 0;
  assign axi_if.slave_if[u_ht_aic_dma].awprot  = 0;
  assign axi_if.slave_if[u_ht_aic_dma].arlock  = 0;
  assign axi_if.slave_if[u_ht_aic_dma].arcache = 0;
  assign axi_if.slave_if[u_ht_aic_dma].arprot  = 0;

  assign axi_if.slave_if[u_lt_aic_dma].awvalid = dut.u_lt_aic_dma.i_awvalid;
  assign axi_if.slave_if[u_lt_aic_dma].awaddr  = dut.u_lt_aic_dma.i_awaddr;
  assign axi_if.slave_if[u_lt_aic_dma].awid    = dut.u_lt_aic_dma.i_awid;
  assign axi_if.slave_if[u_lt_aic_dma].awlen   = dut.u_lt_aic_dma.i_awlen;
  assign axi_if.slave_if[u_lt_aic_dma].awsize  = dut.u_lt_aic_dma.i_awsize;
  assign axi_if.slave_if[u_lt_aic_dma].awburst = dut.u_lt_aic_dma.i_awburst;
  assign axi_if.slave_if[u_lt_aic_dma].awready = dut.u_lt_aic_dma.o_awready;
  assign axi_if.slave_if[u_lt_aic_dma].wvalid  = dut.u_lt_aic_dma.i_wvalid;
  assign axi_if.slave_if[u_lt_aic_dma].wlast   = dut.u_lt_aic_dma.i_wlast;
  assign axi_if.slave_if[u_lt_aic_dma].wstrb   = dut.u_lt_aic_dma.i_wstrb;
  assign axi_if.slave_if[u_lt_aic_dma].wdata   = dut.u_lt_aic_dma.i_wdata;
  assign axi_if.slave_if[u_lt_aic_dma].wready  = dut.u_lt_aic_dma.o_wready;
  assign axi_if.slave_if[u_lt_aic_dma].bvalid  = dut.u_lt_aic_dma.o_bvalid;
  assign axi_if.slave_if[u_lt_aic_dma].bid     = dut.u_lt_aic_dma.o_bid;
  assign axi_if.slave_if[u_lt_aic_dma].bresp   = dut.u_lt_aic_dma.o_bresp;
  assign axi_if.slave_if[u_lt_aic_dma].bready  = dut.u_lt_aic_dma.i_bready;
  assign axi_if.slave_if[u_lt_aic_dma].arvalid = dut.u_lt_aic_dma.i_arvalid;
  assign axi_if.slave_if[u_lt_aic_dma].araddr  = dut.u_lt_aic_dma.i_araddr;
  assign axi_if.slave_if[u_lt_aic_dma].arid    = dut.u_lt_aic_dma.i_arid;
  assign axi_if.slave_if[u_lt_aic_dma].arlen   = dut.u_lt_aic_dma.i_arlen;
  assign axi_if.slave_if[u_lt_aic_dma].arsize  = dut.u_lt_aic_dma.i_arsize;
  assign axi_if.slave_if[u_lt_aic_dma].arburst = dut.u_lt_aic_dma.i_arburst;
  assign axi_if.slave_if[u_lt_aic_dma].arready = dut.u_lt_aic_dma.o_arready;
  assign axi_if.slave_if[u_lt_aic_dma].rvalid  = dut.u_lt_aic_dma.o_rvalid;
  assign axi_if.slave_if[u_lt_aic_dma].rlast   = dut.u_lt_aic_dma.o_rlast;
  assign axi_if.slave_if[u_lt_aic_dma].rid     = dut.u_lt_aic_dma.o_rid;
  assign axi_if.slave_if[u_lt_aic_dma].rdata   = dut.u_lt_aic_dma.o_rdata;
  assign axi_if.slave_if[u_lt_aic_dma].rresp   = dut.u_lt_aic_dma.o_rresp;
  assign axi_if.slave_if[u_lt_aic_dma].rready  = dut.u_lt_aic_dma.i_rready;
  assign axi_if.slave_if[u_lt_aic_dma].awlock  = 0;
  assign axi_if.slave_if[u_lt_aic_dma].awcache = 0;
  assign axi_if.slave_if[u_lt_aic_dma].awprot  = 0;
  assign axi_if.slave_if[u_lt_aic_dma].arlock  = 0;
  assign axi_if.slave_if[u_lt_aic_dma].arcache = 0;
  assign axi_if.slave_if[u_lt_aic_dma].arprot  = 0;

  assign axi_if.slave_if[u_timestamp_logger].awvalid = dut.u_timestamp_logger.i_axi_s_aw_valid;
  assign axi_if.slave_if[u_timestamp_logger].awaddr  = dut.u_timestamp_logger.i_axi_s_aw_addr;
  assign axi_if.slave_if[u_timestamp_logger].awid    = dut.u_timestamp_logger.i_axi_s_aw_id;
  assign axi_if.slave_if[u_timestamp_logger].awlen   = dut.u_timestamp_logger.i_axi_s_aw_len;
  assign axi_if.slave_if[u_timestamp_logger].awsize  = dut.u_timestamp_logger.i_axi_s_aw_size;
  assign axi_if.slave_if[u_timestamp_logger].awburst = dut.u_timestamp_logger.i_axi_s_aw_burst;
  assign axi_if.slave_if[u_timestamp_logger].awready = dut.u_timestamp_logger.o_axi_s_aw_ready;
  assign axi_if.slave_if[u_timestamp_logger].wvalid  = dut.u_timestamp_logger.i_axi_s_w_valid;
  assign axi_if.slave_if[u_timestamp_logger].wlast   = dut.u_timestamp_logger.i_axi_s_w_last;
  assign axi_if.slave_if[u_timestamp_logger].wstrb   = dut.u_timestamp_logger.i_axi_s_w_strb;
  assign axi_if.slave_if[u_timestamp_logger].wdata   = dut.u_timestamp_logger.i_axi_s_w_data;
  assign axi_if.slave_if[u_timestamp_logger].wready  = dut.u_timestamp_logger.o_axi_s_w_ready;
  assign axi_if.slave_if[u_timestamp_logger].bvalid  = dut.u_timestamp_logger.o_axi_s_b_valid;
  assign axi_if.slave_if[u_timestamp_logger].bid     = dut.u_timestamp_logger.o_axi_s_b_id;
  assign axi_if.slave_if[u_timestamp_logger].bresp   = dut.u_timestamp_logger.o_axi_s_b_resp;
  assign axi_if.slave_if[u_timestamp_logger].bready  = dut.u_timestamp_logger.i_axi_s_b_ready;
  assign axi_if.slave_if[u_timestamp_logger].arvalid = dut.u_timestamp_logger.i_axi_s_ar_valid;
  assign axi_if.slave_if[u_timestamp_logger].araddr  = dut.u_timestamp_logger.i_axi_s_ar_addr;
  assign axi_if.slave_if[u_timestamp_logger].arid    = dut.u_timestamp_logger.i_axi_s_ar_id;
  assign axi_if.slave_if[u_timestamp_logger].arlen   = dut.u_timestamp_logger.i_axi_s_ar_len;
  assign axi_if.slave_if[u_timestamp_logger].arsize  = dut.u_timestamp_logger.i_axi_s_ar_size;
  assign axi_if.slave_if[u_timestamp_logger].arburst = dut.u_timestamp_logger.i_axi_s_ar_burst;
  assign axi_if.slave_if[u_timestamp_logger].arready = dut.u_timestamp_logger.o_axi_s_ar_ready;
  assign axi_if.slave_if[u_timestamp_logger].rvalid  = dut.u_timestamp_logger.o_axi_s_r_valid;
  assign axi_if.slave_if[u_timestamp_logger].rlast   = dut.u_timestamp_logger.o_axi_s_r_last;
  assign axi_if.slave_if[u_timestamp_logger].rid     = dut.u_timestamp_logger.o_axi_s_r_id;
  assign axi_if.slave_if[u_timestamp_logger].rdata   = dut.u_timestamp_logger.o_axi_s_r_data;
  assign axi_if.slave_if[u_timestamp_logger].rresp   = dut.u_timestamp_logger.o_axi_s_r_resp;
  assign axi_if.slave_if[u_timestamp_logger].rready  = dut.u_timestamp_logger.i_axi_s_r_ready;
  assign axi_if.slave_if[u_timestamp_logger].awlock  = 0;
  assign axi_if.slave_if[u_timestamp_logger].awcache = 0;
  assign axi_if.slave_if[u_timestamp_logger].awprot  = 0;
  assign axi_if.slave_if[u_timestamp_logger].arlock  = 0;
  assign axi_if.slave_if[u_timestamp_logger].arcache = 0;
  assign axi_if.slave_if[u_timestamp_logger].arprot  = 0;

  assign axi_if.slave_if[u_token_manager].awid    = dut.u_token_manager.i_axi_s_aw.id;
  assign axi_if.slave_if[u_token_manager].awaddr  = dut.u_token_manager.i_axi_s_aw.addr;
  assign axi_if.slave_if[u_token_manager].awlen   = dut.u_token_manager.i_axi_s_aw.len;
  assign axi_if.slave_if[u_token_manager].awsize  = dut.u_token_manager.i_axi_s_aw.size;
  assign axi_if.slave_if[u_token_manager].awburst = dut.u_token_manager.i_axi_s_aw.burst;
  assign axi_if.slave_if[u_token_manager].awvalid = dut.u_token_manager.i_axi_s_aw.valid;
  assign axi_if.slave_if[u_token_manager].awready = dut.u_token_manager.o_axi_s_aw_ready;
  assign axi_if.slave_if[u_token_manager].arid    = dut.u_token_manager.i_axi_s_ar.id;
  assign axi_if.slave_if[u_token_manager].araddr  = dut.u_token_manager.i_axi_s_ar.addr;
  assign axi_if.slave_if[u_token_manager].arlen   = dut.u_token_manager.i_axi_s_ar.len;
  assign axi_if.slave_if[u_token_manager].arsize  = dut.u_token_manager.i_axi_s_ar.size;
  assign axi_if.slave_if[u_token_manager].arburst = dut.u_token_manager.i_axi_s_ar.burst;
  assign axi_if.slave_if[u_token_manager].arvalid = dut.u_token_manager.i_axi_s_ar.valid;
  assign axi_if.slave_if[u_token_manager].arready = dut.u_token_manager.o_axi_s_ar_ready;
  assign axi_if.slave_if[u_token_manager].wdata   = dut.u_token_manager.i_axi_s_w.data;
  assign axi_if.slave_if[u_token_manager].wstrb   = dut.u_token_manager.i_axi_s_w.strb;
  assign axi_if.slave_if[u_token_manager].wlast   = dut.u_token_manager.i_axi_s_w.last;
  assign axi_if.slave_if[u_token_manager].wvalid  = dut.u_token_manager.i_axi_s_w.valid;
  assign axi_if.slave_if[u_token_manager].wready  = dut.u_token_manager.o_axi_s_w_ready;
  assign axi_if.slave_if[u_token_manager].rid     = dut.u_token_manager.o_axi_s_r.id;
  assign axi_if.slave_if[u_token_manager].rdata   = dut.u_token_manager.o_axi_s_r.data;
  assign axi_if.slave_if[u_token_manager].rresp   = dut.u_token_manager.o_axi_s_r.resp;
  assign axi_if.slave_if[u_token_manager].rlast   = dut.u_token_manager.o_axi_s_r.last;
  assign axi_if.slave_if[u_token_manager].rvalid  = dut.u_token_manager.o_axi_s_r.valid;
  assign axi_if.slave_if[u_token_manager].rready  = dut.u_token_manager.i_axi_s_r_ready;
  assign axi_if.slave_if[u_token_manager].bid     = dut.u_token_manager.o_axi_s_b.id;
  assign axi_if.slave_if[u_token_manager].bresp   = dut.u_token_manager.o_axi_s_b.resp;
  assign axi_if.slave_if[u_token_manager].bvalid  = dut.u_token_manager.o_axi_s_b.valid;
  assign axi_if.slave_if[u_token_manager].bready  = dut.u_token_manager.i_axi_s_b_ready;
  assign axi_if.slave_if[u_token_manager].awlock  = 0;
  assign axi_if.slave_if[u_token_manager].awcache = 0;
  assign axi_if.slave_if[u_token_manager].awprot  = 0;
  assign axi_if.slave_if[u_token_manager].arlock  = 0;
  assign axi_if.slave_if[u_token_manager].arcache = 0;
  assign axi_if.slave_if[u_token_manager].arprot  = 0;


  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
   // Generate the clock
  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(aic_infra_freq_mhz), .duty(50));
    clk_en <= 1'b1;
  end


  initial begin
    if($test$plusargs("CID"))
      $value$plusargs("CID=%0d",core_id);
    else
      core_id = 1;
    uvm_config_db#(int)::set(uvm_root::get(), "", "core_id", core_id);
  end


  initial begin
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.axi_system_env", "vif", axi_if);
  end

  // Run test
  initial
  begin
    run_test ();
  end


  initial begin
    //$assertoff(0, dut.u_aic_rv_plic);
    cva6v_assertoff();
  end


  function static void cva6v_assertoff();
    // from Raymonds's hw/vendor/axelera/cva6v/default/dv/rtl/uvm_top.sv
    // TODO: known failure in PMP https://github.com/axelera-ai/hw.riscv/issues/542
    $assertoff(
        0, `CVA6V_PATH.u_cva6v.u_cva6v_top.i_cva6.ex_stage_i.lsu_i.gen_mmu_sv39.i_cva6_mmu.i_pmp_if);
    // TODO: known failure in PMP https://github.com/axelera-ai/hw.riscv/issues/542
    $assertoff(
        0,
        `CVA6V_PATH.u_cva6v.u_cva6v_top.i_cva6.ex_stage_i.lsu_i.gen_mmu_sv39.i_cva6_mmu.i_pmp_data);
    // TODO: to be debuuged
    $assertoff(0, `CVA6V_PATH.u_cva6v.u_cva6v_top.i_cva6.gen_cache_wb.i_cache_subsystem);
  endfunction

endmodule:hdl_top
