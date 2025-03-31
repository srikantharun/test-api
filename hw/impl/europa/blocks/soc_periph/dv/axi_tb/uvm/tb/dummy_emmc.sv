module emmc
  import axi_pkg::*;
  import emmc_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
    parameter type emmc_axi_addr_t  = logic [39:0],
    parameter type emmc_axi_data_t  = logic [63:0],
    parameter type emmc_axi_wstrb_t = logic  [7:0],
    parameter type emmc_axi_id_t    = logic  [3:0],
    parameter type emmc_axi_user_t  = logic  [0:0]
) (
    /// emmc capability register struct for inputs to emmc
    input emmc_outreg_cfg_t emmc_outreg_cfg,

    /// emmc register struct for ports driving from emmc
    output emmc_inreg_cfg_t emmc_inreg_cfg,

    /// Peripheral Clock, positive edge triggered
    input wire i_pclk,

    /// Asynchronous reset, active low
    input wire i_preset_n,

    input wire i_emmc_clk,

    input wire i_emmc_rst_n,

    //--------------------------------------------------------------------
    // SD host events
    //--------------------------------------------------------------------
    output logic o_interrupt,

    //--------------------------------------------------------------------
    // APB slave interface
    //--------------------------------------------------------------------
    input  logic [31:0] i_s_paddr,
    input  logic        i_s_psel,
    input  logic        i_s_penable,
    input  logic        i_s_pwrite,
    input  logic [31:0] i_s_pwdata,
    output logic        o_s_pready,
    output logic [31:0] o_s_prdata,
    output logic        o_s_pslverr,

    //--------------------------------------------------------------------
    // AXI master interface
    //--------------------------------------------------------------------
    // AXI Write Address Channel
    input  logic            i_m_awready,
    output emmc_axi_addr_t  o_m_awaddr,
    output emmc_axi_id_t    o_m_awid,
    output axi_len_t        o_m_awlen,
    output axi_size_e       o_m_awsize,
    output axi_burst_e      o_m_awburst,
    output logic            o_m_awlock,
    output axi_cache_t      o_m_awcache,
    output axi_prot_t       o_m_awprot,
    output axi_qos_t        o_m_awqos,
    output axi_region_t     o_m_awregion,
    output emmc_axi_user_t  o_m_awuser,
    output logic            o_m_awvalid,
    // AXI Write Data Channel
    input  logic            i_m_wready,
    output emmc_axi_data_t  o_m_wdata,
    output emmc_axi_wstrb_t o_m_wstrb,
    output logic            o_m_wlast,
    output emmc_axi_user_t  o_m_wuser,
    output logic            o_m_wvalid,
    // AXI Write Response Channel
    input  axi_resp_t       i_m_bresp,
    input  logic            i_m_bvalid,
    input  emmc_axi_id_t    i_m_bid,
    input  emmc_axi_user_t  i_m_buser,
    output logic            o_m_bready,
    // AXI Read Address Channel
    input  logic            i_m_arready,
    output emmc_axi_id_t    o_m_arid,
    output emmc_axi_addr_t  o_m_araddr,
    output axi_len_t        o_m_arlen,
    output axi_size_e       o_m_arsize,
    output axi_burst_e      o_m_arburst,
    output logic            o_m_arlock,
    output axi_cache_t      o_m_arcache,
    output axi_prot_t       o_m_arprot,
    output axi_qos_t        o_m_arqos,
    output axi_region_t     o_m_arregion,
    output emmc_axi_user_t  o_m_aruser,
    output logic            o_m_arvalid,
    // AXI Read Data Channel
    input  emmc_axi_data_t  i_m_rdata,
    input  axi_resp_t       i_m_rresp,
    input  logic            i_m_rlast,
    input  logic            i_m_rvalid,
    output logic            o_m_rready,

    // SRAM config registers
    input  axe_tcl_sram_pkg::impl_inp_t [3:0] i_impl_inp,
    output axe_tcl_sram_pkg::impl_oup_t [3:0] o_impl_oup,

    //--------------------------------------------------------------------
    // Pad Interface
    //--------------------------------------------------------------------
    output              o_mem_ale_oepad,
    output              o_mem_ale_iepad,
    output              o_mem_ale_opad,
    input               i_mem_cmd_ipad,
    output              o_mem_cmd_oepad,
    output              o_mem_cmd_iepad,
    output              o_mem_cmd_opad,
    output              o_mem_ctrl_0_oepad,
    output              o_mem_ctrl_0_iepad,
    input               i_mem_ctrl_0_ipad,
    output              o_mem_ctrl_1_oepad,
    output              o_mem_ctrl_1_iepad,
    output              o_mem_ctrl_1_opad,
    output              o_mem_rstbar_oepad,
    output              o_mem_rstbar_iepad,
    output              o_mem_rstbar_opad,
    input               i_mem_lpbk_dqs_ipad,
    output              o_mem_lpbk_dqs_oepad,
    output              o_mem_lpbk_dqs_iepad,
    input               i_mem_dqs_ipad,
    output              o_mem_dqs_oepad,
    output              o_mem_dqs_iepad,
    output              o_mem_rebar_oepad,
    output              o_mem_rebar_iepad,
    output              o_mem_rebar_opad,
    input               i_mem_rebar_ipad,
    input        [ 7:0] i_mem_data_ipad,
    output       [ 7:0] o_mem_data_oepad,
    output       [ 7:0] o_mem_data_iepad,
    output       [ 7:0] o_mem_data_opad,
    output              o_mem_webar_oepad,
    output              o_mem_webar_iepad,
    output              o_mem_webar_opad,
    output              o_mem_wpbar_oepad,
    output              o_mem_wpbar_iepad,
    input               i_mem_wpbar_ipad,
    output              o_tsel_dqs_0_opad,
    output              o_tsel_dqs_1_opad,
    output              o_tsel_dqs_2_opad,
    output              o_tsel_dqs_3_opad,
    output       [ 7:0] o_tsel_data_0_opad,
    output       [ 7:0] o_tsel_data_1_opad,
    output       [ 7:0] o_tsel_data_2_opad,
    output       [ 7:0] o_tsel_data_3_opad,
    output              o_v18,
    output       [31:0] o_phy_gpio_reg_ctrl_0,
    input        [31:0] i_phy_gpio_reg_status_0,
    output       [31:0] o_phy_gpio_reg_ctrl_1,
    input        [31:0] i_phy_gpio_reg_status_1,
    // DFT
    input  logic        test_mode,
    input  logic        scan_en
);


  import emmc_pkg::*;
  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;
  //--------------------------------------------------------------------
  // APB slave interface
  //--------------------------------------------------------------------
  logic [ CDNS_EMMC_S_AWIDTH-1:0] s_paddr;
  logic [                    2:0] s_pprot;
  logic                           s_psel;
  logic                           s_penable;
  logic                           s_pwrite;
  logic [ CDNS_EMMC_S_DWIDTH-1:0] s_pwdata;
  logic [CDNS_EMMC_S_BEWIDTH-1:0] s_pstrb;
  logic                           s_pready;
  logic [ CDNS_EMMC_S_DWIDTH-1:0] s_prdata;
  logic                           s_pslverr;
  logic                           s_presetn;
  logic                           s_pclk;

  if (CDNS_EMMC_S_AWIDTH > 32) begin : g_awidth_gt32
    $error("COMPILE_ERROR: Cadence SHDC APB Address Bus is too wide");
  end : g_awidth_gt32
  else begin : g_awidth_lte32
    always_comb s_paddr = i_s_paddr[CDNS_EMMC_S_AWIDTH-1:0];
  end : g_awidth_lte32

  if (CDNS_EMMC_S_DWIDTH > 32) begin : g_dwidth_gt32
    $error("COMPILE_ERROR: Cadence SHDC APB Data Bus is too wide");
  end : g_dwidth_gt32
  else begin : g_dwidth_lte32
    always_comb s_pwdata = i_s_pwdata[CDNS_EMMC_S_DWIDTH-1:0];
    always_comb o_s_prdata = {{32 - CDNS_EMMC_S_DWIDTH{1'b0}}, s_prdata};
  end : g_dwidth_lte32

  always_comb s_pclk = i_pclk;
  always_comb s_presetn = i_preset_n;
  always_comb s_pprot = 3'b0;
  always_comb s_psel = i_s_psel;
  always_comb s_penable = i_s_penable;
  always_comb s_pwrite = i_s_pwrite;
  // NOTE:: s_pstrb is an Optional signal: tied to write signal from Master as MUST not be active during reads
  always_comb s_pstrb = {CDNS_EMMC_S_BEWIDTH{i_s_pwrite}};
  always_comb o_s_pready = s_pready;
  always_comb o_s_pslverr = s_pslverr;

  svt_apb_if emmc_apb_if ();

  assign emmc_apb_if.slave_if[0].pclk = s_pclk;
  assign emmc_apb_if.slave_if[0].presetn = s_presetn;
  assign emmc_apb_if.slave_if[0].psel = s_psel;
  assign emmc_apb_if.slave_if[0].penable = s_penable;
  assign emmc_apb_if.slave_if[0].pwrite = s_pwrite;
  assign emmc_apb_if.slave_if[0].paddr = s_paddr;
  assign emmc_apb_if.slave_if[0].pwdata = s_pwdata;
  assign s_prdata = emmc_apb_if.slave_if[0].prdata;
  assign s_pslverr = emmc_apb_if.slave_if[0].pslverr;
  assign s_pready = emmc_apb_if.slave_if[0].pready;

  svt_apb_system_configuration emmc_apb_env_cfg;

  initial begin
    emmc_apb_env_cfg = new("emmc_apb_env_cfg");
    emmc_apb_env_cfg.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_13;
    emmc_apb_env_cfg.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    emmc_apb_env_cfg.apb4_enable = 0;
    emmc_apb_env_cfg.apb3_enable = 1;
    emmc_apb_env_cfg.create_sub_cfgs(1);
    emmc_apb_env_cfg.slave_addr_ranges = new[1];
    emmc_apb_env_cfg.slave_cfg[0].is_active = 1;
    emmc_apb_env_cfg.slave_cfg[0].mem_enable = 1;
    emmc_apb_env_cfg.slave_cfg[0].default_pready = 1;
    emmc_apb_env_cfg.slave_cfg[0].slave_id = 0;
    emmc_apb_env_cfg.slave_addr_ranges[0] = new("emmc_addr_range");
    emmc_apb_env_cfg.slave_addr_ranges[0].start_addr = 'h00;
    emmc_apb_env_cfg.slave_addr_ranges[0].end_addr = 'h1fff;
    emmc_apb_env_cfg.slave_addr_ranges[0].slave_id = 0;

    uvm_config_db#(svt_apb_system_configuration)::set(
        null, "uvm_test_top.m_env.m_emmc_apb_system_env", "cfg", emmc_apb_env_cfg);

    uvm_config_db#(virtual svt_apb_if)::set(null, "uvm_test_top.m_env.m_emmc_apb_system_env", "vif",
                                            emmc_apb_if);
  end

endmodule
