// AI CORE DWPU hdl top
`define AXI_VIP
`define AXI_VIP_CONN_M
`define AXI_VIP_CONN_S
`define AXI_VIP_CONN_CFG

`define DUT dut

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import dwpu_pkg::*;
  import ai_core_dwpu_common_pkg::*;
  import ai_core_dwpu_test_pkg::*;

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif

  //include bind files
  //`include "axi4pc/bind_ai_core_dwpu.svh"

  realtime CLK_PERIOD = 1.25ns;  // 800MHz --> 1.25ns

  logic i_clk;
  logic i_rst_n;
  logic i_test_mode;
  always_comb i_test_mode = 1'b0;

  logic clk_en;
  int  dwpu_freq_mhz = 800;
  time dwpu_tol_ps   = 10;
  //--------------------------------------------------
  // AXI4 Config port
  //--------------------------------------------------
  // AXI write address channel
  logic                                               i_axi_s_aw_valid;
  logic [       AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]      i_axi_s_aw_addr;
  logic [             AIC_LT_AXI_S_ID_WIDTH-1:0]      i_axi_s_aw_id;
  logic [              AIC_LT_AXI_LEN_WIDTH-1:0]      i_axi_s_aw_len;
  logic [             AIC_LT_AXI_SIZE_WIDTH-1:0]      i_axi_s_aw_size;
  logic [       AIC_LT_AXI_BURST_TYPE_WIDTH-1:0]      i_axi_s_aw_burst;
  logic                                               o_axi_s_aw_ready;
  // AXI write data channel
  logic                                               i_axi_s_w_valid;
  logic                                               i_axi_s_w_last;
  logic [            AIC_LT_AXI_WSTRB_WIDTH-1:0]      i_axi_s_w_strb;
  logic [             AIC_LT_AXI_DATA_WIDTH-1:0]      i_axi_s_w_data;
  logic                                               o_axi_s_w_ready;
  // AXI write response channel
  logic                                               o_axi_s_b_valid;
  logic [             AIC_LT_AXI_S_ID_WIDTH-1:0]      o_axi_s_b_id;
  logic [             AIC_LT_AXI_RESP_WIDTH-1:0]      o_axi_s_b_resp;
  logic                                               i_axi_s_b_ready;
  // AXI read address channel
  logic                                               i_axi_s_ar_valid;
  logic [       AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]      i_axi_s_ar_addr;
  logic [             AIC_LT_AXI_S_ID_WIDTH-1:0]      i_axi_s_ar_id;
  logic [              AIC_LT_AXI_LEN_WIDTH-1:0]      i_axi_s_ar_len;
  logic [             AIC_LT_AXI_SIZE_WIDTH-1:0]      i_axi_s_ar_size;
  logic [       AIC_LT_AXI_BURST_TYPE_WIDTH-1:0]      i_axi_s_ar_burst;
  logic                                               o_axi_s_ar_ready;
  // AXI read data/response channel
  logic                                               o_axi_s_r_valid;
  logic                                               o_axi_s_r_last;
  logic [             AIC_LT_AXI_S_ID_WIDTH-1:0]      o_axi_s_r_id;
  logic [             AIC_LT_AXI_DATA_WIDTH-1:0]      o_axi_s_r_data;
  logic [             AIC_LT_AXI_RESP_WIDTH-1:0]      o_axi_s_r_resp;
  logic                                               i_axi_s_r_ready;

  // IFD0 -> DWPU AXI stream
  logic                                               i_axis_s_tvalid;
  logic [             AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_axis_s_tdata;
  logic                                               i_axis_s_tlast;
  logic                                               o_axis_s_tready;

  // DWPU -> IAU AXI stream
  logic                                               o_axis_m_tvalid;
  logic [             AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] o_axis_m_tdata;
  logic                                               o_axis_m_tlast;
  logic                                               i_axis_m_tready;

  // Tokens
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_tok_prod_valid;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_tok_prod_ready;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0]     i_tok_cons_valid;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0]     o_tok_cons_ready;

  // IRQ
  logic                                               o_irq;
  // Observation
  logic [AIC_DEV_OBS_DW-1:0]                          o_obs;

  ///// Timestamp:
  logic o_ts_start;
  logic o_ts_end;
  ///// ACD sync:
  logic o_acd_sync;

  // CID input
  logic [AIC_CID_SUB_W-1:0]                           i_cid;

  //block id
  logic [AIC_BLOCK_ID_WIDTH-1:0]                      i_block_id ;

  //Sideband signals ( tc_sram)
  axe_tcl_sram_pkg::impl_inp_t                        i_dp_cmd_gen_sram_impl;
  axe_tcl_sram_pkg::impl_oup_t                        o_dp_cmd_gen_sram_impl;

`ifdef TARGET_DFT
  logic                                               ijtag_tck;
  logic                                               ijtag_reset;
  logic                                               ijtag_ce;
  logic                                               ijtag_se;
  logic                                               ijtag_ue;
  logic                                               ijtag_sel;
  logic                                               ijtag_si;
  logic                                               ijtag_so;
  logic                                               test_clock;
  logic                                               edt_update;
  logic                                               scan_en;
  logic [7:0]                                         scan_in;
  logic [7:0]                                         scan_out;
  logic                                               vl_sms_ai_core_dwpu_p_proc_1_sms_1_safe_rr;
  logic                                               vl_sms_dm0;
  logic                                               vl_sms_dm1;
  logic                                               vl_sms_dm2;
  logic                                               vl_srv_WRSTN;
  logic                                               vl_srv_WRCK;
  logic                                               vl_srv_WSI;
  logic                                               vl_srv_SelectWIR;
  logic                                               vl_srv_CaptureWR;
  logic                                               vl_srv_ShiftWR;
  logic                                               vl_srv_UpdateWR;
  logic                                               vl_srv_WSO;
  logic                                               vl_srv_sfp_dft_mode;
  logic                                               vl_srv_sfp_fail;
  logic                                               vl_srv_sfp_ready;

`endif

  // =============================================================================================================
  // Instantiate DWPU agent interface
  // =============================================================================================================
  ai_core_dwpu_if if_dwpu(i_clk);


`ifdef AXI_VIP
  // VIP Interface instance representing the AXI system
  svt_axi_if axi_if ();
  assign axi_if.common_aclk = i_clk;
  // TB Interface instance to provide access to the reset signal
  axi_reset_if axi_reset_if ();
  assign axi_reset_if.clk = i_clk;
`endif

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
`ifdef AXI_VIP
  assign axi_if.master_if[0].aresetn  = axi_reset_if.reset;
  assign axi_if.master_if[1].aresetn  = axi_reset_if.reset;
  assign axi_if.slave_if[0].aresetn   = axi_reset_if.reset;
  assign i_rst_n                      = axi_reset_if.reset;
  assign if_dwpu.reset_an_i           = axi_reset_if.reset;
`endif

  // AXIS:
  //------------------------------------------------------
  // DWPU IFD0
  assign i_axis_s_tvalid     = axi_if.master_if[1].tvalid; //  TB output port
  assign axi_if.master_if[1].tready  = o_axis_s_tready ;    // TB input port
  assign i_axis_s_tdata      = axi_if.master_if[1].tdata;  //   TB output port
  assign i_axis_s_tlast      = axi_if.master_if[1].tlast;  //   TB Output port


  // DWPU IAU
  assign axi_if.slave_if[0].tvalid  = o_axis_m_tvalid;     // TB input port
  assign i_axis_m_tready     = axi_if.slave_if[0].tready; // TB output port
  assign axi_if.slave_if[0].tdata   = o_axis_m_tdata;      // TB input port
  assign axi_if.slave_if[0].tlast   = o_axis_m_tlast;      // TB input port



 // AXI LT interface
`ifdef AXI_VIP_CONN_M
  assign i_axi_s_aw_valid = axi_if.master_if[0].awvalid;
  assign i_axi_s_aw_addr  = axi_if.master_if[0].awaddr;
  assign i_axi_s_aw_id    = axi_if.master_if[0].awid;
  assign i_axi_s_aw_len   = axi_if.master_if[0].awlen;
  assign i_axi_s_aw_size  = axi_if.master_if[0].awsize;
  assign i_axi_s_aw_burst = axi_if.master_if[0].awburst;


  assign axi_if.master_if[0].awready = o_axi_s_aw_ready;

  assign i_axi_s_w_valid  = axi_if.master_if[0].wvalid;
  assign i_axi_s_w_last   = axi_if.master_if[0].wlast;
  assign i_axi_s_w_data   = axi_if.master_if[0].wdata;
  assign i_axi_s_w_strb   = axi_if.master_if[0].wstrb;

  assign axi_if.master_if[0].wready = o_axi_s_w_ready;

  assign axi_if.master_if[0].bvalid = o_axi_s_b_valid;
  assign axi_if.master_if[0].bid    = o_axi_s_b_id;
  assign axi_if.master_if[0].bresp  = o_axi_s_b_resp;

  assign i_axi_s_b_ready  = axi_if.master_if[0].bready;

  assign i_axi_s_ar_valid = axi_if.master_if[0].arvalid;
  assign i_axi_s_ar_addr  = axi_if.master_if[0].araddr;
  assign i_axi_s_ar_id    = axi_if.master_if[0].arid;
  assign i_axi_s_ar_len   = axi_if.master_if[0].arlen;
  assign i_axi_s_ar_size  = axi_if.master_if[0].arsize;
  assign i_axi_s_ar_burst = axi_if.master_if[0].arburst;

  assign axi_if.master_if[0].arready = o_axi_s_ar_ready;

  assign axi_if.master_if[0].rvalid = o_axi_s_r_valid;
  assign axi_if.master_if[0].rlast  = o_axi_s_r_last;
  assign axi_if.master_if[0].rid    = o_axi_s_r_id;
  assign axi_if.master_if[0].rdata  = o_axi_s_r_data;
  assign axi_if.master_if[0].rresp  = o_axi_s_r_resp;

  assign i_axi_s_r_ready  = axi_if.master_if[0].rready;

  token_agent_if tok_agt_if (i_clk);
  assign tok_agt_if.reset_n      = axi_reset_if.reset;
  assign tok_agt_if.tok_cons_rdy = o_tok_cons_ready;
  assign tok_agt_if.tok_prod_vld = o_tok_prod_valid;
  assign i_tok_cons_valid = tok_agt_if.tok_cons_vld;
  assign i_tok_prod_ready = tok_agt_if.tok_prod_rdy;



  assign if_dwpu.irq_o = o_irq;
  assign if_dwpu.obs_o = o_obs;
  assign i_cid                     = 0;
  assign i_block_id = aic_common_pkg::AIC_BLOCK_ID_D_DWPU;




`endif

`ifdef TARGET_DFT
  assign ijtag_tck                                    = 1'b0;
  assign ijtag_reset                                  = 1'b0;
  assign ijtag_ce                                     = 1'b0;
  assign ijtag_se                                     = 1'b0;
  assign ijtag_ue                                     = 1'b0;
  assign ijtag_sel                                    = 1'b0;
  assign ijtag_si                                     = 1'b0;

  assign test_clock                                   = 1'b0;
  assign edt_update                                   = 1'b0;
  assign scan_en                                      = 1'b0;
  assign scan_in                                      = '0;

  assign vl_sms_ai_core_dwpu_p_proc_1_sms_1_safe_rr   = 1'b0;
  assign vl_sms_dm0                                   = 1'b0;
  assign vl_sms_dm1                                   = 1'b0;
  assign vl_sms_dm2                                   = 1'b0;
  assign vl_srv_WRSTN                                 = rst_n;
  assign vl_srv_WRCK                                  = 1'b0;
  assign vl_srv_WSI                                   = 1'b0;
  assign vl_srv_SelectWIR                             = 1'b0;
  assign vl_srv_CaptureWR                             = 1'b0;
  assign vl_srv_ShiftWR                               = 1'b0;
  assign vl_srv_UpdateWR                              = 1'b0;

  assign vl_srv_sfp_dft_mode                          = 1'b0;
`endif

  // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
`ifndef NO_DUT
  dwpu #(
    .REGION_ST_ADDR   (aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR),
    .REGION_END_ADDR  (aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR),
    .DpCommandMemoryDepth(ai_core_dwpu_common_pkg::INSTR_MEM_DEPTH)
  ) dut (.*);
`endif

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
   axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(i_clk)
                                          );

   axe_clk_assert u_axe_clk_assert(.clk(i_clk),
				.rst_n(i_rst_n),
				.freq_mhz(dwpu_freq_mhz),
				.tol_ps  (dwpu_tol_ps)
				);

    // Generate the clock
  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(dwpu_freq_mhz), .duty(50));
    clk_en = 1'b1;
  end


  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
    `ifdef AXI_VIP
    // Set the reset interface on the virtual sequencer
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(
        uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);

    // =============================================================================================================
    // Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI
    // System ENV and the DUT through the AXI interface.
    // =============================================================================================================
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.m_axi_system_env", "vif", axi_if);
    uvm_config_db#(virtual ai_core_dwpu_if)::set(null, "uvm_test_top.env.dwpu_agt", "vif", if_dwpu);
    uvm_config_db#(virtual token_agent_if)::set(null, "uvm_test_top.env.tok_agt", "vif", tok_agt_if);
    `endif
  end

  //disable all assertions until first reset happens
  //RTL assertions are returning false errors before initial reset
  initial begin
    $timeformat(-9, 3, " ns", 10);
    $assertoff(0,dut);
    @(negedge i_rst_n);
    #1; //this is necessary because the reset sequence can drive the reset after #0ps, which leads to a race condition that is triggered by Axi4PC module due to sequence of events on simulator.
    $asserton(0,dut);
  end

  initial begin
    run_test();
  end
endmodule : hdl_top
