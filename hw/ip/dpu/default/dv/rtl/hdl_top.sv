`define AXI_VIP

`define DUT dut
`define MEM_DEPTH 16384

module hdl_top;
  // Time unit and precision
  timeunit 1ps; timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import dpu_pkg::*;
  import dpu_common_pkg::*;
  import dpu_test_pkg::*;
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  `include "axi4pc/bind_ai_core_dpu.svh"

  // Clock and reset signals
  time 	dpu_freq_mhz     = 800;
  time  dpu_tol_ps       = 100;
  bit 	clk_en;
  logic clk;
  bit   rst_n;
  bit [AIC_CID_SUB_W-1:0] i_cid;
  bit [AIC_BLOCK_ID_WIDTH-1:0] i_block_id;

  //Tokens
  logic    [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] dpu_tok_prod_vld;
  logic    [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] dpu_tok_prod_rdy;
  logic    [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] dpu_tok_cons_vld;
  logic    [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] dpu_tok_cons_rdy;
  

  // =============================================================================================================
  // Instantiate IAU interface
  // =============================================================================================================
  dpu_if if_dpu (clk);


  // =============================================================================================================
  // Instantiate interfaces and BFMs and assignments
  // =============================================================================================================
`ifdef AXI_VIP
  // VIP Interface instance representing the AXI system
  svt_axi_if axi_if ();

  iid_if iid_if_i (clk);

  assign axi_if.common_aclk = clk;
  // TB Interface instance to provide access to the reset signal
  axi_reset_if axi_reset_if ();
  assign axi_reset_if.clk = clk;
`endif

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
`ifdef AXI_VIP
  assign axi_if.master_if[0].aresetn = axi_reset_if.reset;
  assign axi_if.master_if[1].aresetn = axi_reset_if.reset;
  assign axi_if.master_if[2].aresetn = axi_reset_if.reset;
  assign axi_if.slave_if[0].aresetn  = axi_reset_if.reset;
  assign rst_n                       = axi_reset_if.reset;
  assign if_dpu.reset_an_i           = axi_reset_if.reset;

  assign axi_if.master_if[0].awprot  = 0;
  assign axi_if.master_if[0].arprot  = 0;
  assign axi_if.master_if[0].acprot  = 0;
  assign axi_if.master_if[0].awlock  = 0;
  assign axi_if.master_if[0].arlock  = 0;
  assign axi_if.master_if[0].awcache = 0;
  assign axi_if.master_if[0].arcache = 0;

  assign axi_if.slave_if[0].awprot   = 0;
  assign axi_if.slave_if[0].arprot   = 0;
  assign axi_if.slave_if[0].acprot   = 0;
  assign axi_if.slave_if[0].awlock   = 0;
  assign axi_if.slave_if[0].arlock   = 0;
  assign axi_if.slave_if[0].arcache  = 0;
  assign axi_if.slave_if[0].awcache  = 0;

`endif

  // Token manager Interface instance
  token_agent_if tok_agt_if (clk);
  assign tok_agt_if.reset_n      = axi_reset_if.reset;
  assign tok_agt_if.tok_cons_rdy = dpu_tok_cons_rdy;
  assign tok_agt_if.tok_prod_vld = dpu_tok_prod_vld;
  assign dpu_tok_cons_vld        = tok_agt_if.tok_cons_vld;
  assign dpu_tok_prod_rdy        = tok_agt_if.tok_prod_rdy;

  dpu #(
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_END_ADDR)
  ) dut (
      // Clock and reset signals
      .i_clk                  (clk),
      .i_rst_n                (rst_n),
      //--------------------------------------------------
      // AXI4 slave config port
      //--------------------------------------------------
      // AXI S read address channel
      .i_dpu_cfg_axi_s_araddr (axi_if.master_if[0].araddr),
      .i_dpu_cfg_axi_s_arburst(axi_if.master_if[0].arburst),
      .i_dpu_cfg_axi_s_arid   (axi_if.master_if[0].arid),
      .i_dpu_cfg_axi_s_arlen  (axi_if.master_if[0].arlen),
      .i_dpu_cfg_axi_s_arsize (axi_if.master_if[0].arsize),
      .i_dpu_cfg_axi_s_arvalid(axi_if.master_if[0].arvalid),
      .o_dpu_cfg_axi_s_arready(axi_if.master_if[0].arready),
      // AXI S write address channe(axi_if.i_master_if[0].a)l
      .i_dpu_cfg_axi_s_awaddr (axi_if.master_if[0].awaddr),
      .i_dpu_cfg_axi_s_awburst(axi_if.master_if[0].awburst),
      .i_dpu_cfg_axi_s_awid   (axi_if.master_if[0].awid),
      .i_dpu_cfg_axi_s_awlen  (axi_if.master_if[0].awlen),
      .i_dpu_cfg_axi_s_awsize (axi_if.master_if[0].awsize),
      .i_dpu_cfg_axi_s_awvalid(axi_if.master_if[0].awvalid),
      .o_dpu_cfg_axi_s_awready(axi_if.master_if[0].awready),
      // AXI S write response channe(axi_if.i_master_if[0].)l
      .o_dpu_cfg_axi_s_bid    (axi_if.master_if[0].bid),
      .o_dpu_cfg_axi_s_bresp  (axi_if.master_if[0].bresp),
      .o_dpu_cfg_axi_s_bvalid (axi_if.master_if[0].bvalid),
      .i_dpu_cfg_axi_s_bready (axi_if.master_if[0].bready),
      // AXI S read data/response channe(axi_if.i_master_if[0].)l
      .o_dpu_cfg_axi_s_rdata  (axi_if.master_if[0].rdata),
      .o_dpu_cfg_axi_s_rid    (axi_if.master_if[0].rid),
      .o_dpu_cfg_axi_s_rlast  (axi_if.master_if[0].rlast),
      .o_dpu_cfg_axi_s_rresp  (axi_if.master_if[0].rresp),
      .o_dpu_cfg_axi_s_rvalid (axi_if.master_if[0].rvalid),
      .i_dpu_cfg_axi_s_rready (axi_if.master_if[0].rready),
      // AXI S write data channe(axi_if.i_master_if[0].)l
      .i_dpu_cfg_axi_s_wdata  (axi_if.master_if[0].wdata),
      .i_dpu_cfg_axi_s_wlast  (axi_if.master_if[0].wlast),
      .i_dpu_cfg_axi_s_wstrb  (axi_if.master_if[0].wstrb),
      .i_dpu_cfg_axi_s_wvalid (axi_if.master_if[0].wvalid),
      .o_dpu_cfg_axi_s_wready (axi_if.master_if[0].wready),

      // Tokens
      .o_dpu_tok_prod_vld(dpu_tok_prod_vld),
      .i_dpu_tok_prod_rdy(dpu_tok_prod_rdy),
      .i_dpu_tok_cons_vld(dpu_tok_cons_vld),
      .o_dpu_tok_cons_rdy(dpu_tok_cons_rdy),

      // IAU AXI stream
      .i_dpu_iau_axis_s_data (axi_if.master_if[1].tdata),
      .i_dpu_iau_axis_s_last (axi_if.master_if[1].tlast),
      .i_dpu_iau_axis_s_valid(axi_if.master_if[1].tvalid),
      .o_dpu_iau_axis_s_ready(axi_if.master_if[1].tready),

      // IFD1 AXI stream
      .i_dpu_ifd1_axis_s_data (axi_if.master_if[2].tdata),
      .i_dpu_ifd1_axis_s_last (axi_if.master_if[2].tlast),
      .i_dpu_ifd1_axis_s_valid(axi_if.master_if[2].tvalid),
      .o_dpu_ifd1_axis_s_ready(axi_if.master_if[2].tready),

      // ODR AXI stream
      .o_dpu_odr_axis_m_data (axi_if.slave_if[0].tdata),
      .o_dpu_odr_axis_m_last (axi_if.slave_if[0].tlast),
      .o_dpu_odr_axis_m_valid(axi_if.slave_if[0].tvalid),
      .i_dpu_odr_axis_m_ready(axi_if.slave_if[0].tready),

      // IRQ
      .o_irq(),

      // Observation
      .o_obs(),

      // Block identification
      .i_cid(i_cid),
      .i_block_id(i_block_id)

  );

  assign axi_if.slave_if[0].awvalid = 0;
  assign axi_if.slave_if[0].wvalid  = 0;
  assign axi_if.slave_if[0].arvalid = 0;
  assign if_dpu.irq_o               = dut.o_irq;

  assign i_cid = 1;
  assign i_block_id = aic_common_pkg::AIC_BLOCK_ID_M_DPU;

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate the clock

  axe_clk_generator u_axe_clk_generator(
    .i_enable ( clk_en ) ,
    .o_clk    ( clk    )
  );

  axe_clk_assert u_axe_clk_assert(
    .clk        ( clk           ) ,
    .rst_n      ( rst_n         ) ,
    .freq_mhz   ( dpu_freq_mhz  ) ,
    .tol_ps     ( dpu_tol_ps    )
  );

  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(dpu_freq_mhz), .duty(50));
    clk_en <= 1;
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
        uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.axi_system_env", "vif", axi_if);
    `endif
    uvm_config_db#(virtual dpu_if)::set(null, "uvm_test_top.env*", "vif", if_dpu);
    uvm_config_db#(virtual iid_if)::set(null, "uvm_test_top.env", "iid_if_i", iid_if_i);
    uvm_config_db#(virtual token_agent_if)::set(null, "uvm_test_top.env.tok_agt", "vif", tok_agt_if);
  end

  //disable all assertions until first reset happens
  //RTL assertions are returning false errors before initial reset
  bit assertoff_PC_OVF_ASSERT;
  initial begin
    $assertoff(0, dut);
    @(negedge rst_n);
    #5ns;
    $asserton(0, dut);


    //disabling iau_dp RTL assertion check when generating
    //interruption, it gives false positive errors otherwise
    if (uvm_root::get().find("uvm_test_top").get_type_name() == "dpu_irq_test") begin
      `uvm_info("top", "IRQ test, disabling some assertions", UVM_LOW)
      $assertoff(0, dut.i_dpu_dp);
      $assertoff(0, dut.u_dpu_dpcmd_gen);
      $assertoff(0, dut.u_dpu_cmdblock);
      assertoff_PC_OVF_ASSERT = 1;
    end

  end
/*
  TODO: remove it later if not needed
  //initialization Cmd program fifos, it will read X otherwise
  for (genvar i = 0; i < 512; i++) begin
    initial begin
      #1;
      force dut.u_dpu_dpcmd_gen.u_cmdblock_desc_mem.gen_ram.u_tc_ram.memory_q[i] = 0;
      #1;
      release dut.u_dpu_dpcmd_gen.u_cmdblock_desc_mem.gen_ram.u_tc_ram.memory_q[i];
    end
  end
*/
  initial begin
    run_test ();
  end


endmodule : hdl_top
