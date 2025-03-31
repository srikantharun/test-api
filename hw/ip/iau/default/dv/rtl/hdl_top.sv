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
  import iau_pkg::*;
  import iau_common_pkg::*;
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import iau_test_pkg::*;
  `include "axi4pc/bind_ai_core_iau.svh"


  time clk_tol_ps    = 100;
  int iau_freq_mhz   = 800;


  // Clock and reset signals
  logic clk;
  bit   rst_n;
  logic clk_en;

  //Tokens
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] iau_tok_prod_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] iau_tok_prod_rdy;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] iau_tok_cons_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] iau_tok_cons_rdy;


  // =============================================================================================================
  // Instantiate IAU interface
  // =============================================================================================================
  iau_if if_iau (clk);


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
  // CLK RST & Assertion Instantitation
  // =============================================================================================================
  axe_clk_generator u_axe_clk_generator(
    .i_enable ( clk_en ) ,
    .o_clk    ( clk    )
  );

  axe_clk_assert u_axe_clk_assert(
    .clk        ( clk           ) ,
    .rst_n      ( rst_n         ) ,
    .freq_mhz   ( iau_freq_mhz  ) ,
    .tol_ps     ( clk_tol_ps    )
  );

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
`ifdef AXI_VIP
  assign axi_if.master_if[0].aresetn = axi_reset_if.reset;
  assign axi_if.master_if[1].aresetn = axi_reset_if.reset;
  assign axi_if.slave_if[0].aresetn  = axi_reset_if.reset;
  assign rst_n                       = axi_reset_if.reset;
  assign if_iau.reset_an_i           = axi_reset_if.reset;

`endif

  // Token manager Interface instance
  token_agent_if tok_agt_if (clk);
  assign tok_agt_if.reset_n      = axi_reset_if.reset;
  assign tok_agt_if.tok_cons_rdy = iau_tok_cons_rdy;
  assign tok_agt_if.tok_prod_vld = iau_tok_prod_vld;
  assign iau_tok_cons_vld        = tok_agt_if.tok_cons_vld;
  assign iau_tok_prod_rdy        = tok_agt_if.tok_prod_rdy;


  // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
  assign if_iau.cid_i            = 0;
  assign if_iau.block_id_i       = 0;
  `include "dut_connections.svh"

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate the clock
  initial begin

    u_axe_clk_generator.set_clock(.freq_mhz(iau_freq_mhz), .duty(50));
    clk_en <= 1'b1;


  end // initial begin


  //initialization Cmd program fifos, it will read X otherwise
  for (genvar i = 0; i < 64; i++) begin
    initial begin
      #1;
      force dut.u_iau_dpcmd_gen.u_cmdblock_desc_mem.gen_flop.gen_storage[i].i_row.d_q = 0;
      #1;
      release dut.u_iau_dpcmd_gen.u_cmdblock_desc_mem.gen_flop.gen_storage[i].i_row.d_q;
    end
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
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.axi_system_env", "vif",
                                     axi_if);
`endif
    uvm_config_db#(virtual iau_if)::set(null, "uvm_test_top.env*", "iau_vif", if_iau);
    uvm_config_db#(virtual iid_if)::set(null, "uvm_test_top.env", "iid_if_i", iid_if_i);
    uvm_config_db#(virtual token_agent_if)::set(null, "uvm_test_top.env.tok_agt", "vif",
                                                tok_agt_if);

  end

  //disable all assertions until first reset happens
  //RTL assertions are returning false errors before initial reset
  initial begin
    $assertoff(0, dut);
    @(negedge rst_n);
    #5ns;
    $asserton(0, dut);

    $assertoff(0, dut.u_iau_dpcmd_gen);
    //disabling iau_dp RTL assertion check when generating
    //interruption, it gives false positive errors otherwise
    if (uvm_root::get().find("uvm_test_top").get_type_name() == "iau_irq_test") begin
      `uvm_info("top", "IRQ test, disabling some assertions", UVM_LOW)
      $assertoff(0, dut.i_iau_dp);
    end


    //QUESTA/vsim gives assertion error because of axi_protocol_checker param ADDR_WIDTH = 32, but IAU uses only 28 bits
    //so the MSB are Z. forcing the signals here because could not found a easy way to override parameters in vsim
    force dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.AWADDR[31:28] = 3'd0;
    force dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.ARADDR[31:28] = 3'd0;
  end

  // =============================================================================================================
  // Coverage for the ALU sum
  covergroup cg_all_ones_to_zeros with function sample(input logic [31:0] signal);
    option.per_instance = 1;
    coverpoint signal {
      bins all_ones = {32'hFFFFFFFF};
      bins all_zeros = {32'h00000000};
      bins all_ones_to_all_zeros = (32'hFFFFFFFF => 32'h00000000);
      wildcard bins byte0_toggle_hi_lo = (32'h??????FF => 32'h??????00);
      wildcard bins byte1_toggle_hi_lo = (32'h????FF?? => 32'h????00??);
      wildcard bins byte2_toggle_hi_lo = (32'h??FF???? => 32'h??00????);
      wildcard bins byte3_toggle_hi_lo = (32'hFF?????? => 32'h00??????);
    }
  endgroup

  cg_all_ones_to_zeros addr_ovf_cov[aic_common_pkg::AIC_PWORD_SIZE];

  for(genvar ii = 0; ii < aic_common_pkg::AIC_PWORD_SIZE; ii++) begin
    initial addr_ovf_cov[ii] = new();

    always @(dut.i_iau_dp.u_pixel_dp[ii].alu_sum) begin
      addr_ovf_cov[ii].sample(dut.i_iau_dp.u_pixel_dp[ii].alu_sum);
    end
  end
  // =============================================================================================================


  initial
  begin
    run_test ();
  end


endmodule : hdl_top
