`define NUM_AXI_INITIATORS  14
`define NUM_AXI_TARGETS     12
`define DUT pve_fabric

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import pve_fabric_uvm_pkg::*;
  import pve_pkg::*;

  // Axi Checkers
  `include "axi4pc/bind_europa_pve_fabric.svh"

  `include "../uvm/fabric_csl_tb_define.sv"

  realtime CLK_PERIOD_1200  = 0.83ns;   // 1200MHz  --> 0.83ns

  // VIP Interface instanc
  svt_axi_if          axi_if();
  axi_reset_if        axi_reset_if();

  logic clk_1_2GHz;
  logic rst_n;

  bit i_rst_n;
  bit i_clk;
  bit [`AXI_HP_ADDR_WIDTH - 1 : 0] i_base_addr;

  // =============================================================================================================
  // RTL <-> MVIP connections
  // create_axi_slv ARGS - (tot_rtl_slv_if_num, rtl_signal_name, addr_w, data_w, id_w, len_w)
  // bind_axi_slv ARGS - (rtl_slv_if_num, rtl_signal_name, vip_intf)
  // =============================================================================================================

  `create_axi_slv(PVE_FABRIC_N_LT_S_EXT_PORTS, lt_axi_s, 40, 64, 4, 8)
  `create_axi_slv(PVE_FABRIC_N_HT_S_EXT_PORTS, ht_axi_s, 40, 512, 8, 8)

  genvar slv_num;
  generate
    for (slv_num=0; slv_num < PVE_FABRIC_N_LT_S_EXT_PORTS + PVE_FABRIC_N_HT_S_EXT_PORTS; slv_num++) begin
      if (slv_num < PVE_FABRIC_N_LT_S_EXT_PORTS) begin
      `interface_connect_axi_slv(slv_num, lt_axi_s, axi_if.master_if[slv_num] )
      end else begin
      `interface_connect_axi_slv(slv_num - PVE_FABRIC_N_LT_S_EXT_PORTS, ht_axi_s, axi_if.master_if[slv_num] )
      end
      if (slv_num < PVE_FABRIC_N_LT_S_EXT_PORTS  && slv_num != 9) 
        assign  i_lt_axi_s_awatop[slv_num]      = axi_if.master_if[slv_num].awatop;
     end
  endgenerate

  // =============================================================================================================
  // RTL <-> SVIP connections
  // ARGS - (rtl_mst_if_num, rtl_signal_name, addr_w, data_w, id_w, len_w, vip_intf)
  // =============================================================================================================

  `create_axi_mst(PVE_FABRIC_N_LT_M_EXT_PORTS, lt_axi_m, 40, 64, 8, 8)
  `create_axi_mst(PVE_FABRIC_N_HT_M_EXT_PORTS, ht_axi_m, 40, 512, 11, 8)

  genvar mst_num;
  generate
    for (mst_num=0; mst_num < PVE_FABRIC_N_LT_M_EXT_PORTS + PVE_FABRIC_N_HT_M_EXT_PORTS; mst_num++) begin
      if (mst_num < PVE_FABRIC_N_LT_M_EXT_PORTS) begin
      `interface_connect_axi_mst(mst_num, lt_axi_m, axi_if.slave_if[mst_num] )
      end else begin
      `interface_connect_axi_mst(mst_num - PVE_FABRIC_N_LT_M_EXT_PORTS, ht_axi_m, axi_if.slave_if[mst_num] )
      end
      if (mst_num < PVE_FABRIC_N_LT_M_EXT_PORTS) 
        assign  axi_if.slave_if[mst_num].awatop = o_lt_axi_m_awatop[mst_num];
     end
  endgenerate

  assign i_rst_n = rst_n;
  assign i_clk = clk_1_2GHz;
  assign i_base_addr = `PVE_BASE;

  // =============================================================================================================
  // Assign the reset and clock pins
  // =============================================================================================================
  assign rst_n                                    = axi_reset_if.reset;
  assign axi_reset_if.clk                         = clk_1_2GHz;
  assign axi_if.common_aclk                       = clk_1_2GHz;
  //Assign CLK and RST for all INITs and TARGs
  genvar i;
  generate
    for (i = 0; i < `NUM_AXI_INITIATORS; i++) begin
      assign axi_if.master_if[i].aclk     = clk_1_2GHz;
      assign axi_if.master_if[i].aresetn  = rst_n;
    end
  endgenerate
  genvar j;
  generate
    for (j = 0; j < `NUM_AXI_TARGETS; j++) begin
      assign axi_if.slave_if[j].aclk      = clk_1_2GHz;
      assign axi_if.slave_if[j].aresetn   = rst_n;
    end
  endgenerate

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate clock
  always begin
    clk_1_2GHz <= 1;
    #(CLK_PERIOD_1200 / 2);
    clk_1_2GHz <= 0;
    #(CLK_PERIOD_1200 / 2);
  end

  // =============================================================================================================
  // Instantiate DUT
  // =============================================================================================================
  `DUT dut (.*);
  
  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
    // Set the reset interface on the virtual sequencer
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(
    uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "*", "vif", axi_if);
  end

  // =============================================================================================================
  // Invoking the test
  // Run test
  // =============================================================================================================
  initial
  begin
    run_test ();
  end

endmodule : hdl_top

