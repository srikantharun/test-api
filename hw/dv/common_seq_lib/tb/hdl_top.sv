`define NUM_AXI_INITIATORS 1 //= noc_init_e.num();
`define NUM_AXI_TARGETS    1 //= noc_targ_e.num();

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import common_seq_lib_tests_pkg::*;
  import axi_pkg::*;
  import axe_axi_default_types_pkg::*;

  `include "../uvm/env/common_seq_lib_tb_define.sv"

  realtime CLK_PERIOD_800 = 1.25ns;  // 800MHz --> 1.25ns
  realtime CLK_PERIOD_600 = 1.666ns;
  realtime CLK_PERIOD_100 = 10ns;  //100Mhz --> slow_clk

  // VIP Interface instanc
  svt_axi_if          axi_if();
  axi_reset_if        axi_reset_if();

  logic clk_800MHz;
  logic clk_600MHz;
  logic clk_100MHz;
  logic rst_n;

  bit i_rst_n;
  bit i_clk;

  // =============================================================================================================
  // Connect MVIP <-> SVIP 
  // =============================================================================================================

`ifdef AXE_AXI_ISOLATE
  logic i_isolate, o_isolated;
  assign i_isolate = 0;
`endif

`ifdef AXE_AXI_ERR_SUB
  `create_and_assign_mst_connections(4, 40, 4, 64, 8)
  `assign_slv_mon_to_axi_err_if
`elsif AXE_AXI_DEMUX
  logic [3:0] i_axi_s_aw_select, i_axi_s_ar_select; //FIXME: use define for signal width, it depends on SLV_NUM width
  `create_and_assign_mst_connections(4, 40, 4, 64, 8)
  `create_demux_slv_conn(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
  genvar slv_num;
  generate
    for (slv_num=0; slv_num < `SLV_NUM; slv_num++) begin
      `assign_demux_slv_conn(slv_num, `ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
    end
  endgenerate
  assign i_axi_s_aw_select = 0;
  assign i_axi_s_ar_select = 0;
`elsif AXE_AXI_MUX
  `create_and_assign_slv_connections(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
  `create_mux_mst_conn(`ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 8)
  genvar mst_num;
  generate
    for (mst_num=0; mst_num < `MST_NUM; mst_num++) begin
      `assign_mux_mst_conn(mst_num, `ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 8)
    end
  endgenerate
`elsif AXE_AXI_ATU
  `create_and_assign_mst_connections(`ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 8)
  `create_and_assign_slv_connections(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
  atu_entry_t    i_entries[axe_axi_default_types_pkg::AtuNumEntries];
  logic      i_bypass;
  assign i_entries[0].first = 0;
  assign i_entries[0].last = 'hFFFF;
  assign i_entries[0].base = 'h0;
  assign i_entries[0].valid = 1;
  assign i_entries[0].read_only = 1;
  assign i_entries[1].first = 0;
  assign i_entries[1].last = 'hFFFF;
  assign i_entries[1].base = 'h0;
  assign i_entries[1].valid = 1;
  assign i_entries[1].read_only = 1;
  assign i_bypass = 1;
`elsif AXE_AXI_DW_CONVERTER
  `create_and_assign_mst_connections(`ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 64)
  `create_and_assign_slv_connections(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
`elsif AXE_AXI_ID_REMAP
  `create_and_assign_mst_connections(`ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 8)
  `create_and_assign_slv_connections(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
`elsif AXE_AXI_MODIFY_ADDRESS
  axi_addr_40_t i_axi_s_aw_addr, i_axi_s_ar_addr;
  `create_and_assign_mst_connections(`ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 8)
  `create_and_assign_slv_connections(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
  assign i_axi_s_aw_addr = axi_if.master_if[0].awaddr;
  assign i_axi_s_ar_addr = axi_if.master_if[0].araddr;
`elsif DUT 
  `create_and_assign_mst_connections(`ID_M_W, `ADDR_M_W, 4, `DATA_M_W, 8)
  `create_and_assign_slv_connections(`ID_S_W, `ADDR_S_W, 4, `DATA_S_W, 8)
`else
  assign axi_if.slave_if[0].awvalid   = axi_if.master_if[0].awvalid;
  assign axi_if.slave_if[0].awaddr    = axi_if.master_if[0].awaddr;
  assign axi_if.slave_if[0].awid      = axi_if.master_if[0].awid;
  assign axi_if.slave_if[0].awlen     = axi_if.master_if[0].awlen;
  assign axi_if.slave_if[0].awsize    = axi_if.master_if[0].awsize;
  assign axi_if.slave_if[0].awburst   = axi_if.master_if[0].awburst;
  assign axi_if.slave_if[0].awlock    = axi_if.master_if[0].awlock;
  assign axi_if.slave_if[0].awcache   = axi_if.master_if[0].awcache;
  assign axi_if.slave_if[0].awprot    = axi_if.master_if[0].awprot;
  assign axi_if.master_if[0].awready  = axi_if.slave_if[0].awready;
  assign axi_if.slave_if[0].wvalid    = axi_if.master_if[0].wvalid;
  assign axi_if.slave_if[0].wlast     = axi_if.master_if[0].wlast;
  assign axi_if.slave_if[0].wdata     = axi_if.master_if[0].wdata;
  assign axi_if.slave_if[0].wstrb     = axi_if.master_if[0].wstrb;
  assign axi_if.master_if[0].wready   = axi_if.slave_if[0].wready;
  assign axi_if.master_if[0].bvalid   = axi_if.slave_if[0].bvalid;
  assign axi_if.master_if[0].bid      = axi_if.slave_if[0].bid;
  assign axi_if.master_if[0].bresp    = axi_if.slave_if[0].bresp;
  assign axi_if.slave_if[0].bready    = axi_if.master_if[0].bready;
  assign axi_if.slave_if[0].arvalid   = axi_if.master_if[0].arvalid;
  assign axi_if.slave_if[0].araddr    = axi_if.master_if[0].araddr;
  assign axi_if.slave_if[0].arid      = axi_if.master_if[0].arid;
  assign axi_if.slave_if[0].arlen     = axi_if.master_if[0].arlen;
  assign axi_if.slave_if[0].arsize    = axi_if.master_if[0].arsize;
  assign axi_if.slave_if[0].arburst   = axi_if.master_if[0].arburst;
  assign axi_if.slave_if[0].arlock    = axi_if.master_if[0].arlock;
  assign axi_if.slave_if[0].arcache   = axi_if.master_if[0].arcache;
  assign axi_if.slave_if[0].arprot    = axi_if.master_if[0].arprot;
  assign axi_if.master_if[0].arready  = axi_if.slave_if[0].arready;
  assign axi_if.master_if[0].rvalid   = axi_if.slave_if[0].rvalid;
  assign axi_if.master_if[0].rlast    = axi_if.slave_if[0].rlast;
  assign axi_if.master_if[0].rid      = axi_if.slave_if[0].rid;
  assign axi_if.master_if[0].rdata    = axi_if.slave_if[0].rdata;
  assign axi_if.master_if[0].rresp    = axi_if.slave_if[0].rresp;
  assign axi_if.slave_if[0].rready    = axi_if.master_if[0].rready;

  assign axi_if.slave_if[0].awqos     = axi_if.master_if[0].awqos;
  assign axi_if.slave_if[0].arqos     = axi_if.master_if[0].arqos;

  assign axi_if.slave_if[0].aruser    = axi_if.master_if[0].aruser;
  assign axi_if.slave_if[0].awuser    = axi_if.master_if[0].awuser;
  assign axi_if.slave_if[0].wuser     = axi_if.master_if[0].wuser;
  assign axi_if.master_if[0].ruser    = axi_if.slave_if[0].ruser;
  assign axi_if.master_if[0].buser    = axi_if.slave_if[0].buser;
`endif

  // =============================================================================================================
  // Assign the reset and clock pins
  // =============================================================================================================
  assign rst_n                        = axi_reset_if.reset;
  assign axi_reset_if.clk             = clk_800MHz;
  assign axi_if.master_if[0].aresetn  = rst_n;
  assign axi_if.master_if[0].aclk     = clk_800MHz;
  assign axi_if.slave_if[0].aresetn   = rst_n;
  assign axi_if.slave_if[0].aclk      = clk_800MHz;
  assign axi_if.common_aclk           = clk_800MHz;


  assign i_clk = clk_800MHz;
  assign i_rst_n = rst_n;

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate the fast clock
  always begin
    clk_800MHz <= 1;
    #(CLK_PERIOD_800 / 2);
    clk_800MHz <= 0;
    #(CLK_PERIOD_800 / 2);
  end

  always begin
    clk_600MHz <= 1;
    #(CLK_PERIOD_600 / 2);
    clk_600MHz <= 0;
    #(CLK_PERIOD_600 / 2);
  end

  // Generate the slow clock
  always begin
    clk_100MHz <= 1;
    #(CLK_PERIOD_100 / 2);
    clk_100MHz <= 0;
    #(CLK_PERIOD_100 / 2);
  end
 
`ifdef DUT
  // =============================================================================================================
  // Instantiate DUT
  // =============================================================================================================
`ifdef AXE_AXI_ATU
  `DUT #(.axi_w_t(axe_axi_default_types_pkg::axi_w_64_8_4_t)) dut (.*);
`elsif AXE_AXI_MODIFY_ADDRESS
  `DUT #(.axi_w_t(axe_axi_default_types_pkg::axi_w_64_8_4_t)) dut (.*);
`elsif AXE_AXI_DEMUX
  `DUT #(.NumPorts(`SLV_NUM)) dut (.*);
`elsif AXE_AXI_MUX
  `DUT #(.NumPorts(`MST_NUM),
         .axi_m_aw_t(axi_aw_8_40_4_t),
         .axi_m_b_t(axi_b_8_4_t),
         .axi_m_ar_t(axi_ar_8_40_4_t),
         .axi_m_r_t(axi_r_8_64_4_t)
        ) dut (.*);
`else
  `DUT  dut (.*);
`endif
`endif
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

