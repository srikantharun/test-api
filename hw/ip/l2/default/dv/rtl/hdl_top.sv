`define AXI_VIP
`define APB_VIP
`define DUT dut
`define MEM_DEPTH 4096
`include "uvm_macros.svh"

module hdl_top;
  // Time unit and precision
    `timescale 1ps/1ps;

  // Packages import
  import uvm_pkg::*;
  import l2_pkg::*;
  import l2_uvm_pkg::*;
  import l2_cfg_pkg::*;
  import l2_verif_tb_pkg::*;
  import chip_pkg::*;

  //AXI Packages
  `ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  `endif
 
  //APB Packages
  `ifdef APB_VIP
  import svt_apb_uvm_pkg::*;
  `endif
 
  //`include "axi4pc/bind_l2.svh"
  `include "axi_perf_tracker/bind_axi_tracker_l2.svh"
  // =============================================================================================================
  // CLK RST Generation
  // =============================================================================================================
  // Clock and reset signals
  logic clk_en;
  logic clk;
  logic ref_clk_en;
  logic ref_clk;
  logic axi_rst;
  logic apb_rst;

  l2_power_if tb_cfg_if ();  //interface
  svt_axi_if axi_if ();  // VIP Interface instance representing the AXI system
  axi_reset_if axi_reset_if ();  // AXI reset interface
  svt_apb_if apb_if ();  // VIP Interface instance representing the APB system
  apb_reset_if apb_reset_if ();  // APB reset interface

  int aicore_freq_mhz = 1200;   //1.2GHz //give value in MHz
  int ref_freq_mhz = 50;        //50MHz //give value in MHz
  time aicore_tol_ps = 10;

  axe_clk_generator  u_axe_clk_generator (
      .i_enable(clk_en),
      .o_clk(clk)
  );

  axe_clk_generator u_axe_ref_clk_generator (
      .i_enable(ref_clk_en),
      .o_clk(ref_clk)
  );
  assign tb_cfg_if.ref_clk = ref_clk;

  axe_rst_generator u_apb_rst_generator (
      .i_clk(ref_clk),
      .o_rst(apb_rst)
  );
   assign tb_cfg_if.apb_rst = apb_rst;

  axe_rst_generator u_axi_rst_generator (
      .i_clk(clk),
      .o_rst(axi_rst)
  );

  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(aicore_freq_mhz), .duty(50));
    u_axe_ref_clk_generator.set_clock(.freq_mhz(ref_freq_mhz), .duty(50));
    clk_en = 1'b1;
    ref_clk_en = 1'b1;
    u_apb_rst_generator.async_rst(.duration_ns(100));
    u_axi_rst_generator.async_rst(.duration_ns(50));
  end

  


  realtime CLK_PERIOD = 0.8333ns;  // 1.2GHz
  //Datatypes
  // Clock and reset signals
  logic                                  tb_clk;
  logic                                  i_ref_clk;
  bit                                    rst_n;
  bit                                    ao_rst_n;
  logic                                  o_noc_rst_n;
  //Isolation interface signals
  logic                                  o_noc_async_idle_req;
  logic                                  o_noc_async_idle_ack;
  logic                                  o_noc_async_idle_val;
  logic                                  o_noc_clken;
  // AXI write address channel
  logic                                  awvalid;
  chip_axi_addr_t                        awaddr;
  logic [        L2_AXI_ID_WIDTH-1:0]    awid;
  l2_axi_len_t                           awlen;
  l2_axi_size_t                          awsize;
  l2_axi_burst_t                         awburst;
  logic                                  awlock;
  l2_axi_cache_t                         awcache;
  l2_axi_prot_t                          awprot;
  logic                                  awready;
  // AXI write data channel
  logic                                  wvalid;
  logic                                  wlast;
  logic [      L2_AXI_DATA_WIDTH-1:0]    wdata;
  logic [     L2_AXI_STRB_WIDTH-1:0]     wstrb;
  logic                                  wready;
  // AXI write response channel
  logic                                  bvalid;
  logic [        L2_AXI_ID_WIDTH-1:0]    bid;
  l2_axi_resp_t                          bresp;
  logic                                  bready;
  // AXI read address channel
  logic                                  arvalid;
  chip_axi_addr_t                        araddr;
  logic [        L2_AXI_ID_WIDTH-1:0]    arid;
  l2_axi_len_t                           arlen;
  l2_axi_size_t                          arsize;
  l2_axi_burst_t                         arburst;
  logic                                  arlock;
  l2_axi_cache_t                         arcache;
  l2_axi_prot_t                          arprot;
  logic                                  arready;
  // AXI read data/response channel
  logic                                  rvalid;
  logic                                  rlast;
  logic [        L2_AXI_ID_WIDTH-1:0]    rid;
  logic [      L2_AXI_DATA_WIDTH-1:0]    rdata;
  l2_axi_resp_t                          rresp;
  logic                                  rready;
      
  `ifdef AXI_VIP
     assign axi_if.common_aclk          = clk;
     assign axi_if.master_if[0].aclk    = clk;
     assign axi_if.slave_if[0].aclk     = clk;

     assign axi_reset_if.clk            = clk;
     assign axi_reset_if.reset          = axi_rst;
     assign axi_if.master_if[0].aresetn = ~axi_reset_if.reset;
     assign axi_if.slave_if[0].aresetn  = ~axi_reset_if.reset;
  `endif
  
  `ifdef APB_VIP
     assign apb_reset_if.pclk           = ref_clk;
     assign apb_reset_if.presetn        = ~apb_rst;
     assign apb_if.pclk                 = ref_clk;
     assign apb_if.presetn              = apb_reset_if.presetn;
  `endif

    
  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
  
  `ifdef AXI_VIP
    assign awvalid = axi_if.master_if[0].awvalid;
    assign awaddr  = axi_if.master_if[0].awaddr;
    assign awid    = axi_if.master_if[0].awid;
    assign awlen   = axi_if.master_if[0].awlen;
    assign awsize  = axi_if.master_if[0].awsize;
    assign awburst = axi_if.master_if[0].awburst;
    assign awlock  = axi_if.master_if[0].awlock;
    assign awcache = axi_if.master_if[0].awcache;
    assign awprot  = axi_if.master_if[0].awprot;

    assign axi_if.master_if[0].awready = awready;

    assign wvalid  = axi_if.master_if[0].wvalid;
    assign wlast   = axi_if.master_if[0].wlast;
    assign wdata   = axi_if.master_if[0].wdata;
    assign wstrb   = axi_if.master_if[0].wstrb;

    assign axi_if.master_if[0].wready = wready;

    assign axi_if.master_if[0].bvalid = bvalid;
    assign axi_if.master_if[0].bid    = bid;
    assign axi_if.master_if[0].bresp  = bresp;

    assign bready  = axi_if.master_if[0].bready;
    assign arvalid = axi_if.master_if[0].arvalid;
    assign araddr  = axi_if.master_if[0].araddr;
    assign arid    = axi_if.master_if[0].arid;
    assign arlen   = axi_if.master_if[0].arlen;
    assign arsize  = axi_if.master_if[0].arsize;
    assign arburst = axi_if.master_if[0].arburst;
    assign arlock  = axi_if.master_if[0].arlock;
    assign arcache = axi_if.master_if[0].arcache;
    assign arprot  = axi_if.master_if[0].arprot;

    assign axi_if.master_if[0].arready = arready;

    assign axi_if.master_if[0].rvalid = rvalid;
    assign axi_if.master_if[0].rlast  = rlast;
    assign axi_if.master_if[0].rid    = rid;
    assign axi_if.master_if[0].rdata  = rdata;
    assign axi_if.master_if[0].rresp  = rresp;

    assign rready  = axi_if.master_if[0].rready;

   // Slave DUT
    assign  axi_if.slave_if[0].awvalid = `DUT.i_ht_axi_s_awvalid;
    assign  axi_if.slave_if[0].awaddr  = `DUT.i_ht_axi_s_awaddr;
    assign  axi_if.slave_if[0].awid    = `DUT.i_ht_axi_s_awid;
    assign  axi_if.slave_if[0].awlen   = `DUT.i_ht_axi_s_awlen;
    assign  axi_if.slave_if[0].awsize  = `DUT.i_ht_axi_s_awsize;
    assign  axi_if.slave_if[0].awburst = `DUT.i_ht_axi_s_awburst;
    assign  axi_if.slave_if[0].awlock  = `DUT.i_ht_axi_s_awlock;
    assign  axi_if.slave_if[0].awcache = `DUT.i_ht_axi_s_awcache;
    assign  axi_if.slave_if[0].awprot  = `DUT.i_ht_axi_s_awprot;
    assign  axi_if.slave_if[0].awready = `DUT.o_ht_axi_s_awready;
    assign  axi_if.slave_if[0].wvalid  = `DUT.i_ht_axi_s_wvalid;
    assign  axi_if.slave_if[0].wlast   = `DUT.i_ht_axi_s_wlast;
    assign  axi_if.slave_if[0].wdata   = `DUT.i_ht_axi_s_wdata;
    assign  axi_if.slave_if[0].wstrb   = `DUT.i_ht_axi_s_wstrb;
    assign  axi_if.slave_if[0].wready  = `DUT.o_ht_axi_s_wready;
    assign  axi_if.slave_if[0].bvalid  = `DUT.o_ht_axi_s_bvalid;
    assign  axi_if.slave_if[0].bid     = `DUT.o_ht_axi_s_bid;
    assign  axi_if.slave_if[0].bresp   = `DUT.o_ht_axi_s_bresp;
    assign  axi_if.slave_if[0].bready  = `DUT.i_ht_axi_s_bready;
    assign  axi_if.slave_if[0].arvalid = `DUT.i_ht_axi_s_arvalid;
    assign  axi_if.slave_if[0].araddr  = `DUT.i_ht_axi_s_araddr;
    assign  axi_if.slave_if[0].arid    = `DUT.i_ht_axi_s_arid;
    assign  axi_if.slave_if[0].arlen   = `DUT.i_ht_axi_s_arlen;
    assign  axi_if.slave_if[0].arsize  = `DUT.i_ht_axi_s_arsize;
    assign  axi_if.slave_if[0].arburst = `DUT.i_ht_axi_s_arburst;
    assign  axi_if.slave_if[0].arlock  = `DUT.i_ht_axi_s_arlock;
    assign  axi_if.slave_if[0].arcache = `DUT.i_ht_axi_s_arcache;
    assign  axi_if.slave_if[0].arprot  = `DUT.i_ht_axi_s_arprot;
    assign  axi_if.slave_if[0].arready = `DUT.o_ht_axi_s_arready;
    assign  axi_if.slave_if[0].rvalid  = `DUT.o_ht_axi_s_rvalid;
    assign  axi_if.slave_if[0].rlast   = `DUT.o_ht_axi_s_rlast;
    assign  axi_if.slave_if[0].rid     = `DUT.o_ht_axi_s_rid;
    assign  axi_if.slave_if[0].rdata   = `DUT.o_ht_axi_s_rdata;
    assign  axi_if.slave_if[0].rresp   = `DUT.o_ht_axi_s_rresp;
    assign  axi_if.slave_if[0].rready  = `DUT.i_ht_axi_s_rready;
  `endif
   
    // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
  l2_p dut (
    // Clock and reset signals
    .i_clk                    (clk),
    .i_ao_rst_n               (apb_reset_if.presetn),
    .i_ref_clk                (ref_clk),
    .i_global_rst_n           (~axi_reset_if.reset),
    .o_noc_rst_n              (o_noc_rst_n),
    //isolation interface 
    .o_noc_async_idle_req     (o_noc_async_idle_req),
    .i_noc_async_idle_ack     (i_noc_async_idle_ack),
    .i_noc_async_idle_val     (i_noc_async_idle_val),
    .o_noc_clken              (o_noc_clken),
    // Input/Outputs
    .i_ht_axi_s_awvalid       (awvalid),
    .i_ht_axi_s_awaddr        (awaddr),
    .i_ht_axi_s_awid          (awid),
    .i_ht_axi_s_awlen         (awlen),
    .i_ht_axi_s_awsize        (awsize),
    .i_ht_axi_s_awburst       (awburst),
    .i_ht_axi_s_awlock        (awlock),
    .i_ht_axi_s_awcache       (awcache),
    .i_ht_axi_s_awprot        (awprot),
    .o_ht_axi_s_awready       (awready),
    .i_ht_axi_s_wvalid        (wvalid),
    .i_ht_axi_s_wlast         (wlast),
    .i_ht_axi_s_wdata         (wdata),
    .i_ht_axi_s_wstrb         (wstrb),
    .o_ht_axi_s_wready        (wready),
    .o_ht_axi_s_bvalid        (bvalid),
    .o_ht_axi_s_bid           (bid),
    .o_ht_axi_s_bresp         (bresp),
    .i_ht_axi_s_bready        (bready),
    .i_ht_axi_s_arvalid       (arvalid),
    .i_ht_axi_s_araddr        (araddr),
    .i_ht_axi_s_arid          (arid),
    .i_ht_axi_s_arlen         (arlen),
    .i_ht_axi_s_arsize        (arsize),
    .i_ht_axi_s_arburst       (arburst),
    .i_ht_axi_s_arlock        (arlock),
    .i_ht_axi_s_arcache       (arcache),
    .i_ht_axi_s_arprot        (arprot),
    .o_ht_axi_s_arready       (arready),
    .o_ht_axi_s_rvalid        (rvalid),
    .o_ht_axi_s_rlast         (rlast),
    .o_ht_axi_s_rid           (rid),
    .o_ht_axi_s_rdata         (rdata),
    .o_ht_axi_s_rresp         (rresp),
    .i_ht_axi_s_rready        (rready),
    .i_cfg_apb4_s_paddr       (apb_if.paddr),
    .i_cfg_apb4_s_pwdata      (apb_if.pwdata),
    .i_cfg_apb4_s_pwrite      (apb_if.pwrite),
    .i_cfg_apb4_s_psel        (apb_if.psel[0]),
    .i_cfg_apb4_s_penable     (apb_if.penable),
    .i_cfg_apb4_s_pstrb       (apb_if.pstrb),
    .i_cfg_apb4_s_pprot       (apb_if.pprot),
    .o_cfg_apb4_s_pready      (apb_if.pready[0]),
    .o_cfg_apb4_s_prdata      (apb_if.prdata[0]),
    .o_cfg_apb4_s_pslverr     (apb_if.pslverr[0]),
   `ifndef TARGET_DFT
    .test_clk('0),
    .test_mode('0),
    .edt_update('0),
    .scan_en('0),
    .scan_in('0),
    .scan_out(),
    .bisr_clk('0),
    .bisr_reset('1),
    .bisr_shift_en('0),
    .bisr_si('0),
    .bisr_so()
   `else
    .ijtag_tck('0),
    .ijtag_reset('0),
    .ijtag_sel('0),
    .ijtag_ue('0),
    .ijtag_se('0),
    .ijtag_ce('0),
    .ijtag_si('0),
    .ijtag_so()
   `endif
    );
 
  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  
  initial
    begin
      import uvm_pkg::uvm_config_db;
      `ifdef AXI_VIP
         // Set the reset interface on the virtual sequencer
         uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);
         uvm_config_db#(virtual apb_reset_if.apb_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.apb_sequencer", "reset_mp", apb_reset_if.apb_reset_modport);
         // =============================================================================================================
         // Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI
         // System ENV and the DUT through the AXI interface.
         // =============================================================================================================
         uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.axi_system_env", "vif", axi_if);
         uvm_config_db#(virtual svt_apb_if)::set(uvm_root::get(), "uvm_test_top.env.m_apb_system_env", "vif", apb_if);

      `endif
    end

  initial
     begin
       `ifdef APB_VIP
         uvm_config_db#(virtual apb_reset_if.apb_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.apb_sequencer", "reset_mp",apb_reset_if.apb_reset_modport);
         uvm_config_db#(svt_apb_vif)::set(uvm_root::get(), "uvm_test_top.env.m_apb_system_env", "vif",apb_if);
       `endif
         uvm_config_db#(virtual l2_power_if)::set(uvm_root::get(), "*", "tb_cfg_if", tb_cfg_if);
     end


  //Preloading memory with mem_write function
  initial begin
    @(posedge ref_clk);
    wait (axi_rst === 0);
    for (int i=0 ;i<`MEM_DEPTH;i++) begin
      // bank 0
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[0].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 1
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[1].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 2
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[2].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 3
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[3].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 4
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[4].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 5
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[5].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 6
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[6].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 7
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[7].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 8
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[8].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 9
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[9].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 10
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[10].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 11
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[11].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 12
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[12].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 13
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[13].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 14
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[14].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      // bank 15
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[0].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[0].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[0].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[0].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[1].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[1].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[1].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[1].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[2].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[2].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[2].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[2].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);

      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[3].u_l2_ram.g_sram[0].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[3].u_l2_ram.g_sram[1].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[3].u_l2_ram.g_sram[2].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
      hdl_top.dut.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[15].u_l2_bank.g_ram[3].u_l2_ram.g_sram[3].u_l2_ram_wrapper.gen_macro.u_macro.u_mem.write_mem(i,'0);
    end
  end


  initial begin
    run_test();
  end

endmodule:hdl_top
