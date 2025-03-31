
`timescale 1ps/1ps
`define AXI_VIP

realtime CLK_PERIOD = 833;
module hdl_top();

    // Packages import

    import uvm_pkg::*;
    import sys_spm_uvm_pkg::*;
    import spm_uvm_pkg::*;
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import svt_apb_uvm_pkg::*;
    import sys_spm_test_pkg::*;
    import axe_tcl_sram_pkg::*;

    `include "uvm_macros.svh"


    localparam spm_config_t spm_config = '{ // Types
                                            spm_axi_data_width:64,
                                            spm_axi_strb_width:8,
                                            spm_axi_addr_width:40,
                                            spm_axi_id_width:4,
                                            spm_axi_atop_width:6,
                                            // Memory stuff
                                            spm_mem_size_kb:8192,
                                            spm_mem_macro_depth_k: 8,
                                            spm_nb_banks:4,
                                            spm_nb_sub_banks:4,
                                            spm_nb_mini_banks:4,
                                            spm_nb_srams_per_mini_bank:2,
                                            spm_nb_req_pipeline:3,
                                            spm_nb_rsp_pipeline:3,
                                            // ECC
                                            ecc_protection_en:1
                                };


    // =========================
    // Datatypes
    typedef logic [spm_config.spm_axi_data_width-1:0]         sys_spm_axi_data_t;
    typedef logic [spm_config.spm_axi_addr_width-1:0]         sys_spm_axi_addr_t;
    typedef logic [spm_config.spm_axi_strb_width-1:0]         sys_spm_axi_strb_t;
    typedef logic [spm_config.spm_axi_id_width-1:0]           sys_spm_axi_id_t;
    typedef logic [spm_config.spm_axi_atop_width-1:0]         sys_spm_axi_atop_t;
    typedef axi_pkg::axi_len_t    sys_spm_axi_len_t;
    typedef axi_pkg::axi_size_t   sys_spm_axi_size_t;
    typedef axi_pkg::axi_burst_t  sys_spm_axi_burst_t;
    typedef axi_pkg::axi_resp_t   sys_spm_axi_resp_t;
    typedef axi_pkg::axi_cache_t  sys_spm_axi_cache_t;
    typedef axi_pkg::axi_prot_t   sys_spm_axi_prot_t;

    logic clk;
    logic rst_n;
    string file;
    bit regression = 0;

    spm_pkg::spm_error_status_t scp_error_status;

    logic sys_spm_axi_awvalid;
    sys_spm_axi_addr_t sys_spm_axi_awaddr;
    sys_spm_axi_id_t sys_spm_axi_awid;
    sys_spm_axi_len_t sys_spm_axi_awlen;
    sys_spm_axi_size_t sys_spm_axi_awsize;
    sys_spm_axi_burst_t sys_spm_axi_awburst;

    sys_spm_axi_cache_t sys_spm_axi_awcache;
    sys_spm_axi_prot_t sys_spm_axi_awprot;
    logic sys_spm_axi_awlock;
    sys_spm_axi_atop_t      sys_spm_axi_awatop;

    logic sys_spm_axi_awready;

    logic sys_spm_axi_wvalid;
    logic sys_spm_axi_wlast;
    sys_spm_axi_data_t sys_spm_axi_wdata;
    sys_spm_axi_strb_t sys_spm_axi_wstrb;

    logic sys_spm_axi_wready;

    logic sys_spm_axi_bvalid;
    sys_spm_axi_id_t sys_spm_axi_bid;
    sys_spm_axi_resp_t sys_spm_axi_bresp;

    logic sys_spm_axi_bready;
    logic sys_spm_axi_arvalid;
    sys_spm_axi_addr_t sys_spm_axi_araddr;
    sys_spm_axi_id_t sys_spm_axi_arid;
    sys_spm_axi_len_t sys_spm_axi_arlen;
    sys_spm_axi_size_t sys_spm_axi_arsize;
    sys_spm_axi_burst_t sys_spm_axi_arburst;
    logic sys_spm_axi_arlock;
    sys_spm_axi_cache_t sys_spm_axi_arcache;
    sys_spm_axi_prot_t sys_spm_axi_arprot;

    logic sys_spm_axi_arready;

    logic sys_spm_axi_rvalid;
    logic sys_spm_axi_rlast;
    sys_spm_axi_id_t sys_spm_axi_rid;
    sys_spm_axi_data_t sys_spm_axi_rdata;
    sys_spm_axi_resp_t sys_spm_axi_rresp;

    logic sys_spm_axi_rready;



    chip_pkg::chip_syscfg_addr_t     sys_spm_apb_paddr;
    chip_pkg::chip_apb_syscfg_data_t sys_spm_apb_pwdata;
    logic                            sys_spm_apb_pwrite;
    logic                            sys_spm_apb_psel;
    logic                            sys_spm_apb_penable;
    chip_pkg::chip_apb_syscfg_strb_t sys_spm_apb_pstrb;
    logic  [3-1:0]                   sys_spm_apb_pprot;
    logic                            sys_spm_apb_pready;
    chip_pkg::chip_apb_syscfg_data_t sys_spm_apb_prdata;
    logic                            sys_spm_apb_pslverr;

    logic o_irq;

    int  spm_freq_mhz = 1200;
    time spm_tol_ps  = 10;
    bit  clk_en;


    // error related
    logic               spm_scp_ecc_disable;
    spm_pkg::spm_error_status_t spm_scp_error_status;
    logic               spm_irq;
    initial begin
        clk=1'b0;
        spm_scp_ecc_disable=1'b0;
    end



    // VIP Interface instance representing the AXI system
    svt_axi_if axi_if ();
    svt_apb_if apb_if ();

    // TB Interface instance to provide access to the reset signal
    axi_reset_if axi_reset_if ();
    apb_reset_if apb_reset_if ();

    spm_if spm_intf();

    // =============================================================================================================
    // CLK RST Instantitation
    // =============================================================================================================
    axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(clk)
                                          );

    axe_clk_assert u_axe_clk_assert(.clk(clk),
                    .rst_n(i_rst_n),
                    .freq_mhz(spm_freq_mhz),
                    .tol_ps  (spm_tol_ps)
                    );

    clk_if u_axe_clk_if(.clk(clk)
                    );

    assign apb_reset_if.pclk = clk;
    assign axi_reset_if.clk = clk;
    assign axi_if.common_aclk = clk;
    assign apb_if.pclk = clk;

    always @*
    begin

        axi_if.master_if[0].aresetn = axi_reset_if.reset;
        apb_if.presetn = apb_reset_if.presetn;

        // AXI write address channel
        sys_spm_axi_awvalid    = axi_if.master_if[0].awvalid;
        sys_spm_axi_awaddr     = axi_if.master_if[0].awaddr;
        sys_spm_axi_awid       = axi_if.master_if[0].awid;
        sys_spm_axi_awlen      = axi_if.master_if[0].awlen;
        sys_spm_axi_awsize     = axi_if.master_if[0].awsize;
        sys_spm_axi_awburst    = axi_if.master_if[0].awburst;
        sys_spm_axi_awlock     = axi_if.master_if[0].awlock;
        sys_spm_axi_awcache    = axi_if.master_if[0].awcache;
        sys_spm_axi_awprot     = axi_if.master_if[0].awprot;
        sys_spm_axi_awatop     = axi_if.master_if[0].awatop;

        axi_if.master_if[0].awready = sys_spm_axi_awready;

        // AXI write data channel
        sys_spm_axi_wvalid  = axi_if.master_if[0].wvalid;
        sys_spm_axi_wlast   = axi_if.master_if[0].wlast;
        sys_spm_axi_wdata   = axi_if.master_if[0].wdata;
        sys_spm_axi_wstrb   = axi_if.master_if[0].wstrb;

        axi_if.master_if[0].wready = sys_spm_axi_wready;

        // AXI write response channel
        axi_if.master_if[0].bvalid = sys_spm_axi_bvalid;
        axi_if.master_if[0].bid    = sys_spm_axi_bid;
        axi_if.master_if[0].bresp  = sys_spm_axi_bresp;

        // AXI read address channel
        sys_spm_axi_bready  = axi_if.master_if[0].bready;
        sys_spm_axi_arvalid = axi_if.master_if[0].arvalid;
        sys_spm_axi_araddr  = axi_if.master_if[0].araddr;
        sys_spm_axi_arid    = axi_if.master_if[0].arid;
        sys_spm_axi_arlen   = axi_if.master_if[0].arlen;
        sys_spm_axi_arsize  = axi_if.master_if[0].arsize;
        sys_spm_axi_arburst = axi_if.master_if[0].arburst;
        sys_spm_axi_arlock  = axi_if.master_if[0].arlock;
        sys_spm_axi_arcache = axi_if.master_if[0].arcache;
        sys_spm_axi_arprot  = axi_if.master_if[0].arprot;

        axi_if.master_if[0].arready = sys_spm_axi_arready;

        // AXI read data/response channel
        axi_if.master_if[0].rvalid = sys_spm_axi_rvalid;
        axi_if.master_if[0].rlast  = sys_spm_axi_rlast;
        axi_if.master_if[0].rid    = sys_spm_axi_rid;
        axi_if.master_if[0].rdata  = sys_spm_axi_rdata;
        axi_if.master_if[0].rresp  = sys_spm_axi_rresp;

        sys_spm_axi_rready  = axi_if.master_if[0].rready;




        axi_if.slave_if[0].aresetn = axi_reset_if.reset;

        // AXI write address channel
        axi_if.slave_if[0].awvalid = sys_spm_axi_awvalid;
        axi_if.slave_if[0].awaddr = sys_spm_axi_awaddr;
        axi_if.slave_if[0].awid = sys_spm_axi_awid;
        axi_if.slave_if[0].awlen = sys_spm_axi_awlen;
        axi_if.slave_if[0].awsize = sys_spm_axi_awsize;
        axi_if.slave_if[0].awburst = sys_spm_axi_awburst;
        axi_if.slave_if[0].awlock = sys_spm_axi_awlock;
        axi_if.slave_if[0].awcache = sys_spm_axi_awcache;
        axi_if.slave_if[0].awprot = sys_spm_axi_awprot;
        axi_if.master_if[0].awatop = sys_spm_axi_awatop;

        axi_if.slave_if[0].awready = sys_spm_axi_awready;

        // AXI write data channel
        axi_if.slave_if[0].wvalid = sys_spm_axi_wvalid;
        axi_if.slave_if[0].wlast = sys_spm_axi_wlast;
        axi_if.slave_if[0].wdata = sys_spm_axi_wdata;
        axi_if.slave_if[0].wstrb = sys_spm_axi_wstrb;

        axi_if.slave_if[0].wready = sys_spm_axi_wready;

        // AXI write response channel
        axi_if.slave_if[0].bvalid = sys_spm_axi_bvalid;
        axi_if.slave_if[0].bid    = sys_spm_axi_bid;
        axi_if.slave_if[0].bresp  = sys_spm_axi_bresp;

        // AXI read address channel
        axi_if.slave_if[0].bready = sys_spm_axi_bready;
        axi_if.slave_if[0].arvalid = sys_spm_axi_arvalid;
        axi_if.slave_if[0].araddr = sys_spm_axi_araddr;
        axi_if.slave_if[0].arid = sys_spm_axi_arid;
        axi_if.slave_if[0].arlen = sys_spm_axi_arlen;
        axi_if.slave_if[0].arsize = sys_spm_axi_arsize;
        axi_if.slave_if[0].arburst = sys_spm_axi_arburst;
        axi_if.slave_if[0].arlock = sys_spm_axi_arlock;
        axi_if.slave_if[0].arcache = sys_spm_axi_arcache;
        axi_if.slave_if[0].arprot = sys_spm_axi_arprot;

        axi_if.slave_if[0].arready = sys_spm_axi_arready;

        // AXI read data/response channel
        axi_if.slave_if[0].rvalid = sys_spm_axi_rvalid;
        axi_if.slave_if[0].rlast  = sys_spm_axi_rlast;
        axi_if.slave_if[0].rid    = sys_spm_axi_rid;
        axi_if.slave_if[0].rdata  = sys_spm_axi_rdata;
        axi_if.slave_if[0].rresp  = sys_spm_axi_rresp;

        axi_if.slave_if[0].rready = sys_spm_axi_rready;

        sys_spm_apb_paddr = apb_if.paddr;
        sys_spm_apb_pwdata = apb_if.pwdata;
        sys_spm_apb_pwrite = apb_if.pwrite;
        sys_spm_apb_psel = apb_if.psel;
        sys_spm_apb_penable = apb_if.penable;
        sys_spm_apb_pstrb = apb_if.pstrb;
        sys_spm_apb_pprot = apb_if.pprot;
        apb_if.pready = sys_spm_apb_pready;
        apb_if.prdata = sys_spm_apb_prdata;
        apb_if.pslverr = sys_spm_apb_pslverr;


        // Assign the reset pin from the reset interface to the reset pins from the VIP
        // interface.
        rst_n            = axi_reset_if.reset | apb_reset_if.presetn;

        spm_intf.spm_if_clk                = clk;
        spm_intf.spm_if_rst_n              = rst_n;
        spm_intf.spm_if_scp_ecc_disable    = spm_scp_ecc_disable;
        spm_intf.spm_if_scp_error_status   = spm_scp_error_status;
        spm_intf.spm_if_irq                = spm_irq;

    end

// TODO(vito, Bronze, review new P Wrapper IO)
logic ref_clk;
logic ao_rst_n;
logic global_rst_n;
logic noc_rst_n;

logic noc_async_idle_req;
logic noc_async_idle_ack;
logic noc_async_idle_val;
logic noc_clken;

assign ref_clk     = clk;
assign ao_rst_n    = rst_n;
assign global_rst_n= rst_n;

sys_spm_p i_sys_spm_dut
(
  // TODO(vito, Bronze, review this)
  .i_clk         (clk),
  .i_ref_clk     (ref_clk),
  .i_ao_rst_n    (ao_rst_n    ),
  .i_global_rst_n(global_rst_n),
  .o_noc_rst_n   (noc_rst_n   ),

  // TODO(vito, Bronze, review this)
  .o_noc_async_idle_req(noc_async_idle_req),
  .i_noc_async_idle_ack(noc_async_idle_ack),
  .i_noc_async_idle_val(noc_async_idle_val),
  .o_noc_clken(noc_clken),


  // AXI Interface
  // - AW Channel
  .i_lt_axi_s_awaddr(sys_spm_axi_awaddr),
  .i_lt_axi_s_awid(sys_spm_axi_awid),
  .i_lt_axi_s_awlen(sys_spm_axi_awlen),
  .i_lt_axi_s_awsize(sys_spm_axi_awsize),
  .i_lt_axi_s_awburst(sys_spm_axi_awburst),
  .i_lt_axi_s_awcache(sys_spm_axi_awcache),
  .i_lt_axi_s_awprot(sys_spm_axi_awprot),
  .i_lt_axi_s_awlock(sys_spm_axi_awlock),
  .i_lt_axi_s_awqos(sys_spm_axi_awqos),
  .i_lt_axi_s_awregion(sys_spm_axi_awregion),
  .i_lt_axi_s_awuser(sys_spm_axi_awuser),
  .i_lt_axi_s_awvalid(sys_spm_axi_awvalid),
  .o_lt_axi_s_awready(sys_spm_axi_awready),
  // - W Channel
  .i_lt_axi_s_wdata(sys_spm_axi_wdata),
  .i_lt_axi_s_wstrb(sys_spm_axi_wstrb),
  .i_lt_axi_s_wlast(sys_spm_axi_wlast),
  .i_lt_axi_s_wuser(sys_spm_axi_wuser),
  .i_lt_axi_s_wvalid(sys_spm_axi_wvalid),
  .o_lt_axi_s_wready(sys_spm_axi_wready),
  // - B Channel
  .o_lt_axi_s_bvalid(sys_spm_axi_bvalid),
  .o_lt_axi_s_bid(sys_spm_axi_bid),
  .o_lt_axi_s_buser(sys_spm_axi_buser),
  .o_lt_axi_s_bresp(sys_spm_axi_bresp),
  .i_lt_axi_s_bready(sys_spm_axi_bready),
  // - AR Channel
  .i_lt_axi_s_araddr(sys_spm_axi_araddr),
  .i_lt_axi_s_arid(sys_spm_axi_arid),
  .i_lt_axi_s_arlen(sys_spm_axi_arlen),
  .i_lt_axi_s_arsize(sys_spm_axi_arsize),
  .i_lt_axi_s_arburst(sys_spm_axi_arburst),
  .i_lt_axi_s_arcache(sys_spm_axi_arcache),
  .i_lt_axi_s_arprot(sys_spm_axi_arprot),
  .i_lt_axi_s_arqos(sys_spm_axi_arqos),
  .i_lt_axi_s_arregion(sys_spm_axi_arregion),
  .i_lt_axi_s_aruser(sys_spm_axi_aruser),
  .i_lt_axi_s_arlock(sys_spm_axi_arlock),
  .i_lt_axi_s_arvalid(sys_spm_axi_arvalid),
  .o_lt_axi_s_arready(sys_spm_axi_arready),
  // - R Channel
  .o_lt_axi_s_rvalid(sys_spm_axi_rvalid),
  .o_lt_axi_s_rlast(sys_spm_axi_rlast),
  .o_lt_axi_s_rid(sys_spm_axi_rid),
  .o_lt_axi_s_rdata(sys_spm_axi_rdata),
  .o_lt_axi_s_ruser(sys_spm_axi_ruser),
  .o_lt_axi_s_rresp(sys_spm_axi_rresp),
  .i_lt_axi_s_rready(sys_spm_axi_rready),
  // APB Interface
  .i_cfg_apb4_s_paddr(sys_spm_apb_paddr),
  .i_cfg_apb4_s_pwdata(sys_spm_apb_pwdata),
  .i_cfg_apb4_s_pwrite(sys_spm_apb_pwrite),
  .i_cfg_apb4_s_psel(sys_spm_apb_psel),
  .i_cfg_apb4_s_penable(sys_spm_apb_penable),
  .i_cfg_apb4_s_pstrb(sys_spm_apb_pstrb),
  .i_cfg_apb4_s_pprot(sys_spm_apb_pprot),
  .o_cfg_apb4_s_pready(sys_spm_apb_pready),
  .o_cfg_apb4_s_prdata(sys_spm_apb_prdata),
  .o_cfg_apb4_s_pslverr(sys_spm_apb_pslverr),
  // Error IRQ signal
  .o_irq(spm_irq),

  // DFT signals
  .tck(),
  .trst(),
  .tms(),
  .tdi(),
  .tdo_en(),
  .tdo(),

  .test_clk(),
  .test_mode(1'b0),
  .edt_update(),
  .scan_en(1'b0),
  .scan_in(),
  .scan_out(),

  .bisr_clk(),
  .bisr_reset(),
  .bisr_shift_en(),
  .bisr_si(),
  .bisr_so()
);

    // =============================================================================================================
    // Reset and clock generation
    // =============================================================================================================
    // Generate the clock
    initial begin
        u_axe_clk_generator.set_clock(.freq_mhz(spm_freq_mhz), .duty(50));
        clk_en = 1'b1;
    end


    initial begin
        uvm_config_db#(spm_config_t)::set(uvm_root::get(), "*", "spm_config", spm_config);
        uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.spm_ip_env.axi_sequencer", "reset_mp", axi_reset_if.axi_reset_modport);
        uvm_config_db#(virtual apb_reset_if.apb_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.apb_sequencer", "reset_mp", apb_reset_if.apb_reset_modport);

        uvm_config_db#(virtual spm_if)::set(uvm_root::get(), "*", "spm_intf", spm_intf);
        uvm_config_db#(bit)::set(uvm_root::get(), "*", "enable_ecc_mon", 0);
        uvm_config_db#(virtual clk_if)::set(uvm_root::get(), "*", "u_axe_clk_if", u_axe_clk_if);
        uvm_config_db#(virtual svt_axi_if)::set(uvm_root::get(), "uvm_test_top.env.spm_ip_env.m_axi_system_env", "vif", axi_if);
        uvm_config_db#(virtual svt_apb_if)::set(uvm_root::get(), "uvm_test_top.env.sys_spm_apb_env", "vif", apb_if);

        run_test ();
    end





  endmodule
