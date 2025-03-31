
`timescale 1ps/1ps
`define AXI_VIP

realtime CLK_PERIOD = 833;
module hdl_top();

    // Packages import

    import uvm_pkg::*;
    import spm_uvm_pkg::*;
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import spm_test_pkg::*;
    import axe_tcl_sram_pkg::*;

    `include "uvm_macros.svh"

    localparam spm_config_t spm_config = calc_config();

    // CLK params
    parameter int unsigned  spm_freq_mhz = 1200;
    parameter real          spm_clk_period_ns = 0.833; // keep up-to-date woth freq mhz as 1000/spm_freq_mhz
    parameter time          spm_tol_ps   = 10;

    // TIMEOUTS and TICKER

    parameter int unsigned soft_timeout_clk_cycles  = 100_000;
    parameter int unsigned hard_timeout_clk_cycles  = 3_000_000_000; //~2490ms

    parameter int unsigned ticker_clk_cycles        = 300; //~249ns
    // Don't change! Only modify clk cycles params
    parameter int unsigned soft_timeout_ns  = soft_timeout_clk_cycles * int'(1000.0 / real'(spm_freq_mhz));
    parameter int unsigned hard_timeout_ns  = hard_timeout_clk_cycles * int'(1000.0 / real'(spm_freq_mhz));
    parameter int unsigned ticker_ns        = ticker_clk_cycles * int'(1000.0 / real'(spm_freq_mhz));


    // events for backdoor memory manipulation
    uvm_event ecc_write_completed_ev, ecc_read_completed_ev, ecc_read_started_ev, ecc_backdoor_access_executed_ev;

    string testname;
    bit enable_ecc_mon;


    // =========================
    // Datatypes
    typedef logic [spm_config.spm_axi_data_width-1:0]         spm_axi_data_t;
    typedef logic [spm_config.spm_axi_data_width + 8-1:0]     spm_axi_ecc_data_t;
    typedef logic [spm_config.spm_axi_addr_width-1:0]         spm_axi_addr_t;
    typedef logic [spm_config.spm_axi_strb_width-1:0]         spm_axi_strb_t;
    typedef logic [spm_config.spm_axi_id_width-1:0]           spm_axi_id_t;
    typedef logic [spm_config.spm_axi_atop_width-1:0]         spm_axi_atop_t;
    typedef axi_pkg::axi_len_t    spm_axi_len_t;
    typedef axi_pkg::axi_size_t   spm_axi_size_t;
    typedef axi_pkg::axi_burst_t  spm_axi_burst_t;
    typedef axi_pkg::axi_resp_t   spm_axi_resp_t;
    typedef axi_pkg::axi_cache_t  spm_axi_cache_t;
    typedef axi_pkg::axi_prot_t   spm_axi_prot_t;

    logic clk;
    logic rst_n;
    string file;

    spm_axi_ecc_data_t ecc_data;
    spm_axi_ecc_data_t ecc_data_tmp;


    spm_axi_data_t my_data_check;

    // AXI AW channel
    logic               spm_axi_awvalid;
    spm_axi_addr_t      spm_axi_awaddr;
    spm_axi_id_t        spm_axi_awid;
    spm_axi_len_t       spm_axi_awlen;
    spm_axi_size_t      spm_axi_awsize;
    spm_axi_burst_t     spm_axi_awburst;
    logic               spm_axi_awlock;
    spm_axi_cache_t     spm_axi_awcache;
    spm_axi_prot_t      spm_axi_awprot;
    logic               spm_axi_awready;
    spm_axi_atop_t      spm_axi_awatop;

    // AXI W channel
    logic               spm_axi_wvalid;
    logic               spm_axi_wlast;
    spm_axi_data_t      spm_axi_wdata;
    spm_axi_strb_t      spm_axi_wstrb;
    logic               spm_axi_wready;

    // AXI B channel
    logic               spm_axi_bvalid;
    spm_axi_id_t        spm_axi_bid;
    spm_axi_resp_t      spm_axi_bresp;
    logic               spm_axi_bready;

    // AXI AR channel
    logic               spm_axi_arvalid;
    spm_axi_addr_t      spm_axi_araddr;
    spm_axi_id_t        spm_axi_arid;
    spm_axi_len_t       spm_axi_arlen;
    spm_axi_size_t      spm_axi_arsize;
    spm_axi_burst_t     spm_axi_arburst;
    logic               spm_axi_arlock;
    spm_axi_cache_t     spm_axi_arcache;
    spm_axi_prot_t      spm_axi_arprot;
    logic               spm_axi_arready;

    // AXI R channel
    logic               spm_axi_rvalid;
    logic               spm_axi_rlast;
    spm_axi_id_t        spm_axi_rid;
    spm_axi_data_t      spm_axi_rdata;
    spm_axi_resp_t      spm_axi_rresp;
    logic               spm_axi_rready;

    // error related
    logic               spm_scp_ecc_disable;
    spm_pkg::spm_error_status_t spm_scp_error_status;
    logic               spm_irq;
    // MEM default values
    impl_inp_t          i_impl;
    impl_oup_t          o_impl;


    // useful stuff
    bit                 ecc_2b_error = 0;
    bit                 clk_en;


    // initialize values
    initial begin
        clk = 1'b0;

        i_impl.mcs   = '0;
        i_impl.mcsw  = 0;
        i_impl.ret   = 0;
        i_impl.pde   = 0;
        i_impl.se    = 0;
        i_impl.adme  = '0;
    end



    initial begin
        uvm_hdl_force("hdl_top.i_spm_dut.spm_ip_axi_protocol_checker.ARESETn", 0);
        @(negedge rst_n);
        uvm_hdl_release("hdl_top.i_spm_dut.spm_ip_axi_protocol_checker.ARESETn");
    end


    // VIP Interface instance representing the AXI system
    svt_axi_if axi_if ();

    // TB Interface instance to provide access to the reset signal
    axi_reset_if axi_reset_if ();

    spm_if spm_intf();

    // =============================================================================================================
    // CLK RST Instantitation
    // =============================================================================================================
    axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(clk)
                                          );

    axe_clk_assert u_axe_clk_assert(.clk(clk),
                    .rst_n(rst_n),
                    .freq_mhz(spm_freq_mhz),
                    .tol_ps  (spm_tol_ps)
                    );

    axe_timeout u_axe_timeout();
    clk_if u_axe_clk_if(.clk(clk));

    // clk assignments
    assign axi_reset_if.clk     = clk;
    assign axi_if.common_aclk   = clk;
    // rst assignment
    assign rst_n                = axi_reset_if.reset;


    // ---- AXI VIPs ----
    always @*
    begin
        // ---- MST AXI ----
        axi_if.master_if[0].aresetn = rst_n;

        // AXI AW channel
        spm_axi_awvalid             = axi_if.master_if[0].awvalid;
        spm_axi_awaddr              = axi_if.master_if[0].awaddr;
        spm_axi_awid                = axi_if.master_if[0].awid;
        spm_axi_awlen               = axi_if.master_if[0].awlen;
        spm_axi_awsize              = axi_if.master_if[0].awsize;
        spm_axi_awburst             = axi_if.master_if[0].awburst;
        spm_axi_awlock              = axi_if.master_if[0].awlock;
        spm_axi_awcache             = axi_if.master_if[0].awcache;
        spm_axi_awprot              = axi_if.master_if[0].awprot;
        spm_axi_awatop              = axi_if.master_if[0].awatop;
        axi_if.master_if[0].awready = spm_axi_awready;

        // AXI W channel
        spm_axi_wvalid              = axi_if.master_if[0].wvalid;
        spm_axi_wlast               = axi_if.master_if[0].wlast;
        spm_axi_wdata               = axi_if.master_if[0].wdata;
        spm_axi_wstrb               = axi_if.master_if[0].wstrb;
        axi_if.master_if[0].wready  = spm_axi_wready;

        // AXI B channel
        axi_if.master_if[0].bvalid  = spm_axi_bvalid;
        axi_if.master_if[0].bid     = spm_axi_bid;
        axi_if.master_if[0].bresp   = spm_axi_bresp;
        spm_axi_bready              = axi_if.master_if[0].bready;

        // AXI AR channel
        spm_axi_arvalid             = axi_if.master_if[0].arvalid;
        spm_axi_araddr              = axi_if.master_if[0].araddr;
        spm_axi_arid                = axi_if.master_if[0].arid;
        spm_axi_arlen               = axi_if.master_if[0].arlen;
        spm_axi_arsize              = axi_if.master_if[0].arsize;
        spm_axi_arburst             = axi_if.master_if[0].arburst;
        spm_axi_arlock              = axi_if.master_if[0].arlock;
        spm_axi_arcache             = axi_if.master_if[0].arcache;
        spm_axi_arprot              = axi_if.master_if[0].arprot;
        axi_if.master_if[0].arready = spm_axi_arready;

        // AXI R channel
        axi_if.master_if[0].rvalid  = spm_axi_rvalid;
        axi_if.master_if[0].rlast   = spm_axi_rlast;
        axi_if.master_if[0].rid     = spm_axi_rid;
        axi_if.master_if[0].rdata   = spm_axi_rdata;
        axi_if.master_if[0].rresp   = spm_axi_rresp;
        spm_axi_rready              = axi_if.master_if[0].rready;


        // ---- SLV AXI ----
        axi_if.slave_if[0].aresetn = rst_n;

        // AXI AW channel
        axi_if.slave_if[0].awvalid = spm_axi_awvalid;
        axi_if.slave_if[0].awaddr = spm_axi_awaddr;
        axi_if.slave_if[0].awid = spm_axi_awid;
        axi_if.slave_if[0].awlen = spm_axi_awlen;
        axi_if.slave_if[0].awsize = spm_axi_awsize;
        axi_if.slave_if[0].awburst = spm_axi_awburst;
        axi_if.slave_if[0].awlock = spm_axi_awlock;
        axi_if.slave_if[0].awcache = spm_axi_awcache;
        axi_if.slave_if[0].awprot = spm_axi_awprot;
        axi_if.slave_if[0].awready = spm_axi_awready;

        // AXI W channel
        axi_if.slave_if[0].wvalid = spm_axi_wvalid;
        axi_if.slave_if[0].wlast = spm_axi_wlast;
        axi_if.slave_if[0].wdata = spm_axi_wdata;
        axi_if.slave_if[0].wstrb = spm_axi_wstrb;
        axi_if.slave_if[0].wready = spm_axi_wready;

        // AXI B channel
        axi_if.slave_if[0].bvalid = spm_axi_bvalid;
        axi_if.slave_if[0].bid    = spm_axi_bid;
        axi_if.slave_if[0].bresp  = spm_axi_bresp;
        axi_if.slave_if[0].bready = spm_axi_bready;

        // AXI AR channel
        axi_if.slave_if[0].arvalid = spm_axi_arvalid;
        axi_if.slave_if[0].araddr = spm_axi_araddr;
        axi_if.slave_if[0].arid = spm_axi_arid;
        axi_if.slave_if[0].arlen = spm_axi_arlen;
        axi_if.slave_if[0].arsize = spm_axi_arsize;
        axi_if.slave_if[0].arburst = spm_axi_arburst;
        axi_if.slave_if[0].arlock = spm_axi_arlock;
        axi_if.slave_if[0].arcache = spm_axi_arcache;
        axi_if.slave_if[0].arprot = spm_axi_arprot;
        axi_if.slave_if[0].arready = spm_axi_arready;

        // AXI R channel
        axi_if.slave_if[0].rvalid = spm_axi_rvalid;
        axi_if.slave_if[0].rlast  = spm_axi_rlast;
        axi_if.slave_if[0].rid    = spm_axi_rid;
        axi_if.slave_if[0].rdata  = spm_axi_rdata;
        axi_if.slave_if[0].rresp  = spm_axi_rresp;
        axi_if.slave_if[0].rready = spm_axi_rready;

        // ---- TB VIF ----
        // Assign the reset pin from the reset interface to the reset pins from the VIP
        // interface.
        // passive if
        spm_intf.spm_if_clk                = clk;
        spm_intf.spm_if_rst_n              = rst_n;
        spm_intf.spm_if_scp_ecc_disable    = spm_scp_ecc_disable;
        spm_intf.spm_if_scp_error_status   = spm_scp_error_status;
        spm_intf.spm_if_irq                = spm_irq;
    end


    // =========================
    // Design Under Test (DUT)
    spm #(
        .SPM_MEM_SIZE_KB(spm_config.spm_mem_size_kb),
        .ECC_PROTECTION_EN(spm_config.ecc_protection_en),
        .SPM_MEM_MACRO_DEPTH_K(spm_config.spm_mem_macro_depth_k),
        .SPM_NB_BANKS(spm_config.spm_nb_banks),
        .SPM_NB_SUB_BANKS(spm_config.spm_nb_sub_banks),
        .SPM_NB_MINI_BANKS(spm_config.spm_nb_mini_banks),
        .SPM_NB_SRAMS_PER_MINI_BANK(spm_config.spm_nb_srams_per_mini_bank),
        .SPM_NB_REQ_PIPELINE(spm_config.spm_nb_req_pipeline),
        .SPM_NB_RSP_PIPELINE(spm_config.spm_nb_rsp_pipeline),
        //custom
        .spm_axi_data_t(spm_axi_data_t),
        .spm_axi_addr_t(spm_axi_addr_t),
        .spm_axi_strb_t(spm_axi_strb_t),
        .spm_axi_id_t(spm_axi_id_t),

        //common
        .spm_axi_len_t(spm_axi_len_t),
        .spm_axi_size_t(spm_axi_size_t),
        .spm_axi_burst_t(spm_axi_burst_t),
        .spm_axi_resp_t(spm_axi_resp_t),
        .spm_axi_cache_t(spm_axi_cache_t),
        .spm_axi_prot_t(spm_axi_prot_t)
    ) i_spm_dut (
        // Clock, positive edge triggered
        .i_clk (clk),
        // Asynchronous reset, active low
        .i_rst_n(rst_n),
        // AXI AW channel
        .i_axi_s_awvalid(spm_axi_awvalid),
        .i_axi_s_awaddr(spm_axi_awaddr),
        .i_axi_s_awid(spm_axi_awid),
        .i_axi_s_awlen(spm_axi_awlen),
        .i_axi_s_awsize(spm_axi_awsize),
        .i_axi_s_awburst(spm_axi_awburst),
        .i_axi_s_awlock(spm_axi_awlock),
        .i_axi_s_awcache(spm_axi_awcache),
        .i_axi_s_awprot(spm_axi_awprot),
        .o_axi_s_awready(spm_axi_awready),
        .i_axi_s_awatop(spm_axi_awatop),
        // AXI W channel
        .i_axi_s_wvalid(spm_axi_wvalid),
        .i_axi_s_wlast(spm_axi_wlast),
        .i_axi_s_wdata(spm_axi_wdata),
        .i_axi_s_wstrb(spm_axi_wstrb),
        .o_axi_s_wready(spm_axi_wready),
        // AXI B channel
        .o_axi_s_bvalid(spm_axi_bvalid),
        .o_axi_s_bid(spm_axi_bid),
        .o_axi_s_bresp(spm_axi_bresp),
        .i_axi_s_bready(spm_axi_bready),
        // AXI AR channel
        .i_axi_s_arvalid(spm_axi_arvalid),
        .i_axi_s_araddr(spm_axi_araddr),
        .i_axi_s_arid(spm_axi_arid),
        .i_axi_s_arlen(spm_axi_arlen),
        .i_axi_s_arsize(spm_axi_arsize),
        .i_axi_s_arburst(spm_axi_arburst),
        .i_axi_s_arlock(spm_axi_arlock),
        .i_axi_s_arcache(spm_axi_arcache),
        .i_axi_s_arprot(spm_axi_arprot),
        .o_axi_s_arready(spm_axi_arready),
        // AXI R channel
        .o_axi_s_rvalid(spm_axi_rvalid),
        .o_axi_s_rlast(spm_axi_rlast),
        .o_axi_s_rid(spm_axi_rid),
        .o_axi_s_rdata(spm_axi_rdata),
        .o_axi_s_rresp(spm_axi_rresp),
        .i_axi_s_rready(spm_axi_rready),
        // Disable ECC error reporting and in flight correction.
        .i_scp_ecc_disable(spm_scp_ecc_disable),
        // scp_error_status
        .o_scp_error_status(spm_scp_error_status),
        // Error IRQ signal
        .o_irq(spm_irq),
        // RAM Configuration pins
        .i_impl(i_impl),
        .o_impl(o_impl)
    );



    // Generate the clock
    initial begin
        u_axe_clk_generator.set_clock(.freq_mhz(spm_freq_mhz), .duty(50));
        clk_en = 1'b1;
        $display($sformatf("HDL TOP --- SPM CONFIG: #banks: %0d, #subbanks: %0d, #minibanks: %0d, #srams: %0d", spm_config.spm_nb_banks, spm_config.spm_nb_sub_banks, spm_config.spm_nb_mini_banks, spm_config.spm_nb_srams_per_mini_bank));
    end

    // Configure ticker/timeout
    initial begin
        u_axe_timeout.timeout(soft_timeout_ns, hard_timeout_ns);
        u_axe_timeout.ticker(ticker_ns);
    end

    initial begin
        @(posedge clk);
        wait (rst_n === 0);
        @(posedge clk);
        wait (rst_n === 1);
        preload_spm_single_value('0);
    end




    initial begin
        spm_scp_ecc_disable = $urandom_range(1, 0);
        $display($sformatf("HDL TOP --- ECC CONFIG: disable ecc: %0d", spm_scp_ecc_disable));

        // retireve testname
        $value$plusargs("UVM_TESTNAME=%s", testname);

        enable_ecc_mon = 0;
        // if an ecc testcase, then enable monitor
        if(testname == "spm_ecc_full_test") begin
            enable_ecc_mon = ~spm_scp_ecc_disable;
            if($test$plusargs("ECC_2B")) begin
                ecc_2b_error = 1;
                uvm_config_db#(bit)::set(uvm_root::get(), "*", "expect_ecc_error", 1);
                $display($sformatf("HDL TOP --- ECC CONFIG: 2bit error case"));
                $display($sformatf("HDL TOP --- ECC CONFIG: expect ecc error: 1"));
            end else begin
                ecc_2b_error = 0;
                uvm_config_db#(bit)::set(uvm_root::get(), "*", "expect_ecc_error", spm_scp_ecc_disable);
                $display($sformatf("HDL TOP --- ECC CONFIG: 1bit error case"));
                $display($sformatf("HDL TOP --- ECC CONFIG: expect ecc error: %0d", spm_scp_ecc_disable));
            end
        end


        uvm_config_db#(bit)::set(uvm_root::get(), "*", "enable_ecc_mon", enable_ecc_mon);
        uvm_config_db#(spm_config_t)::set(uvm_root::get(), "*", "spm_config", spm_config);

        uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.axi_sequencer", "reset_mp", axi_reset_if.axi_reset_modport);

        uvm_config_db#(virtual clk_if)::set(uvm_root::get(), "*", "u_axe_clk_if", u_axe_clk_if);
        uvm_config_db#(virtual spm_if)::set(uvm_root::get(), "*", "spm_intf", spm_intf);
        uvm_config_db#(virtual svt_axi_if)::set(uvm_root::get(), "uvm_test_top.env.m_axi_system_env", "vif", axi_if);

        run_test ();
    end

    //binds
    `include "generated/spm_config_generated.svh"
    `include "axi4pc/bind_spm_axi.svh"
    `include "axi_perf_tracker/bind_axi_tracker_spm.svh"


    bind spm spm_assertions
        SPM_SVAs (
                    .clk(i_clk),
                    .rst_n(i_rst_n),
                    .spm_scp_error_status(o_scp_error_status),
                    .spm_irq(o_irq),
                    .spm_scp_ecc_disable(i_scp_ecc_disable)
                );
endmodule
