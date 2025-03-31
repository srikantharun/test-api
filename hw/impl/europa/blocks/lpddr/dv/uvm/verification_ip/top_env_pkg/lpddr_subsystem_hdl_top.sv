//
// File: hdl_top.sv
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
//Time resolution of '1ps' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)
//Time resolution of '1ns' will be used (See Makefiles and scripts)

`timescale 1ps/1fs

`include "default_clk_gen.sv"
`include "default_reset_gen.sv"
`include "alpddr5.sv"
`include "perf_signal_assigns.sv"

module hdl_top;
    parameter TOT_LOGIC_RANK= 2; 
    parameter  UNIQUE_ID = "";
    parameter  APB_MASTER_0_ACTIVE = 1;
    parameter  APB_MASTER_1_ACTIVE = 1;
    parameter  AXI4_MASTER_0_ACTIVE = 1;
    parameter  EXT_CLK_RESET = 0;
    import uvm_pkg::*;
    import amem_pkg::*;
    import avery_pkg::*;
    import lpddr_subsystem_params_pkg::*;
    wire                                                          default_clk_gen_CLK;
    wire                                                          default_reset_gen_RESET;
    wire [apb_master_0_params::APB3_PADDR_BIT_WIDTH-1:0]       apb_master_0_PADDR;
    wire [apb_master_0_params::APB3_SLAVE_COUNT-1:0]           apb_master_0_PSEL;
    wire                                                          apb_master_0_PENABLE;
    wire                                                          apb_master_0_PWRITE;
    wire [apb_master_0_params::APB3_PWDATA_BIT_WIDTH-1:0]      apb_master_0_PWDATA;
    wire [apb_master_0_params::APB3_PRDATA_BIT_WIDTH-1:0]      apb_master_0_PRDATA;
    wire                                                          apb_master_0_PREADY;
    wire                                                     apb_master_0_PSLVERR;
    wire [3:0]                                                    apb_master_0_PSTRB;
    wire [3:0]                                                    apb_master_1_PSTRB;
    wire [(apb_master_0_params::APB3_PADDR_BIT_WIDTH-16)-1:0]       apb_master_1_PADDR;
    wire [apb_master_0_params::APB3_SLAVE_COUNT-1:0]           apb_master_1_PSEL;
    wire                                                          apb_master_1_PENABLE;
    wire                                                          apb_master_1_PWRITE;
    wire [apb_master_0_params::APB3_PWDATA_BIT_WIDTH-1:0]      apb_master_1_PWDATA;
    wire [apb_master_0_params::APB3_PRDATA_BIT_WIDTH-1:0]      apb_master_1_PRDATA;
    wire [2:0]                                                          apb_master_0_PPROT;
    wire [2:0]                                                          apb_master_1_PPROT;
    wire                                                          apb_master_1_PREADY;
    wire                                                          apb_master_1_PSLVERR;
    wire                                                          axi4_master_0_AWVALID;
    wire [axi4_master_0_params::AXI4_ADDRESS_WIDTH-1:0]           axi4_master_0_AWADDR;
    wire [2:0]                                                    axi4_master_0_AWPROT;
    wire [3:0]                                                    axi4_master_0_AWREGION;
    wire [7:0]                                                    axi4_master_0_AWLEN;
    wire [((axi4_master_0_params::AXI4_WDATA_WIDTH==2048)?3:2):0] axi4_master_0_AWSIZE;
    wire [1:0]                                                    axi4_master_0_AWBURST;
    wire                                                          axi4_master_0_AWLOCK;
    wire [3:0]                                                    axi4_master_0_AWCACHE;
    wire [3:0]                                                    axi4_master_0_AWQOS;
    wire [axi4_master_0_params::AXI4_ID_WIDTH-1:0]                axi4_master_0_AWID;
    wire [axi4_master_0_params::AXI4_USER_WIDTH-1:0]              axi4_master_0_AWUSER;
    wire                                                          axi4_master_0_AWREADY;
    wire                                                          axi4_master_0_ARVALID;
    wire [axi4_master_0_params::AXI4_ADDRESS_WIDTH-1:0]           axi4_master_0_ARADDR;
    wire [2:0]                                                    axi4_master_0_ARPROT;
    wire [3:0]                                                    axi4_master_0_ARREGION;
    wire [7:0]                                                    axi4_master_0_ARLEN;
    wire [((axi4_master_0_params::AXI4_RDATA_WIDTH==2048)?3:2):0] axi4_master_0_ARSIZE;
    wire [1:0]                                                    axi4_master_0_ARBURST;
    wire                                                          axi4_master_0_ARLOCK;
    wire [3:0]                                                    axi4_master_0_ARCACHE;
    wire [3:0]                                                    axi4_master_0_ARQOS;
    wire [axi4_master_0_params::AXI4_ID_WIDTH-1:0]                axi4_master_0_ARID;
    wire [axi4_master_0_params::AXI4_USER_WIDTH-1:0]              axi4_master_0_ARUSER;
    wire                                                          axi4_master_0_ARREADY;
    wire                                                          axi4_master_0_RVALID;
    wire [axi4_master_0_params::AXI4_RDATA_WIDTH-1:0]             axi4_master_0_RDATA;
    wire [1:0]                                                    axi4_master_0_RRESP;
    wire                                                          axi4_master_0_RLAST;
    wire [axi4_master_0_params::AXI4_ID_WIDTH-1:0]                axi4_master_0_RID;
    wire [axi4_master_0_params::AXI4_USER_WIDTH-1:0]              axi4_master_0_RUSER;
    wire                                                          axi4_master_0_RREADY;
    wire                                                          axi4_master_0_WVALID;
    wire [axi4_master_0_params::AXI4_WDATA_WIDTH-1:0]             axi4_master_0_WDATA;
    wire [(axi4_master_0_params::AXI4_WDATA_WIDTH/8)-1:0]         axi4_master_0_WSTRB;
    wire                                                          axi4_master_0_WLAST;
    wire [axi4_master_0_params::AXI4_USER_WIDTH-1:0]              axi4_master_0_WUSER;
    wire                                                          axi4_master_0_WREADY;
    wire                                                          axi4_master_0_BVALID;
    wire [1:0]                                                    axi4_master_0_BRESP;
    wire [axi4_master_0_params::AXI4_ID_WIDTH-1:0]                axi4_master_0_BID;
    wire [axi4_master_0_params::AXI4_USER_WIDTH-1:0]              axi4_master_0_BUSER;
    wire                                                          axi4_master_0_BREADY;
   
    wire RESET_N; 
    wire ZQ;
    wire CK0_T; 
    wire CK0_C; 
    wire CK1_T; 
    wire CK1_C; 
    wire DMI;// todo -RE-CHECK SEPERATE FOR DIFF CHANNEL 

     // sUB-CHANNEL a
     // INPUT
    wire[1:0] CS_A;
    wire[6:0] CA_A;
    wire WCK_T_A; 
    wire WCK_C_A; 
    
    wire[15:0] DQ_A;
    wire RDQS_T_A; 
    wire RDQS_C_A;

     // cHANNEL b
     // INPUT
    wire[1:0] CS_B;
    wire[6:0] CA_B;
    wire WCK_T_B; 
    wire WCK_C_B; 
    // INOUT
    wire[15:0] DQ_B;
    wire RDQS_T_B; 
    wire RDQS_C_B;
    wire PllDigTst,MTEST2,ATO,ATO_PLL,ZN;

    // -------------------------------------------------
    // Local variable declaration
    // -------------------------------------------------
    string mmod_name1= "channelA",mmod_name2= "channelB";
    addr_monitor    ddr_mont_obj_chB;   // DDR Monitor BFM
    addr_monitor    ddr_mont_obj_chA;   // DDR Monitor BFM
    logic bp_ato_pll,bp_zn;
    subsystem_signal_intf top_signals_intf();
    logic [apb_master_0_params::APB3_PADDR_BIT_WIDTH-1:0]       apb_master_0_PADDR_int;
    logic [31:0]       apb_master_0_prdata;
    amem_type_e             type2;
    amem_speed_bin_e        bin2;
    int ratio2;
    int mem_type2;
    amem_device_density_e   density2;
    amem_io_width_e         io_width2;
    time dfi_clk_period2;

    initial begin
      uvm_config_db#(virtual subsystem_signal_intf)::set(null,"UVMF_VIRTUAL_INTERFACES","top_signals_intf",top_signals_intf);

      // TODO issue LS#4
      force LPDDR_P_SUBSYSTEM.u_pctl.g_clkdiv[1].u_clkdiv.enable_clock=1;
    end

		`perf_signal_assignment(top_signals_intf,LPDDR_P_SUBSYSTEM)
		
    // Credit Counters signals
    assign top_signals_intf.hpr_credit_cnt = LPDDR_P_SUBSYSTEM.hpr_credit_cnt;
    assign top_signals_intf.lpr_credit_cnt = LPDDR_P_SUBSYSTEM.lpr_credit_cnt;
    assign top_signals_intf.wr_credit_cnt = LPDDR_P_SUBSYSTEM.wr_credit_cnt;
    assign top_signals_intf.wrecc_credit_cnt = LPDDR_P_SUBSYSTEM.wrecc_credit_cnt;

    // As per the discussion with respect to issue LS#2 below signals has to
    // be forced from testbench
    assign LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDD2H = 1;
    assign LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDD = 1;
    assign LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VAA = 1;
    assign LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VSS = 0;
    assign LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_ZCAL = 1;

    addr_intf       ddr_if();
    DDR_TIMING      ddr_timing;
    alpddr5_timing  lpddr5_fast_sim_timing;
    adfi_timing dfi_timing;
    amem_log        log;

    // TODO Re-check wrapper for dual channel
    alpddr5 chipA(
	.reset_n(RESET_N), 
        .zq(ZQ),
        .dmi(DMI), // TODO re-check don't find relevant signal 

        // Sub-channel A
        // input
        .cs_A(CS_A),// TODO make DDR_CHIP_SELECT_WIDTH = 2
        .ca_A(CA_A),
        .wck_t_A(WCK_T_A), 
        .wck_c_A(WCK_C_A), 
        .ck0_t(CK0_T),
       	.ck0_c(CK0_C), 
        // inout
        .dq_A(DQ_A),
        .rdqs_t_A(RDQS_T_A), 
        .rdqs_c_A(RDQS_C_A),

        // Channel B
        // input
        .cs_B(CS_B),
        .ca_B(CA_B),
        .wck_t_B(WCK_T_B), 
        .wck_c_B(WCK_C_B), 
        .ck1_t(CK1_T), 
	.ck1_c(CK1_C), 
        // inout
        .dq_B(DQ_B),
        .rdqs_t_B(RDQS_B), 
        .rdqs_c_B(RDQS_B_)
    );
    default_clk_gen default_clk_gen_1
            (
                .CLK(top_signals_intf.i_lpddr_clk)
            );
    default_reset_gen default_reset_gen_global
            (
                .RESET(top_signals_intf.i_global_rst_n),
                .CLK_IN(top_signals_intf.i_lpddr_clk)
            );
    default_reset_gen default_reset_gen_ao
            (
                .RESET(top_signals_intf.i_ao_rst_n),
                .CLK_IN(top_signals_intf.i_lpddr_clk)
            );

    
    generate
        if ( EXT_CLK_RESET == 0 )
        begin: generate_internal_clk_rst
            default_clk_gen default_clk_gen
            (
                .CLK(default_clk_gen_CLK)
            );
            default_reset_gen default_reset_gen
            (
                .RESET(default_reset_gen_RESET),
                .CLK_IN(default_clk_gen_CLK)
            );
        end
    endgenerate
    generate
        
        if ( APB_MASTER_0_ACTIVE )
        begin: generate_active_apb_master_0
            apb_master 
            #(
                .SLAVE_COUNT(apb_master_0_params::APB3_SLAVE_COUNT),
                .ADDR_WIDTH(apb_master_0_params::APB3_PADDR_BIT_WIDTH),
                .WDATA_WIDTH(apb_master_0_params::APB3_PWDATA_BIT_WIDTH),
                .RDATA_WIDTH(apb_master_0_params::APB3_PRDATA_BIT_WIDTH),
                .IF_NAME({UNIQUE_ID,"apb_master_0"}),
                .PATH_NAME("UVMF_VIRTUAL_INTERFACES")
            )
            apb_master_0
            (
                .PCLK(default_clk_gen_CLK),
                .PRESETn(default_reset_gen_RESET),
                .PADDR(apb_master_0_PADDR),
                .PSEL(apb_master_0_PSEL),
                .PENABLE(apb_master_0_PENABLE),
                .PWRITE(apb_master_0_PWRITE),
                .PWDATA(apb_master_0_PWDATA),
                .PRDATA(apb_master_0_PRDATA),
                .PREADY(apb_master_0_PREADY),
                .PSLVERR(apb_master_0_PSLVERR),
                .PPROT(apb_master_0_PPROT),
                .PSTRB(apb_master_0_PSTRB)
            );
        end
        else
        begin: generate_passive_apb_master_0_monitor
            apb_monitor 
            #(
                .SLAVE_COUNT(apb_master_0_params::APB3_SLAVE_COUNT),
                .ADDR_WIDTH(apb_master_0_params::APB3_PADDR_BIT_WIDTH),
                .WDATA_WIDTH(apb_master_0_params::APB3_PWDATA_BIT_WIDTH),
                .RDATA_WIDTH(apb_master_0_params::APB3_PRDATA_BIT_WIDTH),
                .IF_NAME({UNIQUE_ID,"apb_master_0"}),
                .PATH_NAME("UVMF_VIRTUAL_INTERFACES")
            )
            apb_master_0
            (
                .PCLK(default_clk_gen_CLK),
                .PRESETn(default_reset_gen_RESET),
                .PADDR(apb_master_0_PADDR),
                .PSEL(apb_master_0_PSEL),
                .PENABLE(apb_master_0_PENABLE),
                .PWRITE(apb_master_0_PWRITE),
                .PWDATA(apb_master_0_PWDATA),
                .PRDATA(apb_master_0_PRDATA),
                .PREADY(apb_master_0_PREADY),
                .PSLVERR(apb_master_0_PSLVERR),
                .PPROT(apb_master_0_PPROT),
                .PSTRB(apb_master_0_PSTRB)
            );
        end
    endgenerate
    generate
        if ( AXI4_MASTER_0_ACTIVE )
        begin: generate_active_axi4_master_0
            axi4_master 
            #(
                .ADDR_WIDTH(axi4_master_0_params::AXI4_ADDRESS_WIDTH),
                .RDATA_WIDTH(axi4_master_0_params::AXI4_RDATA_WIDTH),
                .WDATA_WIDTH(axi4_master_0_params::AXI4_WDATA_WIDTH),
                .ID_WIDTH(axi4_master_0_params::AXI4_ID_WIDTH),
                .USER_WIDTH(axi4_master_0_params::AXI4_USER_WIDTH),
                .REGION_MAP_SIZE(axi4_master_0_params::AXI4_REGION_MAP_SIZE),
                .IF_NAME({UNIQUE_ID,"axi4_master_0"}),
                .PATH_NAME("UVMF_VIRTUAL_INTERFACES")
            )
            axi4_master_0
            (
                .ACLK(default_clk_gen_CLK),
                .ARESETn(default_reset_gen_RESET),
                .AWVALID(axi4_master_0_AWVALID),
                .AWADDR(axi4_master_0_AWADDR),
                .AWPROT(axi4_master_0_AWPROT),
                .AWREGION(axi4_master_0_AWREGION),
                .AWLEN(axi4_master_0_AWLEN),
                .AWSIZE(axi4_master_0_AWSIZE),
                .AWBURST(axi4_master_0_AWBURST),
                .AWLOCK(axi4_master_0_AWLOCK),
                .AWCACHE(axi4_master_0_AWCACHE),
                .AWQOS(axi4_master_0_AWQOS),
                .AWID(axi4_master_0_AWID),
                .AWUSER(axi4_master_0_AWUSER),
                .AWREADY(axi4_master_0_AWREADY),
                .ARVALID(axi4_master_0_ARVALID),
                .ARADDR(axi4_master_0_ARADDR),
                .ARPROT(axi4_master_0_ARPROT),
                .ARREGION(axi4_master_0_ARREGION),
                .ARLEN(axi4_master_0_ARLEN),
                .ARSIZE(axi4_master_0_ARSIZE),
                .ARBURST(axi4_master_0_ARBURST),
                .ARLOCK(axi4_master_0_ARLOCK),
                .ARCACHE(axi4_master_0_ARCACHE),
                .ARQOS(axi4_master_0_ARQOS),
                .ARID(axi4_master_0_ARID),
                .ARUSER(axi4_master_0_ARUSER),
                .ARREADY(axi4_master_0_ARREADY),
                .RVALID(axi4_master_0_RVALID),
                .RDATA(axi4_master_0_RDATA),
                .RRESP(axi4_master_0_RRESP),
                .RLAST(axi4_master_0_RLAST),
                .RID(axi4_master_0_RID),
                .RUSER(axi4_master_0_RUSER),
                .RREADY(axi4_master_0_RREADY),
                .WVALID(axi4_master_0_WVALID),
                .WDATA(axi4_master_0_WDATA),
                .WSTRB(axi4_master_0_WSTRB),
                .WLAST(axi4_master_0_WLAST),
                .WUSER(axi4_master_0_WUSER),
                .WREADY(axi4_master_0_WREADY),
                .BVALID(axi4_master_0_BVALID),
                .BRESP(axi4_master_0_BRESP),
                .BID(axi4_master_0_BID),
                .BUSER(axi4_master_0_BUSER),
                .BREADY(axi4_master_0_BREADY)
            );
        end
        else
        begin: generate_passive_axi4_master_0_monitor
            axi4_monitor 
            #(
                .ADDR_WIDTH(axi4_master_0_params::AXI4_ADDRESS_WIDTH),
                .RDATA_WIDTH(axi4_master_0_params::AXI4_RDATA_WIDTH),
                .WDATA_WIDTH(axi4_master_0_params::AXI4_WDATA_WIDTH),
                .ID_WIDTH(axi4_master_0_params::AXI4_ID_WIDTH),
                .USER_WIDTH(axi4_master_0_params::AXI4_USER_WIDTH),
                .REGION_MAP_SIZE(axi4_master_0_params::AXI4_REGION_MAP_SIZE),
                .IF_NAME({UNIQUE_ID,"axi4_master_0"}),
                .PATH_NAME("UVMF_VIRTUAL_INTERFACES")
            )
            axi4_master_0
            (
                .ACLK(default_clk_gen_CLK),
                .ARESETn(default_reset_gen_RESET),
                .AWVALID(axi4_master_0_AWVALID),
                .AWADDR(axi4_master_0_AWADDR),
                .AWPROT(axi4_master_0_AWPROT),
                .AWREGION(axi4_master_0_AWREGION),
                .AWLEN(axi4_master_0_AWLEN),
                .AWSIZE(axi4_master_0_AWSIZE),
                .AWBURST(axi4_master_0_AWBURST),
                .AWLOCK(axi4_master_0_AWLOCK),
                .AWCACHE(axi4_master_0_AWCACHE),
                .AWQOS(axi4_master_0_AWQOS),
                .AWID(axi4_master_0_AWID),
                .AWUSER(axi4_master_0_AWUSER),
                .AWREADY(axi4_master_0_AWREADY),
                .ARVALID(axi4_master_0_ARVALID),
                .ARADDR(axi4_master_0_ARADDR),
                .ARPROT(axi4_master_0_ARPROT),
                .ARREGION(axi4_master_0_ARREGION),
                .ARLEN(axi4_master_0_ARLEN),
                .ARSIZE(axi4_master_0_ARSIZE),
                .ARBURST(axi4_master_0_ARBURST),
                .ARLOCK(axi4_master_0_ARLOCK),
                .ARCACHE(axi4_master_0_ARCACHE),
                .ARQOS(axi4_master_0_ARQOS),
                .ARID(axi4_master_0_ARID),
                .ARUSER(axi4_master_0_ARUSER),
                .ARREADY(axi4_master_0_ARREADY),
                .RVALID(axi4_master_0_RVALID),
                .RDATA(axi4_master_0_RDATA),
                .RRESP(axi4_master_0_RRESP),
                .RLAST(axi4_master_0_RLAST),
                .RID(axi4_master_0_RID),
                .RUSER(axi4_master_0_RUSER),
                .RREADY(axi4_master_0_RREADY),
                .WVALID(axi4_master_0_WVALID),
                .WDATA(axi4_master_0_WDATA),
                .WSTRB(axi4_master_0_WSTRB),
                .WLAST(axi4_master_0_WLAST),
                .WUSER(axi4_master_0_WUSER),
                .WREADY(axi4_master_0_WREADY),
                .BVALID(axi4_master_0_BVALID),
                .BRESP(axi4_master_0_BRESP),
                .BID(axi4_master_0_BID),
                .BUSER(axi4_master_0_BUSER),
                .BREADY(axi4_master_0_BREADY)
            );
        end
    endgenerate
    generate
    if ( APB_MASTER_1_ACTIVE )
	begin: generate_active_apb_master_1
            apb_master 
            #(
                .SLAVE_COUNT(apb_master_0_params::APB3_SLAVE_COUNT),
                .ADDR_WIDTH(apb_master_0_params::APB3_PADDR_BIT_WIDTH-16),
                .WDATA_WIDTH(apb_master_0_params::APB3_PWDATA_BIT_WIDTH),
                .RDATA_WIDTH(apb_master_0_params::APB3_PRDATA_BIT_WIDTH),
                .IF_NAME({UNIQUE_ID,"apb_master_1"}),
                .PATH_NAME("UVMF_VIRTUAL_INTERFACES")
            )
            apb_master_1
            (
                .PCLK(default_clk_gen_CLK),
                .PRESETn(default_reset_gen_RESET),
                .PADDR(apb_master_1_PADDR),
                .PSEL(apb_master_1_PSEL),
                .PENABLE(apb_master_1_PENABLE),
                .PWRITE(apb_master_1_PWRITE),
                .PWDATA(apb_master_1_PWDATA),
                .PRDATA(apb_master_1_PRDATA),
                .PREADY(apb_master_1_PREADY),
                .PSLVERR(apb_master_1_PSLVERR),
                .PPROT(apb_master_1_PPROT),
                .PSTRB(apb_master_1_PSTRB)
            );
        end
    endgenerate

    // LPDDR Subsystem Design instantiation
    lpddr_p LPDDR_P_SUBSYSTEM (
	    
  // Clocks
  .i_ao_clk   (top_signals_intf.i_lpddr_clk), 
  .i_lpddr_clk(top_signals_intf.i_lpddr_clk), 

  //-------------------------------
  // Partition Controller Interface
  //-------------------------------
  .i_ao_rst_n          (top_signals_intf.i_ao_rst_n),
  .i_global_rst_n      (top_signals_intf.i_global_rst_n),
  .o_ao_rst_sync_n     (), // TODO Need to check document for behavior
  .o_noc_async_idle_req(), // TODO Need to check document for behavior
  .i_noc_async_idle_ack(2'b00), // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  .i_noc_async_idle_val(2'b00), // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  .o_noc_clken         (), // TODO Need to check document for behavior
  .o_noc_rst_n         (), // TODO Need to check document for behavior

  //-------------------------------
  // AXI4 lpddr_axi
  //-------------------------------
  .i_lpddr_axi_m_araddr  ({7'b0,axi4_master_0_ARADDR}),
  .i_lpddr_axi_m_arburst (axi4_master_0_ARBURST),
  .i_lpddr_axi_m_arcache (axi4_master_0_ARCACHE),
  .i_lpddr_axi_m_arid    (axi4_master_0_ARID),
  .i_lpddr_axi_m_arlen   (axi4_master_0_ARLEN),
  .i_lpddr_axi_m_arlock  (axi4_master_0_ARLOCK),
  .i_lpddr_axi_m_arprot  (axi4_master_0_ARPROT),
  .i_lpddr_axi_m_arqos   (axi4_master_0_ARQOS),
  .i_lpddr_axi_m_arregion(axi4_master_0_ARREGION),
  .i_lpddr_axi_m_aruser  (axi4_master_0_ARUSER),
  .i_lpddr_axi_m_arsize  (axi4_master_0_ARSIZE),
  .i_lpddr_axi_m_arvalid (axi4_master_0_ARVALID),
  .i_lpddr_axi_m_rready  (axi4_master_0_RREADY),
  .i_lpddr_axi_m_awaddr  ({7'b0,axi4_master_0_AWADDR}),
  .i_lpddr_axi_m_awburst (axi4_master_0_AWBURST),
  .i_lpddr_axi_m_awcache (axi4_master_0_AWCACHE),
  .i_lpddr_axi_m_awid    (axi4_master_0_AWID),
  .i_lpddr_axi_m_awlen   (axi4_master_0_AWLEN),
  .i_lpddr_axi_m_awlock  (axi4_master_0_AWLOCK),
  .i_lpddr_axi_m_awprot  (axi4_master_0_AWPROT),
  .i_lpddr_axi_m_awqos   (axi4_master_0_AWQOS),
  .i_lpddr_axi_m_awregion(axi4_master_0_AWREGION),
  .i_lpddr_axi_m_awuser  (axi4_master_0_AWUSER),
  .i_lpddr_axi_m_awsize  (axi4_master_0_AWSIZE),
  .i_lpddr_axi_m_awvalid (axi4_master_0_AWVALID),
  .i_lpddr_axi_m_wdata   (axi4_master_0_WDATA),
  .i_lpddr_axi_m_wlast   (axi4_master_0_WLAST),
  .i_lpddr_axi_m_wstrb   (axi4_master_0_WSTRB),
  .i_lpddr_axi_m_wvalid  (axi4_master_0_WVALID),
  .i_lpddr_axi_m_wuser   (axi4_master_0_WUSER),
  .i_lpddr_axi_m_bready  (axi4_master_0_BREADY),
  .o_lpddr_axi_m_arready (axi4_master_0_ARREADY),
  .o_lpddr_axi_m_rdata   (axi4_master_0_RDATA),
  .o_lpddr_axi_m_rid     (axi4_master_0_RID),
  .o_lpddr_axi_m_rlast   (axi4_master_0_RLAST),
  .o_lpddr_axi_m_ruser   (axi4_master_0_RUSER),
  .o_lpddr_axi_m_rresp   (axi4_master_0_RRESP),
  .o_lpddr_axi_m_rvalid  (axi4_master_0_RVALID),
  .o_lpddr_axi_m_awready (axi4_master_0_AWREADY),
  .o_lpddr_axi_m_wready  (axi4_master_0_WREADY),
  .o_lpddr_axi_m_bid     (axi4_master_0_BID),
  .o_lpddr_axi_m_bresp   (axi4_master_0_BRESP),
  .o_lpddr_axi_m_bvalid  (axi4_master_0_BVALID),
  .o_lpddr_axi_m_buser   (axi4_master_0_BUSER),

  //-------------------------------
  // APB4 lpddr_cfg_apb (sync to i_lpddr_clk)
  //-------------------------------
  .i_lpddr_cfg_apb4_s_paddr  (apb_master_0_PADDR_int),
  .i_lpddr_cfg_apb4_s_penable(apb_master_0_PENABLE),
  .i_lpddr_cfg_apb4_s_pprot  (apb_master_0_PPROT),
  .i_lpddr_cfg_apb4_s_psel   (apb_master_0_PSEL),
  .i_lpddr_cfg_apb4_s_pstrb  (apb_master_0_PSTRB),
  .i_lpddr_cfg_apb4_s_pwdata (apb_master_0_PWDATA),
  .i_lpddr_cfg_apb4_s_pwrite (apb_master_0_PWRITE),
  .o_lpddr_cfg_apb4_s_prdata (apb_master_0_PRDATA),
  .o_lpddr_cfg_apb4_s_pready (apb_master_0_PREADY),
  .o_lpddr_cfg_apb4_s_pslverr(apb_master_0_PSLVERR),

  //-------------------------------
  // APB4 lpddr_syscfg_apb (sync to i_ao_clk)
  //-------------------------------
  //chip_syscfg_addr_t           i_lpddr_syscfg_apb4_s_paddr  ,
  .i_lpddr_syscfg_apb4_s_paddr  (apb_master_1_PADDR),
  .i_lpddr_syscfg_apb4_s_pwdata (apb_master_1_PWDATA),
  .i_lpddr_syscfg_apb4_s_pwrite (apb_master_1_PWRITE),
  .i_lpddr_syscfg_apb4_s_psel   (apb_master_1_PSEL),
  .i_lpddr_syscfg_apb4_s_penable(apb_master_1_PENABLE),
  .i_lpddr_syscfg_apb4_s_pstrb  (apb_master_1_PSTRB),
  .i_lpddr_syscfg_apb4_s_pprot  (apb_master_1_PPROT), 
  .o_lpddr_syscfg_apb4_s_pready (apb_master_1_PREADY),
  .o_lpddr_syscfg_apb4_s_prdata (apb_master_1_PRDATA),
  .o_lpddr_syscfg_apb4_s_pslverr(apb_master_1_PSLVERR),

  // CTRL Interrupts
  .o_ctrl_sbr_done_intr             (top_signals_intf.o_ctrl_sbr_done_intr             ),
  .o_ctrl_derate_temp_limit_intr    (top_signals_intf.o_ctrl_derate_temp_limit_intr    ),
  .o_ctrl_ecc_ap_err_intr           (top_signals_intf.o_ctrl_ecc_ap_err_intr           ),
  .o_ctrl_ecc_corrected_err_intr    (top_signals_intf.o_ctrl_ecc_corrected_err_intr    ),
  .o_ctrl_ecc_uncorrected_err_intr  (top_signals_intf.o_ctrl_ecc_uncorrected_err_intr  ),
  .o_ctrl_rd_linkecc_corr_err_intr  (top_signals_intf.o_ctrl_rd_linkecc_corr_err_intr  ),
  .o_ctrl_rd_linkecc_uncorr_err_intr(top_signals_intf.o_ctrl_rd_linkecc_uncorr_err_intr),

  // PHY interrupts
  .o_phy_pie_prog_err_intr   (top_signals_intf.o_phy_pie_prog_err_intr   ),
  .o_phy_ecc_err_intr        (top_signals_intf.o_phy_ecc_err_intr        ),
  .o_phy_rdfptrchk_err_intr  (top_signals_intf.o_phy_rdfptrchk_err_intr  ),
  .o_phy_pie_parity_err_intr (top_signals_intf.o_phy_pie_parity_err_intr ),
  .o_phy_acsm_parity_err_intr(top_signals_intf.o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr      (top_signals_intf.o_phy_trng_fail_intr      ),
  .o_phy_init_cmplt_intr     (top_signals_intf.o_phy_init_cmplt_intr     ),
  .o_phy_trng_cmplt_intr     (top_signals_intf.o_phy_trng_cmplt_intr     ),

  //-------------------------------
  // DFT Interface add by axelera
  //-------------------------------
  .tck   (1'b0),
  .trst  (1'b0),
  .tms   (1'b0),
  .tdi   (1'b0),
  .tdo_en(),
  .tdo   (),

  .ssn_bus_clk     (1'b0),
  .ssn_bus_data_in (24'b0),
  .ssn_bus_data_out(),

  .bisr_clk     (1'b0),
  .bisr_reset   (1'b0),
  .bisr_shift_en(1'b0),
  .bisr_si      (1'b0),
  .bisr_so      (),

  // Observability signals for lpddr
  .o_lpddr_obs(top_signals_intf.o_lpddr_obs),

  //-----------
  // PHY Bump signals
  //-----------
  .BP_MEMRESET_L(RESET_N),
  .BP_A         ({PllDigTst,CA_B[6:4],CS_B,CA_B[3:0],MTEST2,CA_A[6:4],CS_A,CA_A[3:0]}),//{PllDigTst,ddr_if.CA_B[6:4],ddr_if.CS_B,ddr_if.CA_B[3:0],MTEST2,ddr_if.CA[6:4],ddr_if.CS_,ddr_if.CA[3:0]}),
  .BP_ATO       (ATO),// TODO analog signals re-check
  .BP_ATO_PLL   (ATO_PLL),/// TODO analog signals re-check
  .BP_B0_D      ({DMI,WCK_T_A,WCK_C_A,RDQS_T_A,RDQS_C_A,DQ_A[7:0]}), 
  .BP_B1_D      ({DMI,WCK_T_A,WCK_C_A,RDQS_T_A,RDQS_C_A,DQ_A[15:8]}), 
  .BP_B2_D      ({DMI,WCK_T_B,WCK_C_B,RDQS_T_B,RDQS_C_B,DQ_B[7:0]}),
  .BP_B3_D      ({DMI,WCK_T_B,WCK_C_B,RDQS_T_B,RDQS_C_B,DQ_B[15:8]}),
  .BP_CK0_C     (CK0_C),
  .BP_CK0_T     (CK0_T),
  .BP_CK1_C     (CK1_C),
  .BP_CK1_T     (CK1_T),

  .BP_ZN(ZN)// TODO analog signals re-check
    );

    // TODO: Design is aligning Address for PADDR. Need to check documentation.
    always@(apb_master_0_PADDR) begin
      if(apb_master_0_PADDR[25] == 1'b1) begin
        apb_master_0_PADDR_int = apb_master_0_PADDR;
      end
      else begin
        apb_master_0_PADDR_int = {apb_master_0_PADDR,2'b0};
      end
    end

    initial begin	  
	    
      // force hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.U_ddrc_cpf.teengine.RDreplace.te_sel_vpr_entry =0;
      // force hdl_top.LPDDR_P_SUBSYSTEM.dwc_ddrphy_jtag_dfttdrs_Cmd_inst.scan_in = 0;
      // TODO x progation 
      force hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.U_ddrc_cpf.teengine.RDreplace.i_sel_vpr_entry =1;
      // TODO x progation
      // TODO ----------------------------
     
      // TODO this is use for polling match
      assign top_signals_intf.apb_master_0_prdata = apb_master_0_PRDATA;

      // Connection lpddr5 vip with Bump signals
      assign ddr_if.RESET_  = RESET_N;
      assign ddr_if.DM_reg  = DMI;
      assign ddr_if.CA      = CA_A;
      assign ddr_if.CA_B    = CA_B;
      assign ddr_if.CS_     = CS_A;
      assign ddr_if.CS_B    = CS_B;
      assign ddr_if.CK      = CK0_T;
      assign ddr_if.CK_     = CK0_C;
      assign ddr_if.CK_B    = CK1_T;
      assign ddr_if.CK_B_   = CK1_C;
      assign ddr_if.WCK     = WCK_T_A;
      assign ddr_if.WCK_    = WCK_C_A;
      assign ddr_if.WCK_B   = WCK_T_B;
      assign ddr_if.WCK_B_  = WCK_C_B;
      assign ddr_if.RDQS_reg_  = RDQS_C_A;
      assign ddr_if.RDQS_reg   = RDQS_T_A;
      assign ddr_if.RDQS_reg_B_= RDQS_C_B;
      assign ddr_if.RDQS_reg_B = RDQS_T_B;
      assign ddr_if.DQ_reg     = DQ_A;
      assign ddr_if.DQ_B_reg   = DQ_B;
    end

    /* Step 1: check in all memory chips,
        initialize addr_timing and adfi_timing object */
    initial begin
        bit is_3DS2;
	int CL, CWL;
	log = new("hvl_top");
        /* 1. Passing design configuration with runtime arguments:
         use +AMEM_SPEED_BIN=xxx to specify speed bin 
         use +AMEM_DENSITY=xxx to specify density

         NOTE: reference user guide or check src/amem_enum.svh for supported configuration */
	amem_checkin.command_line_extract(log,,
              ddr_timing, type2, bin2, density2, CL, CWL, io_width2);
        /* 2. Or specify design configuration from scratch and passed to BFM 
        For example, run with JEDEC DDR4 3200W speed bin, 2G density, x16 DDR4:
        bin2= AMEM_DDR4_3200W;
        density2= AMEM_2G;
        io_width2= AMEM_BY16;
        //-- End to fill design-specific configuration*/
        bin2= ALPDDR5_SAMSUNG_6400;
        density2= AMEM_2G; // This can be change and should set during elaboration time
        type2= AMEM_TYPE_LPDDR5;
        io_width2= AMEM_BY16; // TODO need to re-check
        //ddr_timing= new(log, bin2, density2, type2, io_width2); // TODO set according to LPDDR5X subsystem features , in uvm different way to setup

    
        log= new("amem_top");
	`ifdef DFI_FREQ_RATIO2
          ratio2= 2;
        `elsif DFI_FREQ_RATIO4
          ratio2= 4;
        `endif

        amem_checkin.TS3DS_support= TOT_LOGIC_RANK - 1;
        is_3DS2= amem_checkin.TS3DS_support != 0;
        amem_checkin.gen_timing(
            log, type2, io_width2, ratio2, // inputs
            ddr_timing, dfi_timing, is_3DS2); // outputs
    
        dfi_timing.owned= 3; // owned by both MC and PHY TODO
        dfi_timing.TS3DS_support= TOT_LOGIC_RANK - 1;
        dfi_timing.set_quick_timing();
        ddr_timing.set_quick_timing();
        ddr_timing.TS_modereg_initialize(2); // set all TS_fields for modereg support fields to 1
        log.info($psprintf("ddr_timing and dfi_timing are created..."));
        ddr_timing.TS_tCKb_timing_check= 0; // CBT was disabled by default(avoid LPDDR5-4.1.1#16/19 error)
    
        `ifdef AVERY_SKIP_POR
           ddr_timing.skip_por = 1;
           chipA.set("start_bfm", 0);
        `elsif AVERY_SKIP_INIT
           ddr_timing.skip_init = 1;
           chipA.set("start_bfm", 0);
        `endif
        // pushed timing object into UVM world
        uvm_config_db #(adfi_timing)::set(uvm_root::get(), "*", "dimm0_dfi_timing", dfi_timing);
        uvm_config_db #(DDR_TIMING)::set(uvm_root::get(), "*", "dimm0_ddr_timing", ddr_timing);
    
        log.info($psprintf("begin memory checkin..."));
        amem_checkin.amemory_checkin(chipA.avy_sparse, 0, 0, mmod_name1); // slice 0, rank 0
        amem_checkin.amemory_checkin(chipA.avy_sparse, 0, 0, mmod_name2); // slice 0, rank 0
        log.info($psprintf("memory checkin is done..."));
    
        `ifdef AMEM_SINGLE_3DS_DEV
            chipA.avy_sparse.TS3DS_support= TOT_LOGIC_RANK-1;
        `endif
        if(!$cast(lpddr5_fast_sim_timing,get_alpddr5_timing(ddr_timing))) begin
          $display("casting failed");
        end
        //lpddr5_fast_sim_timing.tINIT1= 136137500ps;
        lpddr5_fast_sim_timing.set("tINIT5",100ns);
    end

     /* Step 2: timing set up, 
    create ddr BFM and monitor */
    initial begin
      int total_bit; // total bits for data
      ddr_mont_obj_chA = chipA.mon_tracker;
      ddr_mont_obj_chB = chipA.mon_trackerB;

      ddr_mont_obj_chA.assign_vi(ddr_if);
      ddr_mont_obj_chB.assign_vi(ddr_if);
      
      //#1ps; // after all chips have checked in
      log.info($psprintf("begin memory timing setup..."));
      amem_checkin.amemory_timing_setup(ddr_timing, -1, -1, mmod_name1, -1);
      amem_checkin.amemory_timing_setup(ddr_timing, -1, -1, mmod_name2, -1);
      //chipA.set_timing(ddr_timing);
      chipA.ddr_timing = lpddr5_fast_sim_timing;

      log.info($psprintf("memory timing setup is done..."));

      //#3ps; // after sparse class creation in addr3

      // put each memory chip on track file monitoring
      ddr_mont_obj_chA.all_rank_mon= 1;
      ddr_mont_obj_chB.all_rank_mon= 1;
      amem_checkin.amemory_monitor_setup(ddr_mont_obj_chA, mmod_name1, 0);
      amem_checkin.amemory_monitor_setup(ddr_mont_obj_chB, mmod_name2, 0);

      log.info($psprintf("memory monitor setup is done..."));

      // start monitor BFM after set the total bits
      ddr_mont_obj_chA.total_DFIbits = total_bit;
      ddr_mont_obj_chA.set("num_slice_per_cs", 1);
      ddr_mont_obj_chA.set("total_cs", 2);
      ddr_mont_obj_chA.uvm_port_write= 1;
      ddr_mont_obj_chA.set("start_bfm", 1);
      ddr_mont_obj_chB.total_DFIbits = total_bit;
      ddr_mont_obj_chB.set("num_slice_per_cs", 1);
      ddr_mont_obj_chB.set("total_cs", 2);
      ddr_mont_obj_chB.uvm_port_write= 1;
      ddr_mont_obj_chB.set("start_bfm", 1);
      uvm_config_db#(addr_monitor)::set(null,"uvm_test_top.*","ddr_monitorA",ddr_mont_obj_chA);
      uvm_config_db#(addr_monitor)::set(null,"uvm_test_top.*","ddr_monitorB",ddr_mont_obj_chB);
      if (ddr_timing.skip_por || ddr_timing.skip_init) begin
          chipA.set("start_bfm", 1);
          chipA.wait_event("data_structure_ready", 100us);
          #1ps; // intentionally wait before monitor starts
          // copy mode register contents from MC to memory chip directly
          // void'($cast(chipA.por_modereg, dfi_mc_obj.ddr_mrs[0].copy(chipA.por_modereg)));// TODO
      end
      // chipA.bkdoor_sync_up(dfi_mc_obj, dfi_phy_obj, ddr_mont_obj_chA); TODO
    end
endmodule: hdl_top
