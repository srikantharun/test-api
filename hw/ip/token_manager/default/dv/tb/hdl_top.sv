// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: HDL TOP, instatiates the tkn mng aic, the if and starts the test
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
`timescale 1ps/1ps

module hdl_top();

    // Packages import

    import uvm_pkg::*;
    import tkn_mng_uvm_pkg::*;
    import tkn_mng_test_pkg::*;
    import token_manager_pkg::*;
    import token_mgr_mapping_aic_pkg::*;
    import tkn_mng_aic_agent_pkg::*;

    `include "uvm_macros.svh"

    parameter tokmgr_cfg_t LocCfg = token_mgr_mapping_aic_pkg::TOK_MGR_CFG;
    parameter tokmgr_cfg_t TopCfg = token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG;

    string ENV_PATH = "uvm_test_top.env.aic_agent";

    // CLK params
    parameter int unsigned  tkn_mng_freq_mhz            = 1200;
    parameter time          tkn_mng_tol_ps              = 10;
    parameter int unsigned  tkn_mng_reset_cycles    = 10;

    // TIMEOUTS and TICKER

    parameter int unsigned soft_timeout_clk_cycles  = 1_000_000;
    parameter int unsigned hard_timeout_clk_cycles  = 300_000_000; //~2490ms

    parameter int unsigned ticker_clk_cycles        = 3_000; //~249ns
    // Don't change! Only modify clk cycles params
    parameter int unsigned soft_timeout_ns  = soft_timeout_clk_cycles * int'(1000.0 / real'(tkn_mng_freq_mhz));
    parameter int unsigned hard_timeout_ns  = hard_timeout_clk_cycles * int'(1000.0 / real'(tkn_mng_freq_mhz));
    parameter int unsigned ticker_ns        = ticker_clk_cycles * int'(1000.0 / real'(tkn_mng_freq_mhz));


    string testname;



    logic clk;
    logic rst, rst_n;
    string file;



    logic tkn_mng_sync_mvm_exe_swep_en;
    logic tkn_mng_sync_mvm_exe_swep;
    logic tkn_mng_swep_is_acd;
    logic [LocCfg.max_num_prod-1:0] tkn_mng_dev_prod_valid[LocCfg.nr_loc_devs];
    logic [LocCfg.max_num_prod-1:0] tkn_mng_dev_prod_ready[LocCfg.nr_loc_devs];
    logic [LocCfg.max_num_cons-1:0] tkn_mng_dev_cons_valid[LocCfg.nr_loc_devs];
    logic [LocCfg.max_num_cons-1:0] tkn_mng_dev_cons_ready[LocCfg.nr_loc_devs];
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_prod_valid;
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_prod_ready;
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_cons_valid;
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_cons_ready;
    logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] tkn_mng_cid;
    token_manager_pkg::tokmgr_uid_all_t tkn_mng_uid_to_vuid;
    token_manager_pkg::tokmgr_uid_all_t tkn_mng_vuid_to_uid;
    logic [7:0] tkn_mng_tok_prod_ocpl_m_maddr;
    logic tkn_mng_tok_prod_ocpl_m_mcmd;
    logic tkn_mng_tok_prod_ocpl_m_scmdaccept;
    logic [7:0] tkn_mng_tok_prod_ocpl_m_mdata;
    logic [7:0] tkn_mng_tok_cons_ocpl_s_maddr;
    logic tkn_mng_tok_cons_ocpl_s_mcmd;
    logic tkn_mng_tok_cons_ocpl_s_scmdaccept;
    logic [7:0] tkn_mng_tok_cons_ocpl_s_mdata;
    logic [TopCfg.max_num_prod-1:0] tkn_mng_top_prod_valid[TopCfg.nr_loc_devs];
    logic [TopCfg.max_num_prod-1:0] tkn_mng_top_prod_ready[TopCfg.nr_loc_devs];
    logic [TopCfg.max_num_cons-1:0] tkn_mng_top_cons_valid[TopCfg.nr_loc_devs];
    logic [TopCfg.max_num_cons-1:0] tkn_mng_top_cons_ready[TopCfg.nr_loc_devs];
    token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t tkn_mng_axi_s_aw;
    logic tkn_mng_axi_s_aw_ready;
    token_manager_aic_csr_reg_pkg::axi_w_ch_h2d_t tkn_mng_axi_s_w;
    logic tkn_mng_axi_s_w_ready;
    token_manager_aic_csr_reg_pkg::axi_b_ch_d2h_t tkn_mng_axi_s_b;
    logic tkn_mng_axi_s_b_ready;
    token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t tkn_mng_axi_s_ar;
    logic tkn_mng_axi_s_ar_ready;
    token_manager_aic_csr_reg_pkg::axi_r_ch_d2h_t tkn_mng_axi_s_r;
    logic tkn_mng_axi_s_r_ready;
    logic tkn_mng_irq;



    // useful stuff
    bit                 clk_en;


    // initialize values
    initial begin
        clk = 1'b0;
    end



    genvar i, j;
    generate
        for(i = 1; i < $size(DV_TKN_MNG_AIC_CONN_NUM); i++) begin : m_dev_tkn_if_gen
            for(j = 0; j < DV_TKN_MNG_AIC_CONN_NUM[i]; j++) begin : m_dev_conn_tkn_if_gen
                TB_TKN_MNG_AIC_DEV_ENUM current_device = TB_TKN_MNG_AIC_DEV_ENUM'(i);
                string token_connection_name = {current_device.name(), "_TO_", TKN_MNG_AIC_PROD_MAP[j][i].name()};

                token_agent_if m_token_dev_if(clk);
                //connect if
                assign tkn_mng_dev_prod_valid[i][j]     = m_token_dev_if.tok_prod_vld;
                assign m_token_dev_if.tok_prod_rdy      = tkn_mng_dev_prod_ready[i][j];
                assign m_token_dev_if.tok_cons_vld      = tkn_mng_dev_cons_valid[i][j];
                assign tkn_mng_dev_cons_ready[i][j]     = m_token_dev_if.tok_cons_rdy;
                assign m_token_dev_if.reset_n           = rst_n;

                initial begin
                    uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("%s.%s", ENV_PATH, token_connection_name.tolower()), "vif", m_token_dev_if);
                end
            end
        end
    endgenerate

    genvar k;
    generate
        // acd
        for(k = 0; k < DV_TKN_MNG_AIC_ACD_CONN_NUM; k++) begin : m_acd_tkn_if_gen
            TB_TKN_MNG_AIC_DEV_ENUM current_device = TB_TKN_MNG_AIC_DEV_ENUM'(k);
            //create token agent configurations
            string token_connection_name = {"SWEP_OR_ACD", "_TO_", current_device.name()};

            token_agent_if m_token_acd_if(clk);

            //connect if
            assign tkn_mng_acd_prod_valid[k]        = m_token_acd_if.tok_prod_vld;
            assign m_token_acd_if.tok_prod_rdy      = tkn_mng_acd_prod_ready[k];
            assign m_token_acd_if.tok_cons_vld      = tkn_mng_acd_cons_valid[k];
            assign tkn_mng_acd_cons_ready[k]        = m_token_acd_if.tok_cons_rdy;
            assign m_token_acd_if.reset_n           = rst_n;

            initial begin
                uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("%s.%s", ENV_PATH, token_connection_name.tolower()), "vif", m_token_acd_if);
            end

        end
    endgenerate


    // =============================================================================================================
    // CLK RST Instantitation
    // =============================================================================================================
    axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(clk)
                                          );

    axe_rst_generator#(
        .INITIAL_RST(0)
    ) u_axe_rst_generator(
        .i_clk(clk),
        .o_rst(rst)
    );

    always_comb rst_n = ~rst;

    axe_clk_assert u_axe_clk_assert(.clk(clk),
                    .rst_n(rst_n),
                    .freq_mhz(tkn_mng_freq_mhz),
                    .tol_ps  (tkn_mng_tol_ps)
                    );

    axe_timeout u_axe_timeout();

    clk_if u_axe_clk_if(.clk(clk));

    // connect interface
    tkn_mng_aic_interface tkn_mng_aic_if(
        .clk(clk),
        .rst_n(rst_n)
    );

    // =========================
    // Design Under Test (DUT)
    token_manager_aic dut (
        .i_clk(clk),
        .i_rst_n(rst_n),

        .i_sync_mvm_exe_swep_en(0),//temporary, this will be a param of some sort (static value)
        .i_sync_mvm_exe_swep(tkn_mng_sync_mvm_exe_swep),
        .i_swep_is_acd(1),//temporary, this will be a param of some sort (static value)
        .i_dev_prod_valid(tkn_mng_dev_prod_valid),
        .o_dev_prod_ready(tkn_mng_dev_prod_ready),
        .o_dev_cons_valid(tkn_mng_dev_cons_valid),
        .i_dev_cons_ready(tkn_mng_dev_cons_ready),
        .i_acd_prod_valid(tkn_mng_acd_prod_valid),
        .o_acd_prod_ready(tkn_mng_acd_prod_ready),
        .o_acd_cons_valid(tkn_mng_acd_cons_valid),
        .i_acd_cons_ready(tkn_mng_acd_cons_ready),
        .i_cid(tkn_mng_cid),
        .i_uid_to_vuid(tkn_mng_uid_to_vuid),
        .i_vuid_to_uid(tkn_mng_vuid_to_uid),
        .o_tok_prod_ocpl_m_maddr(tkn_mng_tok_prod_ocpl_m_maddr),
        .o_tok_prod_ocpl_m_mcmd(tkn_mng_tok_prod_ocpl_m_mcmd),
        .i_tok_prod_ocpl_m_scmdaccept(tkn_mng_tok_prod_ocpl_m_scmdaccept),
        .o_tok_prod_ocpl_m_mdata(tkn_mng_tok_prod_ocpl_m_mdata),
        .i_tok_cons_ocpl_s_maddr(tkn_mng_tok_cons_ocpl_s_maddr),
        .i_tok_cons_ocpl_s_mcmd(tkn_mng_tok_cons_ocpl_s_mcmd),
        .o_tok_cons_ocpl_s_scmdaccept(tkn_mng_tok_cons_ocpl_s_scmdaccept),
        .i_tok_cons_ocpl_s_mdata(tkn_mng_tok_cons_ocpl_s_mdata),
        .i_top_prod_valid(tkn_mng_top_prod_valid),
        .o_top_prod_ready(tkn_mng_top_prod_ready),
        .o_top_cons_valid(tkn_mng_top_cons_valid),
        .i_top_cons_ready(tkn_mng_top_cons_ready),
        .i_axi_s_aw(tkn_mng_axi_s_aw),
        .o_axi_s_aw_ready(tkn_mng_axi_s_aw_ready),
        .i_axi_s_w(tkn_mng_axi_s_w),
        .o_axi_s_w_ready(tkn_mng_axi_s_w_ready),
        .o_axi_s_b(tkn_mng_axi_s_b),
        .i_axi_s_b_ready(tkn_mng_axi_s_b_ready),
        .i_axi_s_ar(tkn_mng_axi_s_ar),
        .o_axi_s_ar_ready(tkn_mng_axi_s_ar_ready),
        .o_axi_s_r(tkn_mng_axi_s_r),
        .i_axi_s_r_ready(tkn_mng_axi_s_r_ready),
        .o_irq(tkn_mng_irq)
    );



    initial begin
        // clock generator
        u_axe_clk_generator.set_clock(.freq_mhz(tkn_mng_freq_mhz), .duty(50));
        clk_en = 1'b1;
        // reset generator
        u_axe_clk_if.await_rising_edge(10);
        u_axe_rst_generator.sync_rst(.duration_cycles(tkn_mng_reset_cycles));
    end

    // Configure ticker/timeout
    initial begin
        u_axe_timeout.timeout(soft_timeout_ns, hard_timeout_ns);
        u_axe_timeout.ticker(ticker_ns);
    end



    initial begin
        uvm_config_db#(virtual clk_if)::set(uvm_root::get(), "*", "u_axe_clk_if", u_axe_clk_if);
        uvm_config_db#(virtual tkn_mng_aic_interface)::set(uvm_root::get(), "*", "tkn_mng_aic_if", tkn_mng_aic_if);

        run_test ();
    end


endmodule

