// AI CORE MVM hdl top
`define AXI_VIP
`define AXI_VIP_CONN_M
`define AXI_VIP_CONN_S
`define AXI_VIP_CONN_CFG

`define DUT dut

`define MVM_DUT `DUT
`define MVM_SUBIP .u_ai_core_mvm.i_mvm
`define MVM_SUBIP_PATH `MVM_DUT`MVM_SUBIP
`define PATH_PAIR(id_pair) `MVM_SUBIP_PATH.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[``id_pair``].inst_mvm_imc_acc_pair
`define PATH_IMC_W_ACC(id_pair, id_side) `PATH_PAIR(``id_pair``).inst_imc_bank_acc_``id_side``.inst_imc_w_acc
`define IMC_W_ACC_SIGNAL(id_pair, id_side, sig_name) `PATH_IMC_W_ACC(``id_pair``, ``id_side``).``sig_name``

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ns;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import imc_bank_pkg::*;
  import ai_core_mvm_common_pkg::*;
  import mvm_pkg::*;
  import ai_core_mvm_test_pkg::*;
  import aic_addr_map_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  `include "bind_ai_core_mvm.svh"

  import ai_core_mvm_common_pkg::*;
  realtime CLK_PERIOD_JTAG = 10ns;

  logic   clk_en;
  logic i_clk;
  logic i_rst_n;
  logic jtag_tcki=0;
  logic jtag_i_rst_n;

  //--------------------------------------------------
  // AXI4 Config port
  //--------------------------------------------------
  // AXI write address channel
  logic                                       ai_core_mvm_axi_s_awvalid;
  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] ai_core_mvm_axi_s_awaddr;
  logic [AIC_LT_AXI_S_ID_WIDTH-1:0] ai_core_mvm_axi_s_awid;
  logic [AIC_LT_AXI_LEN_WIDTH-1:0] ai_core_mvm_axi_s_awlen;
  logic [AIC_LT_AXI_SIZE_WIDTH-1:0] ai_core_mvm_axi_s_awsize;
  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] ai_core_mvm_axi_s_awburst;
  //TODO: currently cache/prot signals are commented by Design
  //Kindly update in future
  //logic [AIC_LT_AXI_CACHE_WIDTH-1:0]       ai_core_mvm_axi_s_awcache;
  //logic [AIC_LT_AXI_PROT_WIDTH-1:0]        ai_core_mvm_axi_s_awprot;
  //logic                                       ai_core_mvm_axi_s_awlock;
  logic                                       ai_core_mvm_axi_s_awready;
  // AXI write data channel
  logic                                       ai_core_mvm_axi_s_wvalid;
  logic                                       ai_core_mvm_axi_s_wlast;
  logic [AIC_LT_AXI_WSTRB_WIDTH-1:0] ai_core_mvm_axi_s_wstrb;
  logic [AIC_LT_AXI_DATA_WIDTH-1:0] ai_core_mvm_axi_s_wdata;
  logic                                       ai_core_mvm_axi_s_wready;
  // AXI write response channel
  logic                                       ai_core_mvm_axi_s_bvalid;
  logic [AIC_LT_AXI_S_ID_WIDTH-1:0] ai_core_mvm_axi_s_bid;
  logic [AIC_LT_AXI_RESP_WIDTH-1:0] ai_core_mvm_axi_s_bresp;
  logic                                       ai_core_mvm_axi_s_bready;
  // AXI read address channel
  logic                                       ai_core_mvm_axi_s_arvalid;
  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] ai_core_mvm_axi_s_araddr;
  logic [AIC_LT_AXI_S_ID_WIDTH-1:0] ai_core_mvm_axi_s_arid;
  logic [AIC_LT_AXI_LEN_WIDTH-1:0] ai_core_mvm_axi_s_arlen;
  logic [AIC_LT_AXI_SIZE_WIDTH-1:0] ai_core_mvm_axi_s_arsize;
  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] ai_core_mvm_axi_s_arburst;
  //logic [AIC_LT_AXI_CACHE_WIDTH-1:0]       ai_core_mvm_axi_s_arcache;
  //logic [AIC_LT_AXI_PROT_WIDTH-1:0]        ai_core_mvm_axi_s_arprot;
  //logic                                    ai_core_mvm_axi_s_arlock;
  logic                                       ai_core_mvm_axi_s_arready;
  // AXI read data/response channel
  logic                                       ai_core_mvm_axi_s_rvalid;
  logic                                       ai_core_mvm_axi_s_rlast;
  logic [AIC_LT_AXI_S_ID_WIDTH-1:0] ai_core_mvm_axi_s_rid;
  logic [AIC_LT_AXI_DATA_WIDTH-1:0] ai_core_mvm_axi_s_rdata;
  logic [AIC_LT_AXI_RESP_WIDTH-1:0] ai_core_mvm_axi_s_rresp;
  logic                                       ai_core_mvm_axi_s_rready;

  // Tokens

  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] ai_core_mvm_exe_tok_prod_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] ai_core_mvm_exe_tok_prod_rdy;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] ai_core_mvm_exe_tok_cons_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] ai_core_mvm_exe_tok_cons_rdy;
  //TODO: currently ai_core_mvm_exe_trace_vld signal is not present in Design
  //Kindly update in future
  //logic ai_core_mvm_exe_trace_vld;

  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] ai_core_mvm_prg_tok_prod_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] ai_core_mvm_prg_tok_prod_rdy;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] ai_core_mvm_prg_tok_cons_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] ai_core_mvm_prg_tok_cons_rdy;
  //TODO: currently ai_core_mvm_prg_trace_vld signal is not present in Design
  //Kindly update in future
  //logic ai_core_mvm_prg_trace_vld;

  // IFD0 AXI stream
  logic                                 mvm_ifd0_axis_s_tvalid;
  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] mvm_ifd0_axis_s_tdata;
  logic                                 mvm_ifd0_axis_s_tlast;
  logic                                 mvm_ifd0_axis_s_tready;

// IFD2 AXI stream
  logic                                 mvm_ifd2_axis_s_tvalid;
  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] mvm_ifd2_axis_s_tdata;
  logic                                 mvm_ifd2_axis_s_tlast;
  logic                                 mvm_ifd2_axis_s_tready;

  // IFDW AXI stream
  logic                                 mvm_ifdw_axis_s_tvalid;
  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] mvm_ifdw_axis_s_tdata;
  // input  logic [PWORD_i8_AXIS_TSTRB_WIDTH-1:0] mvm_ifdw_axis_s_tstrb;
  logic                                 mvm_ifdw_axis_s_tlast;
  logic                                 mvm_ifdw_axis_s_tready;

  // IAU AXI stream
  logic                                  mvm_iau_axis_m_tvalid;
  logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] mvm_iau_axis_m_tdata;
  //  logic [PWORD_i26_AXIS_TSTRB_WIDTH-1:0] mvm_iau_axis_m_tstrb;
  logic                                  mvm_iau_axis_m_tlast;
  logic                                  mvm_iau_axis_m_tready;

  logic irq_out;

  // Util signals
  logic [          MVM_UTIL_INTERFACE_WIDTH-1:0] mvm_util_limit_value_i ;// = '0;
  logic                                          mvm_util_limit_enable_i;// = '0;
  logic [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0] mvm_util_average_nominator_i;// = '0;
  logic [          MVM_UTIL_INTERFACE_WIDTH-1:0] mvm_util_average_o;

  // DFT signals
  logic test_mode;
  logic imc_bist_fast_clk_en_o;
  logic jtag_seli;
  logic jtag_sei;
  logic jtag_cei;
  logic jtag_uei;
  logic jtag_tdi;
  logic jtag_tdo;

  // AIC CSR:
  imc_bist_pkg::aic_csr_hw2reg_t aic_csr_hw2reg;
  imc_bist_pkg::aic_csr_reg2hw_t aic_csr_reg2hw;
  imc_bist_pkg::aic_csr_reg2hw_t loopback_aic_csr_reg2hw;

  // IMC BIST
  logic imc_bist_busy_o;
  logic imc_bist_done_o;
  logic imc_bist_pass_o;

  // Observation signals
  logic [AIC_DEV_OBS_DW-1:0] ai_core_mvm_exe_obs;
  logic [AIC_DEV_OBS_DW-1:0] ai_core_mvm_prg_obs;

  // CID
  logic [AIC_CID_SUB_W-1:0] cid_i;
  //TODO need to connect
  logic [AIC_BLOCK_ID_WIDTH-1:0] block_id_i;
  time               clk_tol_ps    = 10;
  int 		     mvm_freq_mhz  = 1200;

  `ifndef EUROPA_ADDR_MAP
  localparam longint REGION_ST_ADDR[6]  = ai_core_mvm_common_pkg::MVM_REGION_ST_ADDR;
  localparam longint REGION_END_ADDR[6] = ai_core_mvm_common_pkg::MVM_REGION_END_ADDR;
  `else
  // Europa addr map
  localparam longint REGION_ST_ADDR[6]  = aic_addr_map_pkg::AIC_LOC_M_MVM_REGION_ST_ADDR;
  localparam longint REGION_END_ADDR[6] = aic_addr_map_pkg::AIC_LOC_M_MVM_REGION_END_ADDR;
  `endif

   mvm_pkg::prog_mode_e  prog_mode;





  //logic [aic_common_pkg::PHASE_ACC_WIDTH-1:0] clk_div_ctrl_incr_i   ;
  //logic                                   clk_div_ctrl_enable_i ;
  //logic                                   clk_div_ctrl_clear_i  ;
  //logic                                   clk_div_ctrl_cg_en_o;

//`ifdef TARGET_DFT
//  logic                                   test_clock;
//  logic                                   edt_update;
//  logic                                   scan_en;
//  logic [DFT_SCAN_W-1:0]                  scan_in;
//  logic [DFT_SCAN_W-1:0]                  scan_out;
//`endif



  // =============================================================================================================
  // Instantiate interfaces and BFMs and assignments
  // =============================================================================================================

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
  assign axi_if.master_if[0].aresetn =  ~ axi_reset_if.reset;
  assign axi_if.master_if[1].aresetn =  ~ axi_reset_if.reset;
  assign axi_if.master_if[2].aresetn =  ~ axi_reset_if.reset;
  assign axi_if.master_if[3].aresetn =  ~ axi_reset_if.reset;
  assign axi_if.slave_if[0].aresetn  =  ~ axi_reset_if.reset;
  assign i_rst_n                     =  ~ axi_reset_if.reset;
`endif


  // AXIS:
  //------------------------------------------------------
  // MVM IFDW
  assign mvm_ifdw_axis_s_tvalid     = axi_if.master_if[1].tvalid; //  TB output port
  assign axi_if.master_if[1].tready = mvm_ifdw_axis_s_tready ;    // TB input port
  assign mvm_ifdw_axis_s_tdata      = axi_if.master_if[1].tdata;  //   TB output port
  assign mvm_ifdw_axis_s_tlast      = axi_if.master_if[1].tlast;  //   TB Output port

  // MVM IFD0
  assign mvm_ifd0_axis_s_tvalid     = axi_if.master_if[2].tvalid; // TB output port
  assign axi_if.master_if[2].tready = mvm_ifd0_axis_s_tready;     // TB input port
  assign mvm_ifd0_axis_s_tdata      = axi_if.master_if[2].tdata;  // TB output port
  assign mvm_ifd0_axis_s_tlast      = axi_if.master_if[2].tlast;  // TB output port

   // MVM IFD2
  assign mvm_ifd2_axis_s_tvalid     = axi_if.master_if[3].tvalid; // TB output port
  assign axi_if.master_if[3].tready = mvm_ifd2_axis_s_tready;     // TB input port
  assign mvm_ifd2_axis_s_tdata      = axi_if.master_if[3].tdata;  // TB output port
  assign mvm_ifd2_axis_s_tlast      = axi_if.master_if[3].tlast;  // TB output port


  // MVM IAU
  assign axi_if.slave_if[0].tvalid  = mvm_iau_axis_m_tvalid;     // TB input port
  assign mvm_iau_axis_m_tready      = axi_if.slave_if[0].tready; // TB output port
  assign axi_if.slave_if[0].tdata   = mvm_iau_axis_m_tdata;      // TB input port
  assign axi_if.slave_if[0].tlast   = mvm_iau_axis_m_tlast;      // TB input port


 // AXI LP interface
`ifdef AXI_VIP_CONN_M
  assign ai_core_mvm_axi_s_awvalid = axi_if.master_if[0].awvalid;
  assign ai_core_mvm_axi_s_awaddr  = axi_if.master_if[0].awaddr;
  assign ai_core_mvm_axi_s_awid    = axi_if.master_if[0].awid;
  assign ai_core_mvm_axi_s_awlen   = axi_if.master_if[0].awlen;
  assign ai_core_mvm_axi_s_awsize  = axi_if.master_if[0].awsize;
  assign ai_core_mvm_axi_s_awburst = axi_if.master_if[0].awburst;
  //assign ai_core_mvm_axi_s_awlock  = axi_if.master_if[0].awlock;
  //assign ai_core_mvm_axi_s_awcache = axi_if.master_if[0].awcache;
  //assign ai_core_mvm_axi_s_awprot  = axi_if.master_if[0].awprot;

  assign axi_if.master_if[0].awready = ai_core_mvm_axi_s_awready;

  assign ai_core_mvm_axi_s_wvalid  = axi_if.master_if[0].wvalid;
  assign ai_core_mvm_axi_s_wlast   = axi_if.master_if[0].wlast;
  assign ai_core_mvm_axi_s_wdata   = axi_if.master_if[0].wdata;
  assign ai_core_mvm_axi_s_wstrb   = axi_if.master_if[0].wstrb;

  assign axi_if.master_if[0].wready = ai_core_mvm_axi_s_wready;

  assign axi_if.master_if[0].bvalid = ai_core_mvm_axi_s_bvalid;
  assign axi_if.master_if[0].bid    = ai_core_mvm_axi_s_bid;
  assign axi_if.master_if[0].bresp  = ai_core_mvm_axi_s_bresp;

  assign ai_core_mvm_axi_s_bready  = axi_if.master_if[0].bready;

  assign ai_core_mvm_axi_s_arvalid = axi_if.master_if[0].arvalid;
  assign ai_core_mvm_axi_s_araddr  = axi_if.master_if[0].araddr;
  assign ai_core_mvm_axi_s_arid    = axi_if.master_if[0].arid;
  assign ai_core_mvm_axi_s_arlen   = axi_if.master_if[0].arlen;
  assign ai_core_mvm_axi_s_arsize  = axi_if.master_if[0].arsize;
  assign ai_core_mvm_axi_s_arburst = axi_if.master_if[0].arburst;
  //assign ai_core_mvm_axi_s_arlock  = axi_if.master_if[0].arlock;
  //assign ai_core_mvm_axi_s_arcache = axi_if.master_if[0].arcache;
  //assign ai_core_mvm_axi_s_arprot  = axi_if.master_if[0].arprot;

  assign axi_if.master_if[0].arready = ai_core_mvm_axi_s_arready;

  assign axi_if.master_if[0].rvalid = ai_core_mvm_axi_s_rvalid;
  assign axi_if.master_if[0].rlast  = ai_core_mvm_axi_s_rlast;
  assign axi_if.master_if[0].rid    = ai_core_mvm_axi_s_rid;
  assign axi_if.master_if[0].rdata  = ai_core_mvm_axi_s_rdata;
  assign axi_if.master_if[0].rresp  = ai_core_mvm_axi_s_rresp;

  assign ai_core_mvm_axi_s_rready  = axi_if.master_if[0].rready;



`endif

assign block_id_i = aic_common_pkg::AIC_BLOCK_ID_M_MVM;



axe_clk_generator u_mvm_clk_generator(.i_enable(clk_en),
			              .o_clk(i_clk)
				      );

axe_clk_assert u_axe_clk_assert(.clk(i_clk),
				.rst_n(i_rst_n),
				.freq_mhz(mvm_freq_mhz),
				.tol_ps(clk_tol_ps)
				);



  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
  token_agent_if tok_agt_exe_if[2] (i_clk);
  token_agent_if tok_agt_prg_if[2] (i_clk);
  cc_clk_div_agent_if clk_div_agt_if(i_clk);

  // =============================================================================================================
  // MVM UTILS FILTER INTERFACE
  // =============================================================================================================
  mvm_utils_filter_intf mvm_utils_intf(hdl_top.dut.i_mvm_dp.u_mvm_par2bser_util_ctrl.inst_exp_avg_util.i_clk,i_rst_n);

  // =============================================================================================================
  // MVM user define INTERFACE
  // =============================================================================================================
  mvm_if mvm_if (i_clk, i_rst_n);

  assign aic_csr_reg2hw = '{
    imc_bist_cmd   : mvm_if.aic_csr_reg2hw.imc_bist_cmd,
    imc_bist_cfg   : mvm_if.aic_csr_reg2hw.imc_bist_cfg,
    imc_bist_status: loopback_aic_csr_reg2hw.imc_bist_status
  };




  assign mvm_if.prgmode = dut.i_mvm_prg_cmd_gen.cmd_data_reg.prog.prog_mode;
  assign mvm_if.broadcast_mode = dut.i_mvm_prg_cmd_gen.cmd_data_reg.prog.broadcast;

  //monitor cmd_done
   always @(posedge i_clk) begin
     if (dut.i_mvm_exe_cmd_block.cmd_done) begin
        mvm_if.cmdblk_cmd_done_count <= mvm_if.cmdblk_cmd_done_count + 1;
     end
   end



  // =============================================================================================================
  // MVM POWER SURGE CHECK
  // =============================================================================================================
  mvm_power_surge_check_intf mvm_power_surge_intf(hdl_top.dut.i_mvm_dp.inst_mvm_imc_acc.i_clk,hdl_top.dut.i_mvm_dp.inst_mvm_imc_acc.i_rst_n);
  assign mvm_power_surge_intf.compute_gate_clock[0]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[1]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[2]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[3]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[4]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[5]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[6]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[7]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[8]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[9]  = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[10] = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[11] = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[12] = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[13] = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[14] = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_gate_clock;
  assign mvm_power_surge_intf.compute_gate_clock[15] = dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_gate_clock;

  assign mvm_power_surge_intf.compute_block_enable[0]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[1]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[2]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[3]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[4]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[5]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[6]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[7]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[8]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[9]  = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[10] = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[11] = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[12] = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[13] = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[14] = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;
  assign mvm_power_surge_intf.compute_block_enable[15] = |dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.i_compute_block_enable;

`ifdef DUMP_IMC_BANKS
  // =============================================================================================================
  // Dump IMC bank data
  // =============================================================================================================
  `define PATH_TO_BANK(id_p, id_s, id_w) dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[``id_p``].inst_mvm_imc_acc_pair.inst_imc_bank_acc_``id_s``.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[``id_w``].u_mvm_imc_bank_wrapper

  bind `PATH_TO_BANK(0, a, 0).u_imc_bank imc_bank_dumper #(.ID( 0), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(0, a, 1).u_imc_bank imc_bank_dumper #(.ID( 0), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(0, b, 0).u_imc_bank imc_bank_dumper #(.ID( 2), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(0, b, 1).u_imc_bank imc_bank_dumper #(.ID( 2), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(1, a, 0).u_imc_bank imc_bank_dumper #(.ID( 1), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(1, a, 1).u_imc_bank imc_bank_dumper #(.ID( 1), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(1, b, 0).u_imc_bank imc_bank_dumper #(.ID( 3), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(1, b, 1).u_imc_bank imc_bank_dumper #(.ID( 3), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(2, a, 0).u_imc_bank imc_bank_dumper #(.ID( 4), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(2, a, 1).u_imc_bank imc_bank_dumper #(.ID( 4), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(2, b, 0).u_imc_bank imc_bank_dumper #(.ID( 6), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(2, b, 1).u_imc_bank imc_bank_dumper #(.ID( 6), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(3, a, 0).u_imc_bank imc_bank_dumper #(.ID( 5), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(3, a, 1).u_imc_bank imc_bank_dumper #(.ID( 5), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(3, b, 0).u_imc_bank imc_bank_dumper #(.ID( 7), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(3, b, 1).u_imc_bank imc_bank_dumper #(.ID( 7), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(4, a, 0).u_imc_bank imc_bank_dumper #(.ID( 8), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(4, a, 1).u_imc_bank imc_bank_dumper #(.ID( 8), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(4, b, 0).u_imc_bank imc_bank_dumper #(.ID(10), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(4, b, 1).u_imc_bank imc_bank_dumper #(.ID(10), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(5, a, 0).u_imc_bank imc_bank_dumper #(.ID( 9), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(5, a, 1).u_imc_bank imc_bank_dumper #(.ID( 9), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(5, b, 0).u_imc_bank imc_bank_dumper #(.ID(11), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(5, b, 1).u_imc_bank imc_bank_dumper #(.ID(11), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(6, a, 0).u_imc_bank imc_bank_dumper #(.ID(12), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(6, a, 1).u_imc_bank imc_bank_dumper #(.ID(12), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(6, b, 0).u_imc_bank imc_bank_dumper #(.ID(14), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(6, b, 1).u_imc_bank imc_bank_dumper #(.ID(14), .SUB_ID(1)) u_bank_dumper (.*);

  bind `PATH_TO_BANK(7, a, 0).u_imc_bank imc_bank_dumper #(.ID(13), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(7, a, 1).u_imc_bank imc_bank_dumper #(.ID(13), .SUB_ID(1)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(7, b, 0).u_imc_bank imc_bank_dumper #(.ID(15), .SUB_ID(0)) u_bank_dumper (.*);
  bind `PATH_TO_BANK(7, b, 1).u_imc_bank imc_bank_dumper #(.ID(15), .SUB_ID(1)) u_bank_dumper (.*);
`endif // DUMP_IMC_BANKS

  // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
`ifndef NO_DUT
  mvm #
  (
      .REGION_ST_ADDR(REGION_ST_ADDR),
      .REGION_END_ADDR(REGION_END_ADDR)
  ) dut (
    .i_clk,
    .i_rst_n,
    .i_jtag_tck(jtag_tcki),
    .jtag_i_rst_n(jtag_i_rst_n),
    // AXI write address channel
    .i_ai_core_mvm_axi_s_awvalid(ai_core_mvm_axi_s_awvalid),
    .i_ai_core_mvm_axi_s_awaddr (ai_core_mvm_axi_s_awaddr ),
    .i_ai_core_mvm_axi_s_awid   (ai_core_mvm_axi_s_awid   ),
    .i_ai_core_mvm_axi_s_awlen  (ai_core_mvm_axi_s_awlen  ),
    .i_ai_core_mvm_axi_s_awsize (ai_core_mvm_axi_s_awsize ),
    .i_ai_core_mvm_axi_s_awburst(ai_core_mvm_axi_s_awburst),
    .o_ai_core_mvm_axi_s_awready(ai_core_mvm_axi_s_awready),
    // AXI write data channel
    .i_ai_core_mvm_axi_s_wvalid (ai_core_mvm_axi_s_wvalid),
    .i_ai_core_mvm_axi_s_wlast  (ai_core_mvm_axi_s_wlast ),
    .i_ai_core_mvm_axi_s_wstrb  (ai_core_mvm_axi_s_wstrb ),
    .i_ai_core_mvm_axi_s_wdata  (ai_core_mvm_axi_s_wdata ),
    .o_ai_core_mvm_axi_s_wready (ai_core_mvm_axi_s_wready),
    // AXI write response channel
    .o_ai_core_mvm_axi_s_bvalid (ai_core_mvm_axi_s_bvalid),
    .o_ai_core_mvm_axi_s_bid    (ai_core_mvm_axi_s_bid   ),
    .o_ai_core_mvm_axi_s_bresp  (ai_core_mvm_axi_s_bresp ),
    .i_ai_core_mvm_axi_s_bready (ai_core_mvm_axi_s_bready),
    // AXI read address channel
    .i_ai_core_mvm_axi_s_arvalid(ai_core_mvm_axi_s_arvalid),
    .i_ai_core_mvm_axi_s_araddr (ai_core_mvm_axi_s_araddr ),
    .i_ai_core_mvm_axi_s_arid   (ai_core_mvm_axi_s_arid   ),
    .i_ai_core_mvm_axi_s_arlen  (ai_core_mvm_axi_s_arlen  ),
    .i_ai_core_mvm_axi_s_arsize (ai_core_mvm_axi_s_arsize ),
    .i_ai_core_mvm_axi_s_arburst(ai_core_mvm_axi_s_arburst),
    .o_ai_core_mvm_axi_s_arready(ai_core_mvm_axi_s_arready),
    // AXI read data/response channel
    .o_ai_core_mvm_axi_s_rvalid (ai_core_mvm_axi_s_rvalid),
    .o_ai_core_mvm_axi_s_rlast  (ai_core_mvm_axi_s_rlast ),
    .o_ai_core_mvm_axi_s_rid    (ai_core_mvm_axi_s_rid   ),
    .o_ai_core_mvm_axi_s_rdata  (ai_core_mvm_axi_s_rdata ),
    .o_ai_core_mvm_axi_s_rresp  (ai_core_mvm_axi_s_rresp ),
    .i_ai_core_mvm_axi_s_rready (ai_core_mvm_axi_s_rready),

    // Tokens
    .o_ai_core_mvm_exe_tok_prod_vld(ai_core_mvm_exe_tok_prod_vld),
    .i_ai_core_mvm_exe_tok_prod_rdy(ai_core_mvm_exe_tok_prod_rdy),
    .i_ai_core_mvm_exe_tok_cons_vld(ai_core_mvm_exe_tok_cons_vld),
    .o_ai_core_mvm_exe_tok_cons_rdy(ai_core_mvm_exe_tok_cons_rdy),

    .o_ai_core_mvm_prg_tok_prod_vld(ai_core_mvm_prg_tok_prod_vld),
    .i_ai_core_mvm_prg_tok_prod_rdy(ai_core_mvm_prg_tok_prod_rdy),
    .i_ai_core_mvm_prg_tok_cons_vld(ai_core_mvm_prg_tok_cons_vld),
    .o_ai_core_mvm_prg_tok_cons_rdy(ai_core_mvm_prg_tok_cons_rdy),

    // IFD0 AXI stream
    .i_mvm_ifd0_axis_s_tvalid (mvm_ifd0_axis_s_tvalid),
    .i_mvm_ifd0_axis_s_tdata  (mvm_ifd0_axis_s_tdata ),
    .i_mvm_ifd0_axis_s_tlast  (mvm_ifd0_axis_s_tlast ),
    .o_mvm_ifd0_axis_s_tready (mvm_ifd0_axis_s_tready),

    // IFD0 AXI stream
    // TODO: Double input BW feature
    .i_mvm_ifd2_axis_s_tvalid (mvm_ifd2_axis_s_tvalid),
    .i_mvm_ifd2_axis_s_tdata  (mvm_ifd2_axis_s_tdata),
    .i_mvm_ifd2_axis_s_tlast  (mvm_ifd2_axis_s_tlast),
    .o_mvm_ifd2_axis_s_tready (mvm_ifd2_axis_s_tready),

    // IFDW AXI stream
    .i_mvm_ifdw_axis_s_tvalid (mvm_ifdw_axis_s_tvalid),
    .i_mvm_ifdw_axis_s_tdata  (mvm_ifdw_axis_s_tdata ),
    .i_mvm_ifdw_axis_s_tlast  (mvm_ifdw_axis_s_tlast ),
    .o_mvm_ifdw_axis_s_tready (mvm_ifdw_axis_s_tready),

    // IAU AXI stream
    .o_mvm_iau_axis_m_tvalid (mvm_iau_axis_m_tvalid),
    .o_mvm_iau_axis_m_tdata  (mvm_iau_axis_m_tdata ),
    .o_mvm_iau_axis_m_tlast  (mvm_iau_axis_m_tlast ),
    .i_mvm_iau_axis_m_tready (mvm_iau_axis_m_tready),

    // UTIL limit
    .i_mvm_util_limit_value       ('0),// TODO: Controls the utilisation limit
    .i_mvm_util_limit_enable      ('0),// TODO: Controls the utilisation limit
    .i_mvm_util_average_nominator ('0),// TODO: Controls the utilisation limit
    .o_mvm_util_average           (),  // TODO: Controls the utilisation limit
    // NOP injection
    .i_mvm_nop_inj_rate_value     ('0), // TODO: Controls the fast nop injection mechanism
    .i_mvm_nop_inj_rate_enable    ('0), // TODO: Controls the fast nop injection mechanism
    // TODO: Drive this input port properly to check the ramp up functionality
    .i_ramp_budget_ctrl (mvm_ramp_up_ctrl_pkg::ramp_up_ctrl_t'{default: 0, budget_cost_base: 72, budget_clip: 72, budget_increment: 72}),

    // IRQ
    .o_irq                  (irq_out),

    // DFT signals
    .i_test_mode            (test_mode),
    .o_imc_bist_fast_clk_en (imc_bist_fast_clk_en_o),

    // Observation signals
    .o_ai_core_mvm_exe_obs      (ai_core_mvm_exe_obs),
    .o_ai_core_mvm_prg_obs      (ai_core_mvm_prg_obs),

    //// Block Identification
    .i_cid     (cid_i     ),
    .i_block_id(block_id_i),

    // JTAG
    .i_jtag_sel (jtag_seli),
    .i_jtag_se  (jtag_sei ),
    .i_jtag_ce  (jtag_cei ),
    .i_jtag_ue  (jtag_uei ),
    .i_jtag_td  (jtag_tdi ),
    .o_jtag_td  (jtag_tdo ),

    // AIC CSR
    .i_aic_bist_csr_reg2hw(aic_csr_reg2hw),
    .o_aic_bist_csr_hw2reg(aic_csr_hw2reg),

    // IMC BIST
    .o_imc_bist_busy       (imc_bist_busy_o      ),
    .o_imc_bist_done       (imc_bist_done_o      ),
    .o_imc_bist_pass       (imc_bist_pass_o      )
  );
`endif

  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (1'h0)
  ) u_imc_bist_status_busy (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.busy.de),
    .d      (aic_csr_hw2reg.imc_bist_status.busy.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.busy.q),

    // to register interface (read)
    .qs     ()
  );

  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (1'h0)
  ) u_imc_bist_status_done (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.done.de),
    .d      (aic_csr_hw2reg.imc_bist_status.done.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.done.q),

    // to register interface (read)
    .qs     ()
  );

  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (1'h0)
  ) u_imc_bist_status_pass (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.pass.de),
    .d      (aic_csr_hw2reg.imc_bist_status.pass.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.pass.q),

    // to register interface (read)
    .qs     ()
  );

  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (1'h0)
  ) u_imc_bist_status_repair_needed (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.repair_needed.de),
    .d      (aic_csr_hw2reg.imc_bist_status.repair_needed.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.repair_needed.q),

    // to register interface (read)
    .qs     ()
  );

  prim_subreg #(
    .DW      (4),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (4'h0)
  ) u_imc_bist_status_error_bank (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.error_bank.de),
    .d      (aic_csr_hw2reg.imc_bist_status.error_bank.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.error_bank.q),

    // to register interface (read)
    .qs     ()
  );

  prim_subreg #(
    .DW      (5),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (5'h0)
  ) u_imc_bist_status_error_col (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.error_col.de),
    .d      (aic_csr_hw2reg.imc_bist_status.error_col.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.error_col.q),

    // to register interface (read)
    .qs     ()
  );

  prim_subreg #(
    .DW      (24),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (24'h0)
  ) u_imc_bist_status_error_cycle (
    .clk_i   (i_clk),
    .rst_ni  (i_rst_n),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (aic_csr_hw2reg.imc_bist_status.error_cycle.de),
    .d      (aic_csr_hw2reg.imc_bist_status.error_cycle.d),

    // to internal hardware
    // spyglass disable_block W287b
    .qe     (),
    // spyglass enable_block W287b
    .q      (loopback_aic_csr_reg2hw.imc_bist_status.error_cycle.q),

    // to register interface (read)
    .qs     ()
  );

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate the clock
  initial begin
    u_mvm_clk_generator.set_clock(.freq_mhz(mvm_freq_mhz), .duty(50));
    clk_en = 1'b1;
  end

  initial begin
    jtag_i_rst_n = 1'b0;
    #(CLK_PERIOD_JTAG*13);
    jtag_i_rst_n = 1'b1;
  end

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

    /** Provide token agent interfaces */
    uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("uvm_test_top.env.tok_agt[%0d][0]", VERIF_MVM_PRG_TOK_AGT), "vif", tok_agt_prg_if[0]);
    uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("uvm_test_top.env.tok_agt[%0d][1]", VERIF_MVM_PRG_TOK_AGT), "vif", tok_agt_prg_if[1]);
    uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("uvm_test_top.env.tok_agt[%0d][0]", VERIF_MVM_EXE_TOK_AGT), "vif", tok_agt_exe_if[0]);
    uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("uvm_test_top.env.tok_agt[%0d][1]", VERIF_MVM_EXE_TOK_AGT), "vif", tok_agt_exe_if[1]);

    uvm_config_db#(virtual cc_clk_div_agent_if)::set(null, $sformatf("uvm_test_top.env.clk_div_agt"), "vif", clk_div_agt_if);

    uvm_config_db#(virtual mvm_utils_filter_intf)::set(uvm_root::get(), "uvm_test_top", "mvm_utils_filter_intf", mvm_utils_intf);
    uvm_config_db#(virtual mvm_if)::set(uvm_root::get(), "*", "mvm_if", mvm_if);
    uvm_config_db#(virtual mvm_power_surge_check_intf)::set(uvm_root::get(), "uvm_test_top", "mvm_power_surge_check_intf",mvm_power_surge_intf);

    //Omega issue : #2430 & #2867
    //Europa issue :#1236
    //diabling assertion (#2430 / #2867) as it is not yet fixed by Designer
    $assertoff(0, hdl_top.dut.i_mvm_dp.inst_mvm_imc_acc.imc_banks_ramp_assertion);

  end

  // Connections to MVM Utils Filter Predictor inside the mvm_utils_intf
  assign mvm_util_limit_value_i        = mvm_utils_intf.mvm_util_limit_value_i;
  assign mvm_util_limit_enable_i       = mvm_utils_intf.mvm_util_limit_enable_i;
  assign mvm_util_average_nominator_i  = mvm_utils_intf.mvm_util_average_nominator_i;
  assign mvm_utils_intf.mvm_util_average_o = mvm_util_average_o;
  assign mvm_utils_intf.mvm_util_value_i = dut.i_mvm_dp.u_mvm_par2bser_util_ctrl.inst_exp_avg_util.util_value_i[8:0];
  assign mvm_utils_intf.mvm_util_valid_i = dut.i_mvm_dp.u_mvm_par2bser_util_ctrl.inst_exp_avg_util.util_valid_i;

  assign mvm_if.mvm_int_clk                    = dut.i_clk;
  assign mvm_if.imc_bist_busy                  = imc_bist_busy_o;
  assign mvm_if.imc_bist_done                  = imc_bist_done_o;
  assign mvm_if.imc_bist_pass                  = imc_bist_pass_o;
  assign mvm_if.aic_csr_hw2reg                 = aic_csr_hw2reg;
  assign mvm_if.aic_csr_reg2hw.imc_bist_status = loopback_aic_csr_reg2hw.imc_bist_status;

  // =============================================================================================================
  // Initialize all memories
  // =============================================================================================================
  initial begin
    // Input ports initializations
    mvm_inp_ports_init();

  end

  // Initializing all input masters
  task mvm_inp_ports_init;

    test_mode = 0;
    void'(std::randomize(cid_i));
    jtag_seli = 1'b0;
    jtag_sei = 1'b0;
    jtag_cei = 1'b0;
    jtag_uei = 1'b0;
    jtag_tdi = 1'b0;
    ai_core_mvm_exe_tok_prod_rdy=0;
    ai_core_mvm_exe_tok_cons_vld=0;
    ai_core_mvm_prg_tok_prod_rdy=0;
    ai_core_mvm_prg_tok_cons_vld=0;
  endtask:mvm_inp_ports_init

  // Run test
  initial begin
    run_test();
  end

  always @(posedge mvm_utils_intf.disable_assertion_for_irq)
  begin
    case (mvm_utils_intf.assrt_ctrl)
      3'b000: $assertoff(0, hdl_top.dut.i_mvm_dp);
      3'b010: $assertoff(0, hdl_top.dut.u_mvm_exe_cmd_shim);
      3'b011: $assertoff(0, hdl_top.dut.i_mvm_prg_cmd_gen);
      default : `uvm_fatal("IRQ_test", "none of the irq test is running and still disable_assertion_for_irq got asserted ")
    endcase
  end

  initial begin
    if(!$test$plusargs("POWER_SMOOTH")) begin
      $assertoff(0, hdl_top.mvm_power_surge_intf.UNEXPETED_POWER_SURGE_CHECK);
      $assertoff(0, hdl_top.mvm_power_surge_intf.POWER_SURGE_CHECK_BY_GATE_CLOCK);
      $assertoff(0, hdl_top.mvm_power_surge_intf.POWER_SURGE_CHECK_BY_BLOCK_ENABLE);
    end
  end
endmodule : hdl_top
