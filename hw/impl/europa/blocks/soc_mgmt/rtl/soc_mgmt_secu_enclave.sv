// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: kevin Luciani <kevin.luciani@axelera.ai>
//
/// Description: Top module for the SoC Management Security enclave.
///

module soc_mgmt_secu_enclave
  import soc_mgmt_pkg::*;
  import rot_pkg::*;
#(
  parameter type rom_impl_inp_t = axe_tcl_sram_pkg::impl_inp_rom_t,
  parameter type rom_impl_oup_t = axe_tcl_sram_pkg::impl_oup_rom_t,
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
) (
  /// Default clock, connected to 100MHz periph_clk
  input  wire                                 i_clk,
  input  wire                                 i_rst_n,
  /// OTP wrapper clock, connected to 50MHz ref_clk.
  input  wire                                 i_otp_wrapper_clk,
  /// Always-on reset from POR, synchronized to ref_clk.
  input  wire                                 i_otp_wrapper_rst_n,
  /// Always-on registers reset, synchronized to periph_clk.
  input  wire                                 i_ao_rst_n, // TODO(kluciani, review that the provided resets are synchronised with the i_clk.)
  /// JTAG clock
  input  logic                                tcki,
  /// JTAG reset
  input  logic                                trsti,
  /// KSE3 JTAG warm reset request
  output wire                                 o_kse3_jtag_rst_n,
  ///////////////////////////////////////
  // AHB subordinate interface (KSE-3) //
  ///////////////////////////////////////
  output kudelski_kse3_pkg::kse3_ahb_hdata_t  o_ahb_s_hrdata,
  output logic                                o_ahb_s_hready,
  output logic                                o_ahb_s_hresp,
  input  kudelski_kse3_pkg::kse3_ahb_haddr_t  i_ahb_s_haddr,
  input  axe_ahb_pkg::hburst_e                i_ahb_s_hburst,
  input  axe_ahb_pkg::hsize_e                 i_ahb_s_hsize,
  input  axe_ahb_pkg::htrans_e                i_ahb_s_htrans,
  input  kudelski_kse3_pkg::kse3_ahb_hdata_t  i_ahb_s_hwdata,
  input  logic                                i_ahb_s_hwrite,
  //////////////////////////////////////////////////
  // APB subordinate interface (OTP and AOR regs) //
  //////////////////////////////////////////////////
  input  soc_mgmt_secu_encl_paddr_t           i_apb_s_paddr,
  input  logic                                i_apb_s_pwrite,
  input  soc_mgmt_secu_encl_pdata_t           i_apb_s_pwdata,
  input  logic                                i_apb_s_psel,
  input  soc_mgmt_pprot_t                     i_apb_s_pprot,
  input  logic                                i_apb_s_penable,
  input  soc_mgmt_secu_encl_pstrb_t           i_apb_s_pstrb,
  output logic                                o_apb_s_pslverr,
  output soc_mgmt_secu_encl_pdata_t           o_apb_s_prdata,
  output logic                                o_apb_s_pready,
  ///////////////////
  // OTP DFT ports //
  ///////////////////
  input logic                                 i_dft_scan_test_mode,
  input logic                                 i_dft_otp_test_mode,
  input otp_wrapper_pkg::otp_addr_t           i_dft_otp_tst_a,
  input logic                                 i_dft_otp_tst_din,
  input logic                                 i_dft_otp_tst_readen,
  input logic                                 i_dft_otp_tst_ceb,
  input logic                                 i_dft_otp_tst_cle,
  input logic                                 i_dft_otp_tst_dle,
  input logic                                 i_dft_otp_tst_web,
  input logic                                 i_dft_otp_tst_rstb,
  input logic                                 i_dft_otp_tst_cpumpen,
  input logic                                 i_dft_otp_tst_pgmen,
  input logic                                 i_dft_otp_tst_seltm,
  input logic                                 i_dft_otp_tst_vddrdy,
  input logic                                 i_dft_otp_tst_clken,
  output otp_wrapper_pkg::otp_data_t          o_dft_otp_tst_d,
  output otp_wrapper_pkg::otp_lock_t          o_dft_otp_tst_lock,
  /// KSE3 interrupt
  output logic                                o_kse3_interrupt,
  /// Debug TAPs enable signals
  output dbg_taps_en_t                        o_dbg_taps_en,
  /// OTP TAP enable signal
  output logic                                o_otp_tap_en,
  /////////////////////
  // OTP power ports //
  /////////////////////
  inout  wire                                 io_otp_vtdo,
  inout  wire                                 io_otp_vrefm,
  inout  wire                                 io_otp_vpp,
  /// Implementation specific memory sideband inputs
  input  ram_impl_inp_t                       i_impl_inp,
  /// Implementation specific memory sideband outputs
  output ram_impl_oup_t                       o_impl_oup
);

// ----------------------------------------------------------------------------
// Parameters
// ----------------------------------------------------------------------------
localparam int unsigned KSE_MEM_N = 3;
localparam              ImplKey = "HS_RVT";
// TODO(kluciani, Review required number of synchronizer stages.)
localparam int unsigned SYNC_STAGE_NUM = 3;
localparam int unsigned LOG2_OTP_CLK_DIV = 4;
// localparams from KSE-3 package
localparam int unsigned KSE3_AOR_ADDR_W = kudelski_kse3_pkg::KSE3_AOR_ADDR_W;
localparam int unsigned KSE3_OTP_ADDR_W = kudelski_kse3_pkg::KSE3_OTP_ADDR_W;
localparam int unsigned KSE3_APB_ADDR_W = kudelski_kse3_pkg::KSE3_APB_ADDR_W;
localparam logic[KSE3_APB_ADDR_W-1:0] KSE3_AOR_START_ADDR = kudelski_kse3_pkg::KSE3_AOR_START_ADDR;

// ----------------------------------------------------------------------------
// Signal declaration
// ----------------------------------------------------------------------------
kudelski_kse3_pkg::kse3_dram_addr_t   mem_addr;
logic                                 mem_me;
logic                                 mem_gwe;
kudelski_kse3_pkg::kse3_dram_data_t   mem_we;
kudelski_kse3_pkg::kse3_dram_data_t   mem_wdata;
kudelski_kse3_pkg::kse3_dram_data_t   mem_rdata;
kudelski_kse3_pkg::kse3_rom_addr_t    rom_addr;
logic                                 rom_me;
kudelski_kse3_pkg::kse3_rom_data_t    rom_rdata;
kudelski_kse3_pkg::kse3_iram_addr_t   iram_addr;
logic                                 iram_me;
logic                                 iram_we;
kudelski_kse3_pkg::kse3_iram_data_t   iram_wem;
kudelski_kse3_pkg::kse3_iram_data_t   iram_wdata;
kudelski_kse3_pkg::kse3_iram_data_t   iram_rdata;

kudelski_kse3_pkg::kse3_apb_paddr_t   kse3_apb_paddr;
logic                                 kse3_apb_psel;
logic                                 kse3_apb_penable;
logic                                 kse3_apb_pwrite;
kudelski_kse3_pkg::kse3_apb_pdata_t   kse3_apb_pwdata;
kudelski_kse3_pkg::kse3_apb_pdata_t   kse3_apb_prdata;
logic                                 kse3_apb_pready;
logic                                 kse3_apb_pslverr;

kudelski_kse3_pkg::kse3_apb_paddr_t   kse_apb32_paddr;

soc_mgmt_secu_encl_paddr_t            kse_host_apb_mux_in_paddr   [SECU_ENCL_MUX_NB_APBIN];
logic                                 kse_host_apb_mux_in_psel    [SECU_ENCL_MUX_NB_APBIN];
logic                                 kse_host_apb_mux_in_penable [SECU_ENCL_MUX_NB_APBIN];
logic                                 kse_host_apb_mux_in_pwrite  [SECU_ENCL_MUX_NB_APBIN];
soc_mgmt_secu_encl_pdata_t            kse_host_apb_mux_in_pwdata  [SECU_ENCL_MUX_NB_APBIN];
soc_mgmt_secu_encl_pdata_t            kse_host_apb_mux_in_prdata  [SECU_ENCL_MUX_NB_APBIN];
soc_mgmt_secu_encl_pstrb_t            kse_host_apb_mux_in_pstrb   [SECU_ENCL_MUX_NB_APBIN];
axe_apb_pkg::apb_prot_t               kse_host_apb_mux_in_pprot   [SECU_ENCL_MUX_NB_APBIN];
logic                                 kse_host_apb_mux_in_pready  [SECU_ENCL_MUX_NB_APBIN];
logic                                 kse_host_apb_mux_in_pslverr [SECU_ENCL_MUX_NB_APBIN];
logic                                 kse_apb_addr_is_aor;

soc_mgmt_secu_encl_paddr_t            kse_host_apb_mux_out_paddr;
logic                                 kse_host_apb_mux_out_psel;
logic                                 kse_host_apb_mux_out_penable;
logic                                 kse_host_apb_mux_out_pwrite;
soc_mgmt_secu_encl_pdata_t            kse_host_apb_mux_out_pwdata;
soc_mgmt_secu_encl_pdata_t            kse_host_apb_mux_out_prdata;
soc_mgmt_secu_encl_pstrb_t            kse_host_apb_mux_out_pstrb;
axe_apb_pkg::apb_prot_t               kse_host_apb_mux_out_pprot;
logic                                 kse_host_apb_mux_out_pready;
logic                                 kse_host_apb_mux_out_pslverr;

soc_mgmt_secu_encl_paddr_t            apb_demux_out_paddr          [SECU_ENCL_DEMUX_NB_APBOUT];
logic                                 apb_demux_out_psel           [SECU_ENCL_DEMUX_NB_APBOUT];
logic                                 apb_demux_out_penable        [SECU_ENCL_DEMUX_NB_APBOUT];
logic                                 apb_demux_out_pwrite         [SECU_ENCL_DEMUX_NB_APBOUT];
soc_mgmt_secu_encl_pdata_t            apb_demux_out_pwdata         [SECU_ENCL_DEMUX_NB_APBOUT];
soc_mgmt_secu_encl_pdata_t            apb_demux_out_prdata         [SECU_ENCL_DEMUX_NB_APBOUT];
soc_mgmt_secu_encl_pstrb_t            apb_demux_out_pstrb          [SECU_ENCL_DEMUX_NB_APBOUT];
axe_apb_pkg::apb_prot_t               apb_demux_out_pprot          [SECU_ENCL_DEMUX_NB_APBOUT];
logic                                 apb_demux_out_pready         [SECU_ENCL_DEMUX_NB_APBOUT];
logic                                 apb_demux_out_pslverr        [SECU_ENCL_DEMUX_NB_APBOUT];

ram_impl_inp_t [KSE_MEM_N-1:0]        ram_impl_in;
ram_impl_oup_t [KSE_MEM_N-1:0]        ram_impl_out;
rom_impl_inp_t                        rom_impl_in;
rom_impl_oup_t                        rom_impl_out;

logic                                 lcs_valid;
logic                                 lcs_valid_sync;
logic                                 lcs_is_chip_wafer_test;
logic                                 lcs_is_chip_perso;
logic                                 lcs_is_user_delivery;
logic                                 lcs_is_user_secured;
logic                                 lcs_is_user_decommissioned;
logic                                 lcs_is_chip_field_return;
logic                                 lcs_is_terminated;

// OTP Wrapper APB interface
otp_wrapper_csr_reg_pkg::apb_h2d_t otp_csr_apb_s_h2d;
otp_wrapper_csr_reg_pkg::apb_d2h_t otp_csr_apb_s_d2h;
// AOR APB interface
soc_mgmt_secu_aor_csr_reg_pkg::apb_h2d_t secu_aor_apb_s_h2d;
soc_mgmt_secu_aor_csr_reg_pkg::apb_d2h_t secu_aor_apb_s_d2h;
// AOR output signals
soc_mgmt_secu_aor_csr_reg_pkg::soc_mgmt_secu_aor_csr_reg2hw_t secu_aor_reg2hw;
soc_mgmt_secu_aor_csr_reg_pkg::soc_mgmt_secu_aor_csr_hw2reg_t secu_aor_hw2reg;
// APB MUX index
secu_encl_apb_mux_idx_t apb_manager_idx;
// APB DEMUX index
secu_encl_apb_demux_idx_t apb_subordinate_idx;

logic                                 ro_en;
kudelski_kse3_pkg::kse_ro_clk_t       ro_clk;
wire                                  otp_wrapper_analog_clk;
logic [LOG2_OTP_CLK_DIV-1:0]          otp_clk_div_cnt_q;

kse3_jtag_req_t                       kse3_jtag_req;
kse3_jtag_resp_t                      kse3_jtag_resp;
logic                                 tdr_valid;
logic                                 tdr_ready;
logic                                 tdr_jtag_dbg;
logic                                 tdr_jtag_dbg_sync;
logic                                 tdr_jtag_dbg_sync_q;
wire                                  kse3_jtag_rst;

soc_mgmt_haddr_t                      ahb_demux_in_haddr;
logic                                 ahb_demux_in_hwrite;
soc_mgmt_hdata_t                      ahb_demux_in_hwdata;
axe_ahb_pkg::htrans_e                 ahb_demux_in_htrans;
axe_ahb_pkg::hburst_e                 ahb_demux_in_hburst;
axe_ahb_pkg::hsize_e                  ahb_demux_in_hsize;
soc_mgmt_hdata_t                      ahb_demux_in_hrdata;
logic                                 ahb_demux_in_hready;
logic                                 ahb_demux_in_hresp;
secu_encl_ahb_demux_idx_t             ahb_demux_in_select;

soc_mgmt_haddr_t                      ahb_demux_out_haddr[SECU_ENCL_DEMUX_NB_AHBOUT];
logic                                 ahb_demux_out_hwrite[SECU_ENCL_DEMUX_NB_AHBOUT];
soc_mgmt_hdata_t                      ahb_demux_out_hwdata[SECU_ENCL_DEMUX_NB_AHBOUT];
axe_ahb_pkg::htrans_e                 ahb_demux_out_htrans[SECU_ENCL_DEMUX_NB_AHBOUT];
axe_ahb_pkg::hburst_e                 ahb_demux_out_hburst[SECU_ENCL_DEMUX_NB_AHBOUT];
axe_ahb_pkg::hsize_e                  ahb_demux_out_hsize[SECU_ENCL_DEMUX_NB_AHBOUT];
soc_mgmt_hdata_t                      ahb_demux_out_hrdata[SECU_ENCL_DEMUX_NB_AHBOUT];
logic                                 ahb_demux_out_hready[SECU_ENCL_DEMUX_NB_AHBOUT];
logic                                 ahb_demux_out_hresp[SECU_ENCL_DEMUX_NB_AHBOUT];
logic                                 ahb_demux_out_hsel[SECU_ENCL_DEMUX_NB_AHBOUT];

soc_mgmt_haddr_t                      ahb_mux_in_haddr[SECU_ENCL_MUX_NB_AHBIN];
logic                                 ahb_mux_in_hwrite[SECU_ENCL_MUX_NB_AHBIN];
kudelski_kse3_pkg::kse3_ahb_hdata_t   ahb_mux_in_hwdata[SECU_ENCL_MUX_NB_AHBIN];
axe_ahb_pkg::htrans_e                 ahb_mux_in_htrans[SECU_ENCL_MUX_NB_AHBIN];
axe_ahb_pkg::hburst_e                 ahb_mux_in_hburst[SECU_ENCL_MUX_NB_AHBIN];
axe_ahb_pkg::hsize_e                  ahb_mux_in_hsize[SECU_ENCL_MUX_NB_AHBIN];
kudelski_kse3_pkg::kse3_ahb_hdata_t   ahb_mux_in_hrdata[SECU_ENCL_MUX_NB_AHBIN];
logic                                 ahb_mux_in_hready[SECU_ENCL_MUX_NB_AHBIN];
logic                                 ahb_mux_in_hresp[SECU_ENCL_MUX_NB_AHBIN];

soc_mgmt_haddr_t                      ahb_mux_out_haddr;
logic                                 ahb_mux_out_hwrite;
kudelski_kse3_pkg::kse3_ahb_hdata_t   ahb_mux_out_hwdata;
axe_ahb_pkg::htrans_e                 ahb_mux_out_htrans;
axe_ahb_pkg::hburst_e                 ahb_mux_out_hburst;
axe_ahb_pkg::hsize_e                  ahb_mux_out_hsize;
kudelski_kse3_pkg::kse3_ahb_hdata_t   ahb_mux_out_hrdata;
logic                                 ahb_mux_out_hready;
logic                                 ahb_mux_out_hresp;

// ----------------------------------------------------------------------------
// RTL
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// KSE3 TAP Test Data Registers (TDR)
// ----------------------------------------------------------------------------

kse_jtag_tdr #(
  .SyncStages (SYNC_STAGE_NUM)
)
u_kse_jtag_tdr (
  .i_clk                (i_clk),
  .i_ao_rst_n           (i_ao_rst_n),
  // JTAG
  .tcki                 (tcki),
  .trsti                (trsti),
  // TDR_JTAG_DBG
  .o_tdr_jtag_dbg       (tdr_jtag_dbg),
  // TDR interface
  .o_kse3_jtag_req      (kse3_jtag_req),
  .i_kse3_jtag_resp     (kse3_jtag_resp),
  .o_tdr_valid          (tdr_valid),
  .i_tdr_ready          (tdr_ready)
);

axe_tcl_seq_sync #(
  .SyncStages (SYNC_STAGE_NUM),
  .ResetValue (1'b0)
) u_tdr_jtag_dbg_sync (
  .i_clk   (i_clk),
  .i_rst_n (i_ao_rst_n),
  .i_d     (tdr_jtag_dbg),
  .o_q     (tdr_jtag_dbg_sync)
);

always_ff @(posedge i_clk or negedge i_ao_rst_n) begin
  if (!i_ao_rst_n) tdr_jtag_dbg_sync_q <= 1'b0;
  else             tdr_jtag_dbg_sync_q <= tdr_jtag_dbg_sync;
end

assign kse3_jtag_rst     = tdr_jtag_dbg_sync_q ^ tdr_jtag_dbg_sync;
assign o_kse3_jtag_rst_n = ~kse3_jtag_rst;

// ----------------------------------------------------------------------------
// KSE3 JTAG command FSM
// ----------------------------------------------------------------------------

kse_jtag_fsm u_kse_jtag_fsm (
  .i_clk                      (i_clk),
  .i_rst_n                    (i_rst_n),
  .i_kse3_jtag_req            (kse3_jtag_req),
  .o_kse3_jtag_resp           (kse3_jtag_resp),
  .i_tdr_valid                (tdr_valid),
  .o_tdr_ready                (tdr_ready),
  .i_tdr_jtag_dbg             (tdr_jtag_dbg_sync),
  .i_lcs_valid                (lcs_valid),
  .i_lcs_is_terminated        (lcs_is_terminated),
  .i_lcs_is_chip_wafer_test   (lcs_is_chip_wafer_test),
  .i_lcs_is_chip_perso        (lcs_is_chip_perso),
  .i_lcs_is_chip_field_return (lcs_is_chip_field_return),
  .o_ahb_m_haddr              (ahb_demux_in_haddr),
  .o_ahb_m_hwrite             (ahb_demux_in_hwrite),
  .o_ahb_m_hwdata             (ahb_demux_in_hwdata),
  .o_ahb_m_htrans             (ahb_demux_in_htrans),
  .o_ahb_m_hburst             (ahb_demux_in_hburst),
  .o_ahb_m_hsize              (ahb_demux_in_hsize),
  .i_ahb_m_hrdata             (ahb_demux_in_hrdata),
  .i_ahb_m_hready             (ahb_demux_in_hready),
  .i_ahb_m_hresp              (ahb_demux_in_hresp)
);

// ----------------------------------------------------------------------------
// AHB interconnect
// ----------------------------------------------------------------------------
//
// Used to connect 2 manager ports (KSE3 JTAG and APU) to 2 subordinate ports
// (KSE3 and OTP/AOR).
//
// 1. AHB demux:
//   - Manager: KSE3_JTAG
//   - Subordinates: KSE3 and OTP/AON
//
axe_ahb_demux # (
  .NB_AHBOUT(SECU_ENCL_DEMUX_NB_AHBOUT),
  .IDXW     (SECU_ENCL_DEMUX_IDXW),
  .HAW      (SOC_MGMT_HAW),
  .HDW      (SOC_MGMT_HDW)
)
u_axe_ahb_demux (
  .i_clk          (i_clk),
  .i_rst_n        (i_rst_n),
  .i_ahb_s_haddr  (ahb_demux_in_haddr),
  .i_ahb_s_hwrite (ahb_demux_in_hwrite),
  .i_ahb_s_hwdata (ahb_demux_in_hwdata),
  .i_ahb_s_htrans (ahb_demux_in_htrans),
  .i_ahb_s_hburst (ahb_demux_in_hburst),
  .i_ahb_s_hsize  (ahb_demux_in_hsize),
  .o_ahb_s_hrdata (ahb_demux_in_hrdata),
  .o_ahb_s_hready (ahb_demux_in_hready),
  .o_ahb_s_hresp  (ahb_demux_in_hresp),
  .i_ahb_s_select (ahb_demux_in_select),
  .o_ahb_m_haddr  (ahb_demux_out_haddr),
  .o_ahb_m_hwrite (ahb_demux_out_hwrite),
  .o_ahb_m_hwdata (ahb_demux_out_hwdata),
  .o_ahb_m_htrans (ahb_demux_out_htrans),
  .o_ahb_m_hburst (ahb_demux_out_hburst),
  .o_ahb_m_hsize  (ahb_demux_out_hsize),
  .o_ahb_m_hsel   (ahb_demux_out_hsel),
  .i_ahb_m_hrdata (ahb_demux_out_hrdata),
  .i_ahb_m_hready (ahb_demux_out_hready),
  .i_ahb_m_hresp  (ahb_demux_out_hresp)
);

soc_mgmt_secu_ahb_dec  soc_mgmt_secu_ahb_dec_inst (
  .i_haddr    (ahb_demux_in_haddr),
  .o_sub_idx  (ahb_demux_in_select)
);

// Default AHB subordinate (Error response)
axe_ahb_error_sub # (
  .HAW    (SOC_MGMT_HAW),
  .HDW    (SOC_MGMT_HDW)
)
u_axe_ahb_error_sub (
  .i_clk            (i_clk),
  .i_rst_n          (i_rst_n),
  .i_ahb_s_htrans   (ahb_demux_out_htrans[SECU_ENCL_AHB_DEMUX_ERR_IDX]),
  .i_ahb_s_hsel     (ahb_demux_out_hsel[SECU_ENCL_AHB_DEMUX_ERR_IDX]),
  .i_ahb_s_hready   (ahb_demux_in_hready),
  .o_ahb_s_hreadyout(ahb_demux_out_hready[SECU_ENCL_AHB_DEMUX_ERR_IDX]),
  .o_ahb_s_hresp    (ahb_demux_out_hresp[SECU_ENCL_AHB_DEMUX_ERR_IDX])
);

always_comb begin
  // APU AHB MUX input connected to secure enclave ports.
  ahb_mux_in_haddr  [SECU_ENCL_AHB_MUX_APU_IDX]       = i_ahb_s_haddr;
  ahb_mux_in_hwrite [SECU_ENCL_AHB_MUX_APU_IDX]       = i_ahb_s_hwrite;
  ahb_mux_in_hwdata [SECU_ENCL_AHB_MUX_APU_IDX]       = i_ahb_s_hwdata;
  ahb_mux_in_htrans [SECU_ENCL_AHB_MUX_APU_IDX]       = i_ahb_s_htrans;
  ahb_mux_in_hburst [SECU_ENCL_AHB_MUX_APU_IDX]       = i_ahb_s_hburst;
  ahb_mux_in_hsize  [SECU_ENCL_AHB_MUX_APU_IDX]       = i_ahb_s_hsize;
  o_ahb_s_hrdata                                      = ahb_mux_in_hrdata [SECU_ENCL_AHB_MUX_APU_IDX];
  o_ahb_s_hready                                      = ahb_mux_in_hready [SECU_ENCL_AHB_MUX_APU_IDX];
  o_ahb_s_hresp                                       = ahb_mux_in_hresp  [SECU_ENCL_AHB_MUX_APU_IDX];
  // JTAG AHB MUX port connected to AHB DEMUX KSE3 AHB port.
  ahb_mux_in_haddr     [SECU_ENCL_AHB_MUX_JTAG_IDX]   = ahb_demux_out_haddr  [SECU_ENCL_AHB_DEMUX_KSE3_IDX];
  ahb_mux_in_hwrite    [SECU_ENCL_AHB_MUX_JTAG_IDX]   = ahb_demux_out_hwrite [SECU_ENCL_AHB_DEMUX_KSE3_IDX];
  ahb_mux_in_hwdata    [SECU_ENCL_AHB_MUX_JTAG_IDX]   = ahb_demux_out_hwdata [SECU_ENCL_AHB_DEMUX_KSE3_IDX];
  ahb_mux_in_htrans    [SECU_ENCL_AHB_MUX_JTAG_IDX]   = ahb_demux_out_htrans [SECU_ENCL_AHB_DEMUX_KSE3_IDX];
  ahb_mux_in_hburst    [SECU_ENCL_AHB_MUX_JTAG_IDX]   = ahb_demux_out_hburst [SECU_ENCL_AHB_DEMUX_KSE3_IDX];
  ahb_mux_in_hsize     [SECU_ENCL_AHB_MUX_JTAG_IDX]   = ahb_demux_out_hsize  [SECU_ENCL_AHB_DEMUX_KSE3_IDX];
  ahb_demux_out_hrdata [SECU_ENCL_AHB_DEMUX_KSE3_IDX] = ahb_mux_in_hrdata    [SECU_ENCL_AHB_MUX_JTAG_IDX];
  ahb_demux_out_hready [SECU_ENCL_AHB_DEMUX_KSE3_IDX] = ahb_mux_in_hready    [SECU_ENCL_AHB_MUX_JTAG_IDX];
  ahb_demux_out_hresp  [SECU_ENCL_AHB_DEMUX_KSE3_IDX] = ahb_mux_in_hresp     [SECU_ENCL_AHB_MUX_JTAG_IDX];
  // Default subordinate read data is set to 0.
  ahb_demux_out_hrdata[SECU_ENCL_AHB_DEMUX_ERR_IDX]   = '0;
end

//
// 2. AHB MUX between KSE3_JTAG, APU
//
axe_ahb_mux # (
  .NB_AHBIN (SECU_ENCL_MUX_NB_AHBIN),
  .HAW      (SOC_MGMT_HAW),
  .HDW      (SOC_MGMT_HDW)
)
axe_ahb_mux_inst (
  .i_clk          (i_clk),
  .i_rst_n        (i_rst_n),
  .i_ahb_s_haddr  (ahb_mux_in_haddr),
  .i_ahb_s_hwrite (ahb_mux_in_hwrite),
  .i_ahb_s_hwdata (ahb_mux_in_hwdata),
  .i_ahb_s_htrans (ahb_mux_in_htrans),
  .i_ahb_s_hburst (ahb_mux_in_hburst),
  .i_ahb_s_hsize  (ahb_mux_in_hsize),
  .o_ahb_s_hrdata (ahb_mux_in_hrdata),
  .o_ahb_s_hready (ahb_mux_in_hready),
  .o_ahb_s_hresp  (ahb_mux_in_hresp),
  .o_ahb_m_haddr  (ahb_mux_out_haddr),
  .o_ahb_m_hwrite (ahb_mux_out_hwrite),
  .o_ahb_m_hwdata (ahb_mux_out_hwdata),
  .o_ahb_m_htrans (ahb_mux_out_htrans),
  .o_ahb_m_hburst (ahb_mux_out_hburst),
  .o_ahb_m_hsize  (ahb_mux_out_hsize),
  .i_ahb_m_hrdata (ahb_mux_out_hrdata),
  .i_ahb_m_hready (ahb_mux_out_hready),
  .i_ahb_m_hresp  (ahb_mux_out_hresp)
);

//
// 3. AHB to APB to OTP/AON subordinates
//
axe_ahb_to_apb # (
  .AW     (SOC_MGMT_HAW),
  .DW     (SOC_MGMT_HDW),
  .PSTRBW (SECU_ENCL_PSTRBW)
)
axe_ahb_to_apb_inst (
  .i_clk            (i_clk),
  .i_rst_n          (i_rst_n),
  .i_ahb_s_haddr    (ahb_demux_out_haddr[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .i_ahb_s_hwrite   (ahb_demux_out_hwrite[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .i_ahb_s_hwdata   (ahb_demux_out_hwdata[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .i_ahb_s_htrans   (ahb_demux_out_htrans[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .i_ahb_s_hburst   (ahb_demux_out_hburst[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .i_ahb_s_hsize    (ahb_demux_out_hsize[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .o_ahb_s_hrdata   (ahb_demux_out_hrdata[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .o_ahb_s_hready   (ahb_demux_out_hready[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .o_ahb_s_hresp    (ahb_demux_out_hresp[SECU_ENCL_AHB_DEMUX_OTP_AON_IDX]),
  .o_apb_m_paddr    (kse_host_apb_mux_in_paddr[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .o_apb_m_pwdata   (kse_host_apb_mux_in_pwdata[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .o_apb_m_pwrite   (kse_host_apb_mux_in_pwrite[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .o_apb_m_psel     (kse_host_apb_mux_in_psel[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .o_apb_m_penable  (kse_host_apb_mux_in_penable[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .o_apb_m_pstrb    (kse_host_apb_mux_in_pstrb[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .o_apb_m_pprot    (kse_host_apb_mux_in_pprot[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .i_apb_m_pready   (kse_host_apb_mux_in_pready[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .i_apb_m_prdata   (kse_host_apb_mux_in_prdata[SECU_ENCL_APB_MUX_JTAG_IDX]),
  .i_apb_m_pslverr  (kse_host_apb_mux_in_pslverr[SECU_ENCL_APB_MUX_JTAG_IDX])
);

// ----------------------------------------------------------------------------
// KSE-3 instance
// ----------------------------------------------------------------------------
kudelski_kse3_top u_kudelski_kse3_top (
  .i_clk                   (i_clk),
  .i_rst_n                 (i_rst_n),
  .i_ahb_s_haddr           (ahb_mux_out_haddr[kudelski_kse3_pkg::KSE3_AHB_ADDR_W-1:0]),
  .i_ahb_s_hsel            (1'b1),                // KSE-3 is the only AHB subordinate addressed by AHB MUX
  .i_ahb_s_hready          (ahb_mux_out_hready),  // KSE-3 is the only AHB subordinate addressed by AHB MUX
  .i_ahb_s_hwrite          (ahb_mux_out_hwrite),
  .i_ahb_s_htrans          (ahb_mux_out_htrans),
  .i_ahb_s_hburst          (ahb_mux_out_hburst),
  .i_ahb_s_hsize           (ahb_mux_out_hsize),
  .i_ahb_s_hwdata          (ahb_mux_out_hwdata),
  .o_ahb_s_hrdata          (ahb_mux_out_hrdata),
  .o_ahb_s_hreadyout       (ahb_mux_out_hready),
  .o_ahb_s_hresp           (ahb_mux_out_hresp),
  .o_apb_m_paddr           (kse3_apb_paddr),
  .o_apb_m_psel            (kse3_apb_psel),
  .o_apb_m_penable         (kse3_apb_penable),
  .o_apb_m_pwrite          (kse3_apb_pwrite),
  .o_apb_m_pwdata          (kse3_apb_pwdata),
  .i_apb_m_prdata          (kse3_apb_prdata),
  .i_apb_m_pready          (kse3_apb_pready),
  .i_apb_m_pslverr         (kse3_apb_pslverr),
  .i_config                (8'h50),
  .o_interrupt             (o_kse3_interrupt),
  .o_mem_addr              (mem_addr),
  .o_mem_me                (mem_me),
  .o_mem_gwe               (mem_gwe),
  .o_mem_we                (mem_we),
  .o_mem_wdata             (mem_wdata),
  .i_mem_rdata             (mem_rdata),
  .o_rom_addr              (rom_addr),
  .o_rom_me                (rom_me),
  .i_rom_rdata             (rom_rdata),
  .o_iram_addr             (iram_addr),
  .o_iram_me               (iram_me),
  .o_iram_we               (iram_we),
  .o_iram_wem              (iram_wem),
  .o_iram_wdata            (iram_wdata),
  .i_iram_rdata            (iram_rdata),
  .o_ro_en                 (ro_en),
  .i_ro_clk                (ro_clk),
  .i_kb_ack                ('0),
  .o_kb_sel                (/*UNUSED*/),
  .o_kb_addr               (/*UNUSED*/),
  .o_kb_data               (/*UNUSED*/)
);

//
// DBG TAPs are forced open   when LCS == Chip Wafer Test or Chip Field Return or Chip Perso.
// DBG TAPs are forced closed when LCS == Terminated.
// DBG TAPs are controlled by KSE3 AOR (Soc Config) otherwise.
// Keep the TAPs closed until OTP wrapper reads the LCS value.
//
always_comb begin
  if (!lcs_valid_sync)
    o_dbg_taps_en = '0;
  else if (lcs_is_terminated)
    o_dbg_taps_en = '0;
  else if (lcs_is_chip_wafer_test || lcs_is_chip_perso || lcs_is_chip_field_return)
    o_dbg_taps_en = '1;
  else
    // soc_config0 bit 0 has different meaning than other bits and is unused in Europa.
    o_dbg_taps_en = {secu_aor_reg2hw.soc_config1, secu_aor_reg2hw.soc_config0[7:1]};
end
//
// OTP TAP is forced open when LCS == Chip Wafer Test or Chip Field Return. Closed otherwise.
// Keep the TAP closed until OTP wrapper reads the LCS value.
//
always_comb begin
  if (!lcs_valid_sync)                                         o_otp_tap_en  = 1'b0;
  else if (lcs_is_chip_wafer_test || lcs_is_chip_field_return) o_otp_tap_en  = 1'b1;
  else                                                         o_otp_tap_en  = 1'b0;
end

axe_tcl_sram_cfg #(
    .NUM_SRAMS(KSE_MEM_N)
) u_kudelski_kse3_mem_cfg_impl (
    .i_s(i_impl_inp),
    .o_s(o_impl_oup),
    .o_m(ram_impl_in),
    .i_m(ram_impl_out)
);

// ----------------------------------------------------------------------------
// KSE-3 ROM
// ----------------------------------------------------------------------------
axe_tcl_rom_1p #(
  .NumWords     (kudelski_kse3_pkg::KSE3_ROM_WORDS),
  .DataWidth    (kudelski_kse3_pkg::KSE3_ROM_DATA_W),
  .ImplKey      (ImplKey),
  .ReadLatency  (1)
) u_kudelski_kse3_rom (
  .i_clk      (i_clk),
  .i_rst_n    (i_rst_n),
  .i_req      (rom_me),
  .i_addr     (rom_addr),
  .o_rd_data  (rom_rdata),
  .i_impl     (rom_impl_in),
  .o_impl     (rom_impl_out)
);

// ROM and RAM memories are connected to the same power-down chain.
always_comb begin
  rom_impl_in.pde   = ram_impl_in[0].pde;
  rom_impl_in.se    = ram_impl_in[0].se;
  ram_impl_out[0]   = rom_impl_out;
end

// ----------------------------------------------------------------------------
// KSE-3 DRAM
// ----------------------------------------------------------------------------
axe_tcl_ram_1rwp #(
  .NumWords    (kudelski_kse3_pkg::KSE3_DRAM_WORDS),
  .DataWidth   (kudelski_kse3_pkg::KSE3_DRAM_DATA_W),
  .ByteWidth   (1),
  .ReadLatency (1),
  .ImplKey     (ImplKey)
) u_kudelski_kse3_dram (
  .i_clk       (i_clk),
  .i_rst_n     (i_rst_n),
  .i_req       (mem_me),
  .i_addr      (mem_addr),
  .i_wr_enable (mem_gwe),
  .i_wr_data   (mem_wdata),
  .i_wr_mask   (mem_we),
  .o_rd_data   (mem_rdata),
  .i_impl      (ram_impl_in[1]),
  .o_impl      (ram_impl_out[1])
);

// ----------------------------------------------------------------------------
// KSE-3 IRAM
// ----------------------------------------------------------------------------
axe_tcl_ram_1rwp #(
  .NumWords    (kudelski_kse3_pkg::KSE3_IRAM_WORDS),
  .DataWidth   (kudelski_kse3_pkg::KSE3_IRAM_DATA_W),
  .ByteWidth   (1),
  .ReadLatency (1),
  .ImplKey     (ImplKey)
) u_kudelski_kse3_iram (
  .i_clk       (i_clk),
  .i_rst_n     (i_rst_n),
  .i_req       (iram_me),
  .i_addr      (iram_addr),
  .i_wr_enable (iram_we),
  .i_wr_data   (iram_wdata),
  .i_wr_mask   (iram_wem),
  .o_rd_data   (iram_rdata),
  .i_impl      (ram_impl_in[2]),
  .o_impl      (ram_impl_out[2])
);

// ----------------------------------------------------------------------------
// KSE-3 Ring oscillators
// ----------------------------------------------------------------------------
kudelski_ring_osc #(
  .N_BITS   (kudelski_kse3_pkg::KSE3_RO_CLK_W)
) u_ring_osc (
  .i_en     (ro_en),
  .o_ro_clk (ro_clk)
);

// Convert KSE-3 8-bit APB to 32-bit APB data width
// Bypass conversion for AOR addresses, since they are word-aligned in secure enclave
// (and byte-aligned for the KSE3), hence a left-shift of the address by 2 is enough.
axe_apb_8to32 #(
  .PAW  (kudelski_kse3_pkg::KSE3_APB_ADDR_W)
) u_kse3_apb_8to32 (
  .i_clk                 (i_clk),
  .i_rst_n               (i_rst_n),
  .i_bypass              (kse_apb_addr_is_aor),
  .i_apb_s_paddr         (kse3_apb_paddr),
  .i_apb_s_pwdata        (kse3_apb_pwdata),
  .i_apb_s_pwrite        (kse3_apb_pwrite),
  .i_apb_s_psel          (kse3_apb_psel),
  .i_apb_s_penable       (kse3_apb_penable),
  .i_apb_s_pprot         (PPROT_VAL),
  .o_apb_s_pready        (kse3_apb_pready),
  .o_apb_s_prdata        (kse3_apb_prdata),
  .o_apb_s_pslverr       (kse3_apb_pslverr),
  .o_apb_m_paddr         (kse_apb32_paddr),
  .o_apb_m_pwdata        (kse_host_apb_mux_in_pwdata[SECU_ENCL_APB_MUX_KSE_IDX]),
  .o_apb_m_pwrite        (kse_host_apb_mux_in_pwrite[SECU_ENCL_APB_MUX_KSE_IDX]),
  .o_apb_m_psel          (kse_host_apb_mux_in_psel[SECU_ENCL_APB_MUX_KSE_IDX]),
  .o_apb_m_penable       (kse_host_apb_mux_in_penable[SECU_ENCL_APB_MUX_KSE_IDX]),
  .o_apb_m_pstrb         (kse_host_apb_mux_in_pstrb[SECU_ENCL_APB_MUX_KSE_IDX]),
  .o_apb_m_pprot         (kse_host_apb_mux_in_pprot[SECU_ENCL_APB_MUX_KSE_IDX]),
  .i_apb_m_pready        (kse_host_apb_mux_in_pready[SECU_ENCL_APB_MUX_KSE_IDX]),
  .i_apb_m_prdata        (kse_host_apb_mux_in_prdata[SECU_ENCL_APB_MUX_KSE_IDX]),
  .i_apb_m_pslverr       (kse_host_apb_mux_in_pslverr[SECU_ENCL_APB_MUX_KSE_IDX])
);

always_comb kse_apb_addr_is_aor = kse3_apb_paddr[KSE3_APB_ADDR_W-1:KSE3_AOR_ADDR_W] == KSE3_AOR_START_ADDR[KSE3_APB_ADDR_W-1:KSE3_AOR_ADDR_W];

// Convert KSE-3 address to SoC memory map address
//
// KSE-3 OTP address: 9'h000 to 9'h0FF
// KSE-3 AOR address: 9'h100 to 9'h10F
//
always_comb begin
  // Default base address is invalid and will trigger an error response thanks to the
  // APB demux decoder and access right check.
  kse_host_apb_mux_in_paddr[SECU_ENCL_APB_MUX_KSE_IDX] = '0;

  if (kse_apb_addr_is_aor) begin
    // Effective AOR address obtained from:
    // - AOR base address
    // - KSE3 AOR offset shifted left by 2 to get a word-aligned address
    //
    kse_host_apb_mux_in_paddr[SECU_ENCL_APB_MUX_KSE_IDX] = {aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR[SECU_ENCL_PAW:KSE3_AOR_ADDR_W+2],
                                                            kse_apb32_paddr[KSE3_AOR_ADDR_W-1:0],
                                                            2'b00};

  end else if (kse_apb32_paddr[KSE3_APB_ADDR_W-1:KSE3_OTP_ADDR_W] == kudelski_kse3_pkg::KSE3_OTP_START_ADDR[KSE3_APB_ADDR_W-1:KSE3_OTP_ADDR_W]) begin
    // Effective OTP address obtained from:
    // - OTP base address
    // - KSE3 OTP offset
    //
    kse_host_apb_mux_in_paddr[SECU_ENCL_APB_MUX_KSE_IDX] = {aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR[SECU_ENCL_PAW:KSE3_OTP_ADDR_W],
                                                            kse_apb32_paddr[KSE3_OTP_ADDR_W-1:0]};
  end
end

// ----------------------------------------------------------------------------
// APB interconnect
// ----------------------------------------------------------------------------
//
// Logic in this section is used to connect the following components:
//
// -  APB managers:      HOST (APU), JTAG, KSE
// -  APB subordinates:  OTP, AOR, Error Response
//
always_comb begin
  kse_host_apb_mux_in_paddr   [SECU_ENCL_APB_MUX_HOST_IDX] = i_apb_s_paddr;
  kse_host_apb_mux_in_pwdata  [SECU_ENCL_APB_MUX_HOST_IDX] = i_apb_s_pwdata;
  kse_host_apb_mux_in_pwrite  [SECU_ENCL_APB_MUX_HOST_IDX] = i_apb_s_pwrite;
  kse_host_apb_mux_in_psel    [SECU_ENCL_APB_MUX_HOST_IDX] = i_apb_s_psel;
  kse_host_apb_mux_in_penable [SECU_ENCL_APB_MUX_HOST_IDX] = i_apb_s_penable;
  kse_host_apb_mux_in_pstrb   [SECU_ENCL_APB_MUX_HOST_IDX] = i_apb_s_pstrb;
  kse_host_apb_mux_in_pprot   [SECU_ENCL_APB_MUX_HOST_IDX] = PPROT_VAL;
  o_apb_s_pready                                           = kse_host_apb_mux_in_pready  [SECU_ENCL_APB_MUX_HOST_IDX];
  o_apb_s_prdata                                           = kse_host_apb_mux_in_prdata  [SECU_ENCL_APB_MUX_HOST_IDX];
  o_apb_s_pslverr                                          = kse_host_apb_mux_in_pslverr [SECU_ENCL_APB_MUX_HOST_IDX];
end

// APB Mux between KSE-3 (secure) and HOST (non-secure) manager
axe_apb_mux #(
  .NB_APBIN (SECU_ENCL_MUX_NB_APBIN),
  .PAW      (SECU_ENCL_PAW),
  .PDW      (SECU_ENCL_PDW),
  .PSTRBW   (SECU_ENCL_PSTRBW)
) u_kse_host_apb_mux (
  .i_clk             (i_clk),
  .i_rst_n           (i_rst_n),
  .i_apb_s_paddr     (kse_host_apb_mux_in_paddr),
  .i_apb_s_pwdata    (kse_host_apb_mux_in_pwdata),
  .i_apb_s_pwrite    (kse_host_apb_mux_in_pwrite),
  .i_apb_s_psel      (kse_host_apb_mux_in_psel),
  .i_apb_s_penable   (kse_host_apb_mux_in_penable),
  .i_apb_s_pstrb     (kse_host_apb_mux_in_pstrb),
  .i_apb_s_pprot     (kse_host_apb_mux_in_pprot),
  .o_apb_s_pready    (kse_host_apb_mux_in_pready),
  .o_apb_s_prdata    (kse_host_apb_mux_in_prdata),
  .o_apb_s_pslverr   (kse_host_apb_mux_in_pslverr),
  .o_apb_m_paddr     (kse_host_apb_mux_out_paddr),
  .o_apb_m_pwdata    (kse_host_apb_mux_out_pwdata),
  .o_apb_m_pwrite    (kse_host_apb_mux_out_pwrite),
  .o_apb_m_psel      (kse_host_apb_mux_out_psel),
  .o_apb_m_penable   (kse_host_apb_mux_out_penable),
  .o_apb_m_pstrb     (kse_host_apb_mux_out_pstrb),
  .o_apb_m_pprot     (kse_host_apb_mux_out_pprot),
  .i_apb_m_pready    (kse_host_apb_mux_out_pready),
  .i_apb_m_prdata    (kse_host_apb_mux_out_prdata),
  .i_apb_m_pslverr   (kse_host_apb_mux_out_pslverr),
  .o_manager_idx     (apb_manager_idx)
);

// APB demux to access OTP wrapper or AOR.
axe_apb_demux #(
  .NB_APBOUT          (SECU_ENCL_DEMUX_NB_APBOUT),
  .PAW                (SECU_ENCL_PAW),
  .PDW                (SECU_ENCL_PDW),
  .PSTRBW             (SECU_ENCL_PSTRBW),
  .IDXW               (SECU_ENCL_APB_IDXW),
  .DEFAULT_SUB_IDX    (APB_DEMUX_ERR_IDX)
) u_otp_aor_apb_demux (
  .i_clk              (i_clk),
  .i_rst_n            (i_rst_n),
  .i_apb_s_paddr      (kse_host_apb_mux_out_paddr),
  .i_apb_s_pwdata     (kse_host_apb_mux_out_pwdata),
  .i_apb_s_pwrite     (kse_host_apb_mux_out_pwrite),
  .i_apb_s_psel       (kse_host_apb_mux_out_psel),
  .i_apb_s_penable    (kse_host_apb_mux_out_penable),
  .i_apb_s_pstrb      (kse_host_apb_mux_out_pstrb),
  .i_apb_s_pprot      (kse_host_apb_mux_out_pprot),
  .o_apb_s_pready     (kse_host_apb_mux_out_pready),
  .o_apb_s_prdata     (kse_host_apb_mux_out_prdata),
  .o_apb_s_pslverr    (kse_host_apb_mux_out_pslverr),
  .o_apb_m_paddr      (apb_demux_out_paddr),
  .o_apb_m_pwdata     (apb_demux_out_pwdata),
  .o_apb_m_pwrite     (apb_demux_out_pwrite),
  .o_apb_m_psel       (apb_demux_out_psel),
  .o_apb_m_penable    (apb_demux_out_penable),
  .o_apb_m_pstrb      (apb_demux_out_pstrb),
  .o_apb_m_pprot      (apb_demux_out_pprot),
  .i_apb_m_pready     (apb_demux_out_pready),
  .i_apb_m_prdata     (apb_demux_out_prdata),
  .i_apb_m_pslverr    (apb_demux_out_pslverr),
  .i_sub_idx_from_dec (apb_subordinate_idx)
);

// APB demux subordinate signals assignments
always_comb begin
  // AOR
  secu_aor_apb_s_h2d.paddr                  = apb_demux_out_paddr   [APB_DEMUX_AOR_IDX];
  secu_aor_apb_s_h2d.psel                   = apb_demux_out_psel    [APB_DEMUX_AOR_IDX];
  secu_aor_apb_s_h2d.penable                = apb_demux_out_penable [APB_DEMUX_AOR_IDX];
  secu_aor_apb_s_h2d.pwrite                 = apb_demux_out_pwrite  [APB_DEMUX_AOR_IDX];
  secu_aor_apb_s_h2d.pwdata                 = apb_demux_out_pwdata  [APB_DEMUX_AOR_IDX];
  secu_aor_apb_s_h2d.pstrb                  = apb_demux_out_pstrb   [APB_DEMUX_AOR_IDX];
  secu_aor_apb_s_h2d.pprot                  = apb_demux_out_pprot   [APB_DEMUX_AOR_IDX];
  apb_demux_out_pready  [APB_DEMUX_AOR_IDX] = secu_aor_apb_s_d2h.pready;
  apb_demux_out_pslverr [APB_DEMUX_AOR_IDX] = secu_aor_apb_s_d2h.pslverr;
  apb_demux_out_prdata  [APB_DEMUX_AOR_IDX] = secu_aor_apb_s_d2h.prdata;

  // Default subordinate (Error response)
  apb_demux_out_pready  [APB_DEMUX_ERR_IDX] = apb_demux_out_psel[APB_DEMUX_ERR_IDX];
  apb_demux_out_pslverr [APB_DEMUX_ERR_IDX] = 1'b1;
  apb_demux_out_prdata  [APB_DEMUX_ERR_IDX] = '0;
end

// APB demux decoder and access right checks.
soc_mgmt_secu_apb_dec u_soc_mgmt_secu_apb_dec (
  .i_paddr                  (kse_host_apb_mux_out_paddr),
  .i_pwrite                 (kse_host_apb_mux_out_pwrite),
  .i_lcs_valid              (lcs_valid_sync),
  .i_lcs_is_chip_wafer_test (lcs_is_chip_wafer_test),
  .i_manager_idx            (apb_manager_idx),
  .o_sub_idx                (apb_subordinate_idx)
);

// APB async bridge for OTP
axe_apb_cdc # (
  .SyncStages   (SYNC_STAGE_NUM),
  .ApbAddrWidth (SECU_ENCL_PAW),
  .ApbDataWidth (SECU_ENCL_PDW)
) u_otp_apb_async_bridge (
  .i_src_clk        (i_clk),
  .i_src_rst_n      (i_ao_rst_n),
  .i_dst_clk        (i_otp_wrapper_clk),
  .i_dst_rst_n      (i_otp_wrapper_rst_n),
  .i_apb_s_paddr    (apb_demux_out_paddr[APB_DEMUX_OTP_IDX]),
  .i_apb_s_pwdata   (apb_demux_out_pwdata[APB_DEMUX_OTP_IDX]),
  .i_apb_s_pwrite   (apb_demux_out_pwrite[APB_DEMUX_OTP_IDX]),
  .i_apb_s_psel     (apb_demux_out_psel[APB_DEMUX_OTP_IDX]),
  .i_apb_s_penable  (apb_demux_out_penable[APB_DEMUX_OTP_IDX]),
  .i_apb_s_pstrb    (apb_demux_out_pstrb[APB_DEMUX_OTP_IDX]),
  .i_apb_s_pprot    (apb_demux_out_pprot[APB_DEMUX_OTP_IDX]),
  .o_apb_s_pready   (apb_demux_out_pready[APB_DEMUX_OTP_IDX]),
  .o_apb_s_prdata   (apb_demux_out_prdata[APB_DEMUX_OTP_IDX]),
  .o_apb_s_pslverr  (apb_demux_out_pslverr[APB_DEMUX_OTP_IDX]),
  .o_apb_m_paddr    (otp_csr_apb_s_h2d.paddr),
  .o_apb_m_pwdata   (otp_csr_apb_s_h2d.pwdata),
  .o_apb_m_pwrite   (otp_csr_apb_s_h2d.pwrite),
  .o_apb_m_psel     (otp_csr_apb_s_h2d.psel),
  .o_apb_m_penable  (otp_csr_apb_s_h2d.penable),
  .o_apb_m_pstrb    (otp_csr_apb_s_h2d.pstrb),
  .o_apb_m_pprot    (otp_csr_apb_s_h2d.pprot),
  .i_apb_m_pready   (otp_csr_apb_s_d2h.pready),
  .i_apb_m_prdata   (otp_csr_apb_s_d2h.prdata),
  .i_apb_m_pslverr  (otp_csr_apb_s_d2h.pslverr)
);

// ----------------------------------------------------------------------------
// OTP Wrapper instantiation
// ----------------------------------------------------------------------------
otp_wrapper u_otp_wrapper (
  .i_clk                        (i_otp_wrapper_clk),
  .i_rst_n                      (i_otp_wrapper_rst_n),
  .i_analog_clk                 (otp_wrapper_analog_clk),
  .i_apb                        (otp_csr_apb_s_h2d),
  .o_apb                        (otp_csr_apb_s_d2h),
  .i_otp_clear                  ('0),                       // TODO(kluciani, Check if to be removed.)
  .o_otp_clear_ack              (),                         // TODO(kluciani, Check if to be removed.)
  .o_lcs_valid                  (lcs_valid),
  .o_lcs_is_chip_wafer_test     (lcs_is_chip_wafer_test),
  .o_lcs_is_chip_perso          (lcs_is_chip_perso),
  .o_lcs_is_user_delivery       (lcs_is_user_delivery),
  .o_lcs_is_user_secured        (lcs_is_user_secured),
  .o_lcs_is_user_decommissioned (lcs_is_user_decommissioned),
  .o_lcs_is_chip_field_return   (lcs_is_chip_field_return),
  .o_lcs_is_terminated          (lcs_is_terminated),
  .i_dft_scan_test_mode         (i_dft_scan_test_mode),
  .i_dft_otp_test_mode          (i_dft_otp_test_mode),
  .i_dft_otp_tst_a              (i_dft_otp_tst_a),
  .i_dft_otp_tst_din            (i_dft_otp_tst_din),
  .i_dft_otp_tst_readen         (i_dft_otp_tst_readen),
  .i_dft_otp_tst_ceb            (i_dft_otp_tst_ceb),
  .i_dft_otp_tst_cle            (i_dft_otp_tst_cle),
  .i_dft_otp_tst_dle            (i_dft_otp_tst_dle),
  .i_dft_otp_tst_web            (i_dft_otp_tst_web),
  .i_dft_otp_tst_rstb           (i_dft_otp_tst_rstb),
  .i_dft_otp_tst_cpumpen        (i_dft_otp_tst_cpumpen),
  .i_dft_otp_tst_pgmen          (i_dft_otp_tst_pgmen),
  .i_dft_otp_tst_seltm          (i_dft_otp_tst_seltm),
  .i_dft_otp_tst_vddrdy         (i_dft_otp_tst_vddrdy),
  .i_dft_otp_tst_clken          (i_dft_otp_tst_clken),
  .o_dft_otp_tst_d              (o_dft_otp_tst_d),
  .o_dft_otp_tst_lock           (o_dft_otp_tst_lock),
  .io_otp_vtdo                  (io_otp_vtdo),
  .io_otp_vrefm                 (io_otp_vrefm),
  .io_otp_vpp                   (io_otp_vpp)
);

// ----------------------------------------------------------------------------
//
// Synchronize lcs_valid flag from i_otp_wrapper_clk (50MHz) to i_clk (100MHz typical).
// This flag is set only once and will stay set until cold reset.
// This signal is used as a qualifier for all lcs_is_* signals.
//
// ----------------------------------------------------------------------------
axe_tcl_seq_sync #(
  .SyncStages (SYNC_STAGE_NUM),
  .ResetValue (1'b0)
) u_lcs_valid_sync (
  .i_clk   (i_clk),
  .i_rst_n (i_ao_rst_n),
  .i_d     (lcs_valid),
  .o_q     (lcs_valid_sync)
);

// ----------------------------------------------------------------------------
// OTP analog clock divider.
//
// The OTP analog logic requires a clock with frequency between 1MHz and 5MHz.
// This clock is not used by the digital logic and can be asynchronous to any other signal.
// It is here derived from the 50MHz i_ref_clk = i_otp_wrapper_clk.
// To get a 50% duty-cycle, we divide i_ref_clk by 16 and get 3.125MHz frequency.
//
// Given the low frequency and the fact that it's meant for analog only, we use
// a simple 4-bit counter to divide by 2^4.
//
// ----------------------------------------------------------------------------

// DFFR: D-Flip-Flop, asynchronous reset
always_ff @(posedge i_otp_wrapper_clk or negedge i_otp_wrapper_rst_n) begin
  if (!i_otp_wrapper_rst_n) otp_clk_div_cnt_q <= '0;
  else                      otp_clk_div_cnt_q <= otp_clk_div_cnt_q + 1;
end

assign otp_wrapper_analog_clk = otp_clk_div_cnt_q[LOG2_OTP_CLK_DIV-1];

// ----------------------------------------------------------------------------
// Always-on Registers (AOR) instantiation
// ----------------------------------------------------------------------------
soc_mgmt_secu_aor_csr_reg_top #(
  .StageNum (SYNC_STAGE_NUM)
) u_soc_mgmt_secu_aor_csr_reg_top (
  .clk_i     ( i_clk              ),
  .rst_ni    ( i_ao_rst_n         ),
  .apb_i     ( secu_aor_apb_s_h2d ),
  .apb_o     ( secu_aor_apb_s_d2h ),
  .reg2hw    ( secu_aor_reg2hw    ),
  .hw2reg    ( secu_aor_hw2reg    ),
  .devmode_i ( 1'b1               )
);

always_comb secu_aor_hw2reg.jtag_dbg.d  = tdr_jtag_dbg_sync;

endmodule
