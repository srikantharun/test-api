// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
module sys_spm_p
  import sys_spm_pkg::*;
(
  // Fast Clock, positive edge triggered
  input   wire   i_clk,
  // APB Clock, positive edge triggered
  input   wire   i_ref_clk,
  // Asynchronous POR / always On reset, active low
  input   wire   i_ao_rst_n,
  // Asynchronous global reset, active low
  input   wire   i_global_rst_n,
  // Synchronous NoC reset, active low
  output  wire   o_noc_rst_n,

  /// Isolation interface
  output logic o_noc_async_idle_req,
  input  logic i_noc_async_idle_ack,
  input  logic i_noc_async_idle_val,
  output logic o_noc_clken,

  // AXI Interface
  // - AW Channel
  input  chip_pkg::chip_axi_addr_t        i_lt_axi_s_awaddr,
  input  sys_spm_targ_lt_axi_id_t         i_lt_axi_s_awid,
  input  axi_pkg::axi_len_t               i_lt_axi_s_awlen,
  input  axi_pkg::axi_size_t              i_lt_axi_s_awsize,
  input  axi_pkg::axi_burst_t             i_lt_axi_s_awburst,
  input  axi_pkg::axi_cache_t             i_lt_axi_s_awcache,
  input  axi_pkg::axi_prot_t              i_lt_axi_s_awprot,
  input  logic                            i_lt_axi_s_awlock,
  input  axi_pkg::axi_qos_t               i_lt_axi_s_awqos,
  input  axi_pkg::axi_region_t            i_lt_axi_s_awregion,
  input  chip_pkg::chip_axi_lt_awuser_t   i_lt_axi_s_awuser,
  input  logic                            i_lt_axi_s_awvalid,
  output logic                            o_lt_axi_s_awready,
  // - W Channel
  input chip_pkg::chip_axi_lt_data_t      i_lt_axi_s_wdata,
  input chip_pkg::chip_axi_lt_wstrb_t     i_lt_axi_s_wstrb,
  input logic                             i_lt_axi_s_wlast,
  input chip_pkg::chip_axi_lt_wuser_t     i_lt_axi_s_wuser,
  input logic                             i_lt_axi_s_wvalid,
  output logic                            o_lt_axi_s_wready,
  // - B Channel
  output logic                            o_lt_axi_s_bvalid,
  output sys_spm_targ_lt_axi_id_t         o_lt_axi_s_bid,
  output chip_pkg::chip_axi_lt_buser_t    o_lt_axi_s_buser,
  output axi_pkg::axi_resp_t              o_lt_axi_s_bresp,
  input  logic                            i_lt_axi_s_bready,
  // - AR Channel
  input  chip_pkg::chip_axi_addr_t        i_lt_axi_s_araddr,
  input  sys_spm_targ_lt_axi_id_t         i_lt_axi_s_arid,
  input  axi_pkg::axi_len_t               i_lt_axi_s_arlen,
  input  axi_pkg::axi_size_t              i_lt_axi_s_arsize,
  input  axi_pkg::axi_burst_t             i_lt_axi_s_arburst,
  input  axi_pkg::axi_cache_t             i_lt_axi_s_arcache,
  input  axi_pkg::axi_prot_t              i_lt_axi_s_arprot,
  input  axi_pkg::axi_qos_t               i_lt_axi_s_arqos,
  input  axi_pkg::axi_region_t            i_lt_axi_s_arregion,
  input  chip_pkg::chip_axi_lt_aruser_t   i_lt_axi_s_aruser,
  input  logic                            i_lt_axi_s_arlock,
  input  logic                            i_lt_axi_s_arvalid,
  output logic                            o_lt_axi_s_arready,
  // - R Channel
  output logic                            o_lt_axi_s_rvalid,
  output logic                            o_lt_axi_s_rlast,
  output sys_spm_targ_lt_axi_id_t         o_lt_axi_s_rid,
  output chip_pkg::chip_axi_lt_data_t     o_lt_axi_s_rdata,
  output chip_pkg::chip_axi_lt_ruser_t    o_lt_axi_s_ruser,
  output axi_pkg::axi_resp_t              o_lt_axi_s_rresp,
  input  logic                            i_lt_axi_s_rready,
  // APB Interface
  input  chip_pkg::chip_syscfg_addr_t     i_cfg_apb4_s_paddr,
  input  chip_pkg::chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata,
  input  logic                            i_cfg_apb4_s_pwrite,
  input  logic                            i_cfg_apb4_s_psel,
  input  logic                            i_cfg_apb4_s_penable,
  input  chip_pkg::chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb,
  input  logic  [3-1:0]                   i_cfg_apb4_s_pprot,
  output logic                            o_cfg_apb4_s_pready,
  output chip_pkg::chip_apb_syscfg_data_t o_cfg_apb4_s_prdata,
  output logic                            o_cfg_apb4_s_pslverr,
  // Error IRQ signal
  output logic o_irq,
  // Observation port
  output logic [15:0] o_sysspm_obs,

  // DFT signals
  input  wire        tck,
  input  wire        trst,
  input  logic       tms,
  input  logic       tdi,
  output logic       tdo_en,
  output logic       tdo,

  input  wire        test_clk,
  input  logic       test_mode,
  input  logic       edt_update,
  input  logic       scan_en,
  input  logic [7:0] scan_in,
  output logic [7:0] scan_out,

  input  wire        bisr_clk,
  input  wire        bisr_reset,
  input  logic       bisr_shift_en,
  input  logic       bisr_si,
  output logic       bisr_so
);
  // --------------------------------------------------------------
  // Signals
  // --------------------------------------------------------------
  localparam int unsigned SYS_SPM_ECC_DATA_WIDTH = ($bits(spm_pkg::spm_ecc_err_syndrome_t) +
                                                    $bits(spm_pkg::spm_ecc_err_index_t) + $bits(spm_pkg::spm_ecc_err_type_t));

  pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;

  sys_spm_csr_reg_pkg::sys_spm_csr_reg2hw_t reg2hw;
  sys_spm_csr_reg_pkg::sys_spm_csr_hw2reg_t hw2reg;

  spm_pkg::spm_error_status_t scp_error_status;
  sys_spm_error_status_data_t sys_spm_error_status_data;
  sys_spm_error_status_data_t sys_spm_error_status_data_sync;
  logic                       ecc_status_sync_busy;
  logic                       ecc_err_present_q;
  logic                       ecc_err_present_sync;
  logic                       scp_err_disable_sync;
  logic [15:0]                sys_spm_obs;
  logic [15:0]                sys_spm_obs_q;
  logic                       obs_bus_new_value;
  logic                       obs_bus_en;
  logic                       obs_bus_sync_busy;

  // Internal Clocks and Resets
  wire  sys_spm_clk;
  wire  sys_spm_rst_n;
  wire  ao_rst_sync_n;

  // SRAM control signals
  logic ret;
  logic pde;
  logic prn;

  // --------------------------------------------------------------
  // RTL
  // --------------------------------------------------------------

  // A new valid ECC indication for synchronization to the CSR
  always_ff @(posedge sys_spm_clk or negedge sys_spm_rst_n) begin
    if (~sys_spm_rst_n) begin
      ecc_err_present_q <= 1'b0;
    end
    // The current content of the register went to synchronization and we are free
    // to take the next values coming from spm_control (might be "ecc_err" asserted or not)
    else if (~ecc_status_sync_busy) begin
      ecc_err_present_q <= scp_error_status.ecc_err;
    end
    // Capture the next ecc_err from spm_control if "ecc_status_sync_busy" is asserted - thus guarantees that
    // the next ECC error will not be missed - the only one way to clear the captured "ecc_err" (ecc_err_present_q)
    // is when "ecc_status_sync_busy" goes low and the current "ecc_err_present_q" goes to synchronization -
    // the highest priority and (the latest) ECC is guaranteed by the logic in spm_control (that's why we should not take care of priority here)
    else if (scp_error_status.ecc_err) begin
      ecc_err_present_q <= 1'b1;
    end
  end

  // The new ECC data for synchronization to the CSR (only when there is a valid ECC indication)
  always_ff @(posedge sys_spm_clk or negedge sys_spm_rst_n) begin
    if (~sys_spm_rst_n) begin
      sys_spm_error_status_data.ecc_err_index    <= '0;
      sys_spm_error_status_data.ecc_err_type     <= spm_pkg::spm_ecc_err_type_t'('0);
      sys_spm_error_status_data.ecc_err_syndrome <= '0;
    end
    else if (scp_error_status.ecc_err) begin
      sys_spm_error_status_data.ecc_err_index    <= scp_error_status.ecc_err_index;
      sys_spm_error_status_data.ecc_err_type     <= scp_error_status.ecc_err_type;
      sys_spm_error_status_data.ecc_err_syndrome <= scp_error_status.ecc_err_syndrome;
    end
  end

  // Synchronization for the ECC error status signals from sys_spm_clk to i_ref_clk
  axe_ccl_cdc_bus #(
    .SyncStages (SYS_SPM_SYNC_STAGES),
    .data_t     (sys_spm_error_status_data_t)
  ) u_ecc_status_sync (
    .i_src_clk    (sys_spm_clk),
    .i_src_rst_n  (sys_spm_rst_n),
    .i_src_en     (ecc_err_present_q),
    .i_src_data   (sys_spm_error_status_data),
    .o_src_busy   (ecc_status_sync_busy),
    .i_dst_clk    (i_ref_clk),
    .i_dst_rst_n  (ao_rst_sync_n),
    .o_dst_data   (sys_spm_error_status_data_sync),
    .o_dst_update (ecc_err_present_sync)
  );

  // Use "ecc_err_present_sync" indication (ECC_ERR_PRESENT CSR field) as enable to capture all relevant ECC error fields in the corresponding ECC status CSR
  always_comb begin
    hw2reg.scp_err_status.ecc_err_present.de  = ecc_err_present_sync;
    hw2reg.scp_err_status.ecc_err_index.de    = ecc_err_present_sync;
    hw2reg.scp_err_status.ecc_err_type.de     = ecc_err_present_sync;
    hw2reg.scp_err_status.ecc_err_syndrome.de = ecc_err_present_sync;

    hw2reg.scp_err_status.ecc_err_present.d   = ecc_err_present_sync;
    hw2reg.scp_err_status.ecc_err_index.d     = sys_spm_error_status_data_sync.ecc_err_index;
    hw2reg.scp_err_status.ecc_err_type.d      = sys_spm_error_status_data_sync.ecc_err_type;
    hw2reg.scp_err_status.ecc_err_syndrome.d  = sys_spm_error_status_data_sync.ecc_err_syndrome;
  end


  // Synchronization for the ECC disable configuration CSR signal from i_ref_clk to sys_spm_clk
  axe_tcl_seq_sync #(
    .SyncStages(SYS_SPM_SYNC_STAGES),
    .ResetValue(1'b0)
  ) u_ecc_disable_csr_sync (
    .i_clk   (sys_spm_clk),
    .i_rst_n (sys_spm_rst_n),
    .i_d     (reg2hw.scp_err_disable.q),
    .o_q     (scp_err_disable_sync)
  );


  assign obs_bus_new_value = (sys_spm_obs_q != sys_spm_obs);

  // A new valid indication for obs bus synchronization
  always_ff @(posedge sys_spm_clk or negedge sys_spm_rst_n) begin
    if (~sys_spm_rst_n) begin
      obs_bus_en <= 1'b0;
    end
    else if (~obs_bus_sync_busy) begin
      obs_bus_en <= obs_bus_new_value;
    end
    else if (obs_bus_new_value) begin
      obs_bus_en <= 1'b1;
    end
  end

  // The new obs bus synchronization (only when there is a new valid indication)
  always_ff @(posedge sys_spm_clk or negedge sys_spm_rst_n) begin
    if (~sys_spm_rst_n) begin
      sys_spm_obs_q <= {16{1'b1}};
    end
    else if (obs_bus_new_value) begin
      sys_spm_obs_q <= sys_spm_obs;
    end
  end

  // Synchronization for the observation signals from sys_spm_clk to i_ref_clk
  axe_ccl_cdc_bus #(
    .SyncStages (SYS_SPM_SYNC_STAGES),
    .data_t     (logic [15:0])
  ) u_obs_bus_sync (
    .i_src_clk    (sys_spm_clk),
    .i_src_rst_n  (sys_spm_rst_n),
    .i_src_en     (obs_bus_en),
    .i_src_data   (sys_spm_obs_q),
    .o_src_busy   (obs_bus_sync_busy),
    .i_dst_clk    (i_ref_clk),
    .i_dst_rst_n  (ao_rst_sync_n),
    .o_dst_data   (o_sysspm_obs),
    .o_dst_update ()
  );


  // ---------------
  // -- Partition Control
  pctl #(
    .N_FAST_CLKS      (1),
    .N_RESETS         (1),
    .N_MEM_PG         (1),
    .N_FENCES         (1),
    .N_THROTTLE_PINS  (0),
    .CLKRST_MATRIX    (1'b1),
    .PLL_CLK_IS_I_CLK (1'b0),
    .NOC_RST_IDX      (1'b0),
    .SYNC_CLK_IDX     (1'b0),
    .AUTO_RESET_REMOVE(1'b1), // Sys-SPM should leave reset automatically
    .AUTO_FENCE_REMOVE(1'b1), // Sys-SPM should lower fences automatically
    .paddr_t          (chip_pkg::chip_syscfg_addr_t),
    .pdata_t          (chip_pkg::chip_apb_syscfg_data_t),
    .pstrb_t          (chip_pkg::chip_apb_syscfg_strb_t)
  ) u_pctl (
    // Input clocks and resets
    .i_clk         (i_ref_clk),
    .i_ao_rst_n    (i_ao_rst_n),
    .i_global_rst_n(i_global_rst_n),
    .i_test_mode   (test_mode),
    .i_throttle(1'b0),
    // Output clocks and resets
    .i_pll_clk        (i_clk),
    .o_partition_clk  (sys_spm_clk),
    .o_partition_rst_n(sys_spm_rst_n),

    .o_ao_rst_sync_n(ao_rst_sync_n),

    // Isolation interface
    .o_noc_async_idle_req,
    .i_noc_async_idle_ack,
    .i_noc_async_idle_val,
    .o_noc_clken,
    .o_noc_rst_n,

    .o_int_shutdown_req  (/*NC*/),
    .i_int_shutdown_ack  (1'b1),

    // SRAM control signals
    .o_ret(ret),
    .o_pde(pde),
    .i_prn(prn),

    // SYS_CFG Bus
    .i_cfg_apb4_s_paddr,
    .i_cfg_apb4_s_pwdata,
    .i_cfg_apb4_s_pwrite,
    .i_cfg_apb4_s_psel,
    .i_cfg_apb4_s_penable,
    .i_cfg_apb4_s_pstrb,
    .i_cfg_apb4_s_pprot,
    .o_cfg_apb4_s_pready,
    .o_cfg_apb4_s_prdata,
    .o_cfg_apb4_s_pslverr,
    // Sync interface
    .i_global_sync_async(1'b0),
    .o_global_sync      (/*NC*/),
    // External APB interface
    .o_ao_csr_apb_req(ao_csr_apb_req),
    .i_ao_csr_apb_rsp(ao_csr_apb_rsp)
  );

  // ---------------
  // -- AO CSRs
  sys_spm_csr_reg_top u_sys_spm_ao_csr (
    // Clk/Rst
    .clk_i (i_ref_clk),
    .rst_ni(ao_rst_sync_n),
    // APB interface
    .apb_i(ao_csr_apb_req),
    .apb_o(ao_csr_apb_rsp),
    // HW interface
    .reg2hw,
    .hw2reg,
    // Config
    .devmode_i(1'b1)
  );

  // ---------------
  // -- Sys-SPM Instance
  sys_spm #(
    // AXI types
    .sys_spm_axi_data_t (chip_pkg::chip_axi_lt_data_t),
    .sys_spm_axi_strb_t (chip_pkg::chip_axi_lt_wstrb_t),
    .sys_spm_axi_len_t  (axi_pkg::axi_len_t),
    .sys_spm_axi_addr_t (chip_pkg::chip_axi_addr_t),
    .sys_spm_axi_id_t   (sys_spm_targ_lt_axi_id_t),
    .sys_spm_axi_size_t (axi_pkg::axi_size_t),
    .sys_spm_axi_burst_t(axi_pkg::axi_burst_t),
    .sys_spm_axi_resp_t (axi_pkg::axi_resp_t),
    .sys_spm_axi_cache_t(axi_pkg::axi_cache_t),
    .sys_spm_axi_prot_t (axi_pkg::axi_prot_t)
) u_sys_spm(
    // Clock and Reset
    .i_clk  (sys_spm_clk),
    .i_rst_n(sys_spm_rst_n),

    // ---------------
    // AXI Write Address Channel
    .i_lt_axi_s_awaddr  (i_lt_axi_s_awaddr),
    .i_lt_axi_s_awid    (i_lt_axi_s_awid),
    .i_lt_axi_s_awlen   (i_lt_axi_s_awlen),
    .i_lt_axi_s_awsize  (i_lt_axi_s_awsize),
    .i_lt_axi_s_awburst (i_lt_axi_s_awburst),
    .i_lt_axi_s_awcache (i_lt_axi_s_awcache),
    .i_lt_axi_s_awprot  (i_lt_axi_s_awprot),
    .i_lt_axi_s_awlock  (i_lt_axi_s_awlock),
    .i_lt_axi_s_awvalid (i_lt_axi_s_awvalid),
    .o_lt_axi_s_awready (o_lt_axi_s_awready),
    // AXI Write Data Channel
    .i_lt_axi_s_wdata   (i_lt_axi_s_wdata),
    .i_lt_axi_s_wstrb   (i_lt_axi_s_wstrb),
    .i_lt_axi_s_wlast   (i_lt_axi_s_wlast),
    .i_lt_axi_s_wvalid  (i_lt_axi_s_wvalid),
    .o_lt_axi_s_wready  (o_lt_axi_s_wready),
    // AXI Write Response Channel
    .o_lt_axi_s_bvalid  (o_lt_axi_s_bvalid),
    .o_lt_axi_s_bid     (o_lt_axi_s_bid),
    .o_lt_axi_s_bresp   (o_lt_axi_s_bresp),
    .i_lt_axi_s_bready  (i_lt_axi_s_bready),
    // AXI Read Address Channel
    .i_lt_axi_s_araddr  (i_lt_axi_s_araddr),
    .i_lt_axi_s_arid    (i_lt_axi_s_arid),
    .i_lt_axi_s_arlen   (i_lt_axi_s_arlen),
    .i_lt_axi_s_arsize  (i_lt_axi_s_arsize),
    .i_lt_axi_s_arburst (i_lt_axi_s_arburst),
    .i_lt_axi_s_arcache (i_lt_axi_s_arcache),
    .i_lt_axi_s_arprot  (i_lt_axi_s_arprot),
    .i_lt_axi_s_arlock  (i_lt_axi_s_arlock),
    .i_lt_axi_s_arvalid (i_lt_axi_s_arvalid),
    .o_lt_axi_s_arready (o_lt_axi_s_arready),
    // AXI Read Channel
    .o_lt_axi_s_rvalid  (o_lt_axi_s_rvalid),
    .o_lt_axi_s_rlast   (o_lt_axi_s_rlast),
    .o_lt_axi_s_rid     (o_lt_axi_s_rid),
    .o_lt_axi_s_rdata   (o_lt_axi_s_rdata),
    .o_lt_axi_s_rresp   (o_lt_axi_s_rresp),
    .i_lt_axi_s_rready  (i_lt_axi_s_rready),

    // ---------------
    // - ECC and Error signals
    // Error IRQ signal
    .o_irq(o_irq),
    // Disable ECC error reporting and in flight correction.
    .i_scp_ecc_disable (scp_err_disable_sync),
    // Error status
    .o_scp_error_status(scp_error_status),
    // Internal observation
    .o_spm_obs(sys_spm_obs),
    // ---------------
    // RAM Configuration pins
    .i_ret  (ret),
    .i_pde  (pde),
    .o_prn  (prn),

    .i_se   (scan_en)
);

endmodule
