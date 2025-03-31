// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MVM JTAG TDR wrapper
// Implements glue logic for CSR/JTAG compatiblity and instantiates the TDR core
// Interface upstream with AI Core JTAG TAP, downstream with IMC BIST CTL
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef MVM_JTAG_TDR_SV
`define MVM_JTAG_TDR_SV

module mvm_jtag_tdr
  import imc_bist_pkg::IMC_BIST_REPAIR_ATTEMPT_PW;
#(
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t,
  parameter type aic_csr_reg2hw_imc_status_t = imc_bist_pkg::reg2hw_imc_bist_status_reg_t
) (
  input  wire i_clk,
  input  logic i_rst_n,
  // JTAG
  input  logic tcki,
  input  logic trsti,
  // JTAG TAP
  input  logic seli,
  input  logic sei,
  input  logic cei,
  input  logic uei,
  input  logic tdi,
  output logic tdo,

  // IMC BIST
  output imc_bist_fast_clk_en_o,
  output aic_csr_reg2hw_t imc_bist_tdr2hw_o,
  input  aic_csr_hw2reg_t imc_bist_hw2tdr_i
);

  typedef union packed {
    imc_bist_pkg::reg2hw_imc_bist_cmd_reg_t as_struct;
    logic [3:0] raw;
  } reg2hw_cmd_t;

  aic_csr_reg2hw_imc_status_t s_status_reg, r_status_reg;
  aic_csr_reg2hw_t imc_bist_tdr2hw_core;
  aic_csr_hw2reg_t imc_bist_hw2tdr_core;

  // Unconnected OK: imc_bist_hw2tdr_i.imc_bist_cmd is not used, JTAG mode does not support acknowledging CMD
  logic unconnected_ok_cmd;
  // Unconnected OK: imc_bist_tdr2hw_core.status is not used, status reg to hw is handled at this level (not mvm_jtag_tdr_core level)
  logic unconnected_ok_status;

  // Synchronization
  // mvm i_clk -> jtag i_clk
  logic r_status_done_sync;

  logic                                  core_mbist_start;
  logic                                  core_cbist_start;
  logic                                  core_resume;
  logic                                  core_stop;
  logic [IMC_BIST_REPAIR_ATTEMPT_PW-1:0] core_max_repair_attempts;
  logic                          [2-1:0] core_bira_mode;
  logic                                  core_burn_in;
  logic                                  core_fail_analysis;

  assign unconnected_ok_cmd = |imc_bist_hw2tdr_i.imc_bist_cmd;

  mvm_jtag_tdr_core #(
    .aic_csr_hw2reg_t(aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(aic_csr_reg2hw_t)
  ) i_mvm_jtag_tdr_core (
    .tcki(tcki),
    .trsti(trsti),
    .seli(seli),
    .sei(sei),
    .cei(cei),
    .uei(uei),
    .tdi(tdi),
    .tdo(tdo),

    // Status
    .i_busy         (imc_bist_hw2tdr_core.imc_bist_status.busy.d),
    .i_done         (imc_bist_hw2tdr_core.imc_bist_status.done.d),
    .i_pass         (imc_bist_hw2tdr_core.imc_bist_status.pass.d),
    .i_repair_needed(imc_bist_hw2tdr_core.imc_bist_status.repair_needed.d),
    .i_error_bank   (imc_bist_hw2tdr_core.imc_bist_status.error_bank.d),
    .i_error_col    (imc_bist_hw2tdr_core.imc_bist_status.error_col.d),
    .i_error_cycle  (imc_bist_hw2tdr_core.imc_bist_status.error_cycle.d),

    // Cfg and Cmd
    .o_mbist_start        (core_mbist_start),
    .o_cbist_start        (core_cbist_start),
    .o_resume             (core_resume),
    .o_stop               (core_stop),
    .o_max_repair_attempts(core_max_repair_attempts),
    .o_bira_mode          (core_bira_mode),
    .o_burn_in            (core_burn_in),
    .o_fail_analysis      (core_fail_analysis)
  );

  assign imc_bist_tdr2hw_core = '{
    imc_bist_cmd: '{
      mbist_start: core_mbist_start,
      cbist_start: core_cbist_start,
      resume     : core_resume,
      stop       : core_stop
    },
    imc_bist_cfg: '{
      csr_sel            : '0,
      max_repair_attempts: core_max_repair_attempts,
      bira_mode          : core_bira_mode,
      burn_in            : core_burn_in,
      fail_analysis      : core_fail_analysis
    },
    default: '0
  };

  assign unconnected_ok_status = |imc_bist_tdr2hw_core.imc_bist_status;

  // Command sync jtag i_clk -> mvm i_clk
  // All cmds are unrelated, bus is one-hot-zero, no convergence management needed
  cc_cdc_sync_array #(
    .SyncStages (3),
    .Width      (4),
    .ResetValues(4'h0)
  ) i_cmd_sync (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_data (imc_bist_tdr2hw_core.imc_bist_cmd),
    .o_data (imc_bist_tdr2hw_o.imc_bist_cmd)
  );

  always_ff @(posedge i_clk, negedge i_rst_n) begin : status_loopback_sproc
    if (!i_rst_n) begin
      r_status_reg <= '0;
    end else begin
      r_status_reg <= s_status_reg;
    end
  end

  // verilog_format: off
  assign s_status_reg = '{
    busy: '{q: imc_bist_hw2tdr_i.imc_bist_status.busy.de ?
               imc_bist_hw2tdr_i.imc_bist_status.busy.d : r_status_reg.busy.q},
    pass: '{q: imc_bist_hw2tdr_i.imc_bist_status.pass.de ?
               imc_bist_hw2tdr_i.imc_bist_status.pass.d : r_status_reg.pass.q},
    done: '{q: imc_bist_hw2tdr_i.imc_bist_status.done.de ?
               imc_bist_hw2tdr_i.imc_bist_status.done.d : r_status_reg.done.q},
    repair_needed: '{q: imc_bist_hw2tdr_i.imc_bist_status.repair_needed.de ?
                        imc_bist_hw2tdr_i.imc_bist_status.repair_needed.d : r_status_reg.repair_needed.q},
    error_bank: '{q: imc_bist_hw2tdr_i.imc_bist_status.error_bank.de ?
                     imc_bist_hw2tdr_i.imc_bist_status.error_bank.d : r_status_reg.error_bank.q},
    error_col: '{q: imc_bist_hw2tdr_i.imc_bist_status.error_col.de ?
                    imc_bist_hw2tdr_i.imc_bist_status.error_col.d : r_status_reg.error_col.q},
    error_cycle: '{q: imc_bist_hw2tdr_i.imc_bist_status.error_cycle.de ?
                      imc_bist_hw2tdr_i.imc_bist_status.error_cycle.d : r_status_reg.error_cycle.q}
  };
  // verilog_format: on

  // Status sync mvm i_clk -> jtag i_clk
  // done is a qualifier for all other status fields
   cc_cdc_sync_array #(
    .SyncStages (3),
    .Width      (1),
    .ResetValues(1'b0)
  ) i_status_done_sync (
    .i_clk  (tcki),
    .i_rst_n(trsti),
    .i_data (r_status_reg.done.q),
    .o_data (r_status_done_sync)
  );

  assign imc_bist_hw2tdr_core = '{
          imc_bist_cmd: '0,
          imc_bist_status: '{
              busy: '{de: 1'b0, d: r_status_reg.busy.q},
              pass: '{de: 1'b0, d: r_status_reg.pass.q},
              done: '{de: 1'b0, d: r_status_done_sync},
              repair_needed: '{de: 1'b0, d: r_status_reg.repair_needed.q},
              error_bank: '{de: 1'b0, d: r_status_reg.error_bank.q},
              error_col: '{de: 1'b0, d: r_status_reg.error_col.q},
              error_cycle: '{de: 1'b0, d: r_status_reg.error_cycle.q}
          }
      };

  assign imc_bist_tdr2hw_o.imc_bist_cfg = '{
              fail_analysis: imc_bist_tdr2hw_core.imc_bist_cfg.fail_analysis,
              burn_in: imc_bist_tdr2hw_core.imc_bist_cfg.burn_in,
              bira_mode: imc_bist_tdr2hw_core.imc_bist_cfg.bira_mode,
              max_repair_attempts: imc_bist_tdr2hw_core.imc_bist_cfg.max_repair_attempts,
              csr_sel: 1'b0
          };
  assign imc_bist_tdr2hw_o.imc_bist_status = r_status_reg;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
`endif  // MVM_JTAG_TDR_SV
