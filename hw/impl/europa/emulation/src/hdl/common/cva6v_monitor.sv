import cva6v_pve_pkg::*;
import raptor_pkg::*;
import cva6v_config_pkg::*;
`include "cva6v/include/rvfi_types.svh"
`include "cva6v/include/cva6v/cva6v_tracing.svh"
`include "cva6v_dv_typedefs.svh"

module cva6v_monitor (
  input logic                          clk_i,
  input logic                          rst_ni,
  input [CVA6VConfig.CVA6Cfg.XLEN-1:0] hart_id_i,
  input logic                          enable,
  input logic                          new_file,
  input rvfi_probes_t                  rvfi_probes_o
);

  // CVA6 RISC-V formal interface port
  rvfi_instr_t [CVA6VConfig.CVA6Cfg.NrCommitPorts-1:0] rvfi_instr;
  rvfi_csr_t rvfi_csr;
  logic [31:0] tb_exit_o;

  cva6v_cva6_rvfi #(
    .CVA6Cfg   (CVA6VConfig.CVA6Cfg),
    .rvfi_instr_t(rvfi_instr_t),
    .rvfi_csr_t(rvfi_csr_t),
    .rvfi_probes_instr_t(rvfi_probes_instr_t),
    .rvfi_probes_csr_t(rvfi_probes_csr_t),
    .rvfi_probes_t(rvfi_probes_t)
  ) i_cva6_rvfi (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .rvfi_probes_i(rvfi_probes_o),
    .rvfi_instr_o (rvfi_instr),
    .rvfi_csr_o   (rvfi_csr)
  );

  rvfi_tracer #(
    .CVA6Cfg(CVA6VConfig.CVA6Cfg),
    .rvfi_instr_t(rvfi_instr_t),
    .rvfi_csr_t(rvfi_csr_t),
    .DEBUG_START(0),
    .DEBUG_STOP(0)
  ) i_rvfi_tracer (
    .hart_id_i(hart_id_i),
    .enable(enable),
    .new_file(new_file),
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvfi_i(rvfi_instr),
    .rvfi_csr_i(rvfi_csr),
    .end_of_test_o(tb_exit_o)
  );

endmodule
