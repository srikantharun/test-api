// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: CVA6V DV Type Defines
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

// RVFI PROBES
typedef `RVFI_INSTR_T(CVA6VConfig.CVA6Cfg)                 rvfi_instr_t;
typedef `RVFI_CSR_ELMT_T(CVA6VConfig.CVA6Cfg)              rvfi_csr_elmt_t;
typedef `RVFI_CSR_T(CVA6VConfig.CVA6Cfg, rvfi_csr_elmt_t)  rvfi_csr_t;
typedef `RVFI_PROBES_INSTR_T(CVA6VConfig.CVA6Cfg)          rvfi_probes_instr_t;
typedef `RVFI_PROBES_CSR_T(CVA6VConfig.CVA6Cfg)            rvfi_probes_csr_t;
typedef `RVVI_TRACE_T(CVA6VConfig)                         rvvi_trace_t;


typedef struct packed {
  rvfi_probes_csr_t   csr;
  rvfi_probes_instr_t instr;
} rvfi_probes_t;

typedef `RAPTOR_TRACE_T(CVA6VConfig)                       raptor_trace_sigs_t;

parameter int unsigned VRFAddrWidth           = $clog2(VRFRegCount * VRFBankCount);
parameter int unsigned VRFOffsetWidth         = (VRFBankColumnCount > 'd1) ? $clog2(VRFBankColumnCount) : 'd1;
parameter type  cva6_config_t = cva6v_config_pkg::cva6_cfg_t;
