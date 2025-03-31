// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DFT insertable TDR core
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

`ifndef KSE_JTAG_TDR_CORE_SV
`define KSE_JTAG_TDR_CORE_SV

module kse_jtag_tdr_core
  import soc_mgmt_pkg::*;
  import rot_pkg::*;
 (
  // AHB command information
  output logic [KSE3_JTAG_HAW-1:0]              o_ahb_haddr,
  output logic [SOC_MGMT_HDW-1:0]               o_ahb_hwdata,
  output logic                                  o_ahb_hwrite,
  // JTAG command information
  output logic                                  o_ahb_valid,
  output logic                                  o_enter_jtag_access_mode,
  output logic                                  o_init_kse3_adac_itf,
  output logic                                  o_jtag_dbg,
  // JTAG command synchronization
  // The following signal shall toggle between one command and the next.
  output logic                                  o_transaction_id,
  // Response to JTAG
  input  logic [SOC_MGMT_HDW-1:0]               i_ahb_hrdata,
  input  logic                                  i_jtag_ready,
  input  logic                                  i_jtag_kse_error,
  input  logic                                  i_jtag_ahb_error,
  input  logic                                  i_jtag_cmd_ignored
);

`ifndef TARGET_DFT
`ifndef TESSENT
  always_comb o_ahb_haddr              = '0;
  always_comb o_ahb_hwdata             = '0;
  always_comb o_ahb_hwrite             = '0;
  always_comb o_ahb_valid              = '0;
  always_comb o_enter_jtag_access_mode = '0;
  always_comb o_init_kse3_adac_itf     = '0;
  always_comb o_jtag_dbg               = '0;
  always_comb o_transaction_id         = '0;
`endif // ! TESSENT
`endif // ! TARGET_DFT

endmodule
`endif  // KSE_JTAG_TDR_CORE_SV
