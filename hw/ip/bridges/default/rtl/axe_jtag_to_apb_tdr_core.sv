// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DFT insertable TDR core
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

`ifndef AXE_JTAG_TO_APB_TDR_CORE_SV
`define AXE_JTAG_TO_APB_TDR_CORE_SV

module axe_jtag_to_apb_tdr_core
#(
  // width definition for APB address bus
  parameter int  unsigned PAW               = 16                       ,
  // width definition for APB data bus
  parameter int  unsigned PDW               = 32                       ,
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW            = 4                        ,
  // APB types
  parameter type          paddr_t       = logic [PAW              -1:0],
  parameter type          pdata_t       = logic [PDW              -1:0],
  parameter type          pstrb_t       = logic [PSTRBW           -1:0]
)(
  // AHB command information
  output paddr_t                    o_apb_paddr,
  output pdata_t                    o_apb_pwdata,
  output logic                      o_apb_pwrite,
  // JTAG command synchronization
  // The following signal shall toggle between one command and the next.
  output logic                      o_transaction_id,
  // Response to JTAG
  input  pdata_t                    i_apb_prdata,
  input  logic                      i_apb_error,
  input  logic                      i_jtag_ready
);

`ifndef TARGET_DFT
`ifndef TESSENT
  always_comb o_apb_paddr              = '0;
  always_comb o_apb_pwdata             = '0;
  always_comb o_apb_pwrite             = '0;
  always_comb o_transaction_id         = '0;
`endif // ! TESSENT
`endif // ! TARGET_DFT

endmodule
`endif  // AXE_JTAG_TO_APB_TDR_CORE_SV
