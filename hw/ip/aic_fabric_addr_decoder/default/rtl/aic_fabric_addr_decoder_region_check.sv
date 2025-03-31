// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Address decoder region check, check if address is in the specified region
// Owner: Sander Geursen <sander.geursen@axelera.ai>
//        Luyi <yi.lu@axelera.ai>

`ifndef _AIC_FABRIC_ADDR_DECODER_REGION_CHECK_SV_
`define _AIC_FABRIC_ADDR_DECODER_REGION_CHECK_SV_

module aic_fabric_addr_decoder_region_check #(
  parameter int AW,

  parameter int CORE_ID_LSB,
  parameter int NR_SLAVES,

  parameter bit REGION_IS_CORE,
  parameter bit SKIP_CORE_CHECK_IF_NOT_CORE=1'b0,
  parameter longint REGION_ST_ADDR,
  parameter longint REGION_END_ADDR,
  parameter int REGION_SLAVE_ID,
  localparam int SL_SEL_B = $clog2(NR_SLAVES+1)
) (
  input logic [AW-1:0] addr_in,
  input logic is_this_core,

  output logic hit,
  output logic [SL_SEL_B-1:0] sl_sel
);

  localparam int CHK_AW = (REGION_IS_CORE | SKIP_CORE_CHECK_IF_NOT_CORE) ? CORE_ID_LSB : AW;

  logic [CHK_AW-1:0] addr_in_chk;
  logic [CHK_AW-1:0] region_st_addr;
  logic [CHK_AW-1:0] region_end_addr;
  logic is_this_core_msk;

  always_comb is_this_core_msk = (SKIP_CORE_CHECK_IF_NOT_CORE & ~REGION_IS_CORE) ? 1'b0 : is_this_core;

  // assign wire to region width, as this could remove the core part (if region is core)
  assign region_st_addr = REGION_ST_ADDR;
  assign region_end_addr = REGION_END_ADDR;
  assign addr_in_chk = addr_in[CHK_AW-1:0];

  always_comb begin : pr_region_chk
    // check if address is in the specified region. Only flag valid if the this core is hit, or this region is not in the core
    if ((region_st_addr <= addr_in_chk) &&
        (region_end_addr >= addr_in_chk) &&
        (is_this_core_msk ^ (!REGION_IS_CORE))
    ) begin
      hit = 1'b1;
      sl_sel = REGION_SLAVE_ID;
    end else begin
      hit = 1'b0;
      sl_sel = 0;
    end
  end
endmodule

`endif //_AIC_FABRIC_ADDR_DECODER_REGION_CHECK_SV_
