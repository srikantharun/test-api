// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// Description: Decode APB for soc_mgmt.
//
module soc_mgmt_sycscfg_apb_decode
  import chip_pkg    ::*;
  import axi_pkg     ::*;
  import soc_mgmt_pkg::*;
(
  input  chip_soc_mgmt_syscfg_addr_t  i_paddr    ,
  output logic                        o_pslv_err ,
  output syscfg_apb_mux_idx_t         o_sub_idx
);

//==============================================================================
// RTL
always_comb begin
  case(i_paddr[18:16])
    3'h0    : begin
                o_sub_idx  = 3'd0;
                o_pslv_err = 1'h0;
              end
    3'h1    : begin
                o_sub_idx  = 3'd1;
                o_pslv_err = 1'h0;
              end
    3'h2    : begin
                o_sub_idx  = 3'd2;
                o_pslv_err = 1'h0;
              end
    3'h3    : begin
                o_sub_idx  = 3'd3;
                o_pslv_err = 1'h0;
              end
    3'h4    : begin
                o_sub_idx  = 3'd4;
                o_pslv_err = 1'h0;
              end
    default : begin
                o_sub_idx  = 3'd0; // TODO : Revisit if we should have it as X
                o_pslv_err = 1'h1;
              end
  endcase
end

endmodule
