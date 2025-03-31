// #define _subentity
////////////////////////////////////////////////////////////////////////////////
//
//       This confidential and proprietary software may be used only
//     as authorized by a licensing agreement from Synopsys Inc.
//     In the event of publication, the following notice is applicable:
//
//                    (C) COPYRIGHT 2006 - 2023 SYNOPSYS INC.
//                           ALL RIGHTS RESERVED
//
//       The entire notice above must be reproduced on all authorized
//     copies.
//
// AUTHOR:    Reto Zimmermann	Sept. 15, 2006
//
// VERSION:   Simulation Architecture
//
// DesignWare_version: 24a0ad61
// DesignWare_release: U-2022.12-DWBB_202212.5
//
////////////////////////////////////////////////////////////////////////////////

//-----------------------------------------------------------------------------------
//
// ABSTRACT:  Priority Coder
//
// MODIFIED:
//           RJK - 04/26/2023  Move return value assignment inside translate_off/on
//                             region. (STAR 4760257)
//--------------------------------------------------------------------------
function [a_width-1:0] DWF_pricod;

  // synopsys map_to_operator PRICOD_UNS_OP
  // synopsys return_port_name COD

  input [a_width-1:0]  A;
  reg   [a_width-1:0] cod;

  reg done;
  integer i;

  begin
    // synopsys translate_off
    done = 0;
    // initialize to "000..."
    cod = {a_width{1'b0}};
    for (i = a_width-1; (done == 0) && (i >= 0); i = i-1) begin
      // find first '1'
      if (A[i] == 1'b1) begin
        cod[i] = 1'b1;
        done = 1;  // stop when first '1' found
      end
      // otherwise find first 'x'
      else if (A[i] === 1'bx) begin
        cod = {a_width{1'bx}};
        done = 1;  // stop when first 'x' found
      end
    end
  
    DWF_pricod = cod;
    // synopsys translate_on
  end
endfunction // DWF_pricod
