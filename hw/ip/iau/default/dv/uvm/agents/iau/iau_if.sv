`ifndef IAU_IF
`define IAU_IF

interface iau_if (input clk);
  import iau_common_pkg::*;
  wire reset_an_i;
  wire irq_o;
  wire [OBS_W-1:0] obs_o;
  wire [CID_W-1:0] cid_i;
  wire [BLOCK_ID_W-1:0] block_id_i;
  bit scb_icdf_exec_done;
  shortint exec_count;
 
  clocking mon @(posedge clk);
    input reset_an_i;
    input irq_o;
    input obs_o;
    input cid_i;
    input block_id_i;
  endclocking

endinterface

`endif

