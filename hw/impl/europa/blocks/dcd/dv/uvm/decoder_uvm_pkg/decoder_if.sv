import uvm_pkg::*;

`include "uvm_macros.svh"
//`include "svt_apb_if.svi"
//`include "svt_axi_if.svi"

interface decoder_if ();

  svt_axi_if axi_if   ();
  // master_if[0] = mcu
  // master_if[1] = core0
  // master_if[2] = core1
  // master_if[3] = postproc
  //
  svt_apb_if apb_if   ();


endinterface
