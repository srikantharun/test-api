
package decoder_uvm_pkg;
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;
  import allegro_codec_pkg::*;

  //`include "decoder_if.sv"

  `include "decoder_scoreboard.svh"
  `include "decoder_env.svh"

  `include "decoder_env.sv"
  `include "decoder_scoreboard.sv"
endpackage: decoder_uvm_pkg

