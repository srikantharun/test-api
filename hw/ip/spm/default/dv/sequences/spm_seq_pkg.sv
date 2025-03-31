
// SPM SEQ package
package spm_seq_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"


    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import spm_uvm_pkg::*;
    import axe_uvm_resource_allocator_pkg::*;


    //seq
    `include "axi_simple_reset_sequence.svh"
    `include "axi_basic_sequence.svh"
    `include "axi_wr_rd_sequence.svh"
    `include "axi_wr_rd_ecc_sequence.svh"
    `include "axi_wr_rd_sequencial_sequence.svh"



endpackage
