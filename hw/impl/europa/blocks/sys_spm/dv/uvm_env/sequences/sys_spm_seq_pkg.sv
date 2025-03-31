// SYS_SPM SEQ package
package sys_spm_seq_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"


    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import spm_uvm_pkg::*;
    import sys_spm_uvm_pkg::*;


    //seq
    `include "apb_simple_reset_sequence.svh"

endpackage
