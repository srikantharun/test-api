// SYS SPM TEST package
package sys_spm_test_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"


    import svt_uvm_pkg::*;
    import spm_uvm_pkg::*;
    import sys_spm_uvm_pkg::*;
    import spm_seq_pkg::*;
    import svt_axi_uvm_pkg::*;
    import axe_uvm_resource_allocator_pkg::*;
    import spm_seq_pkg::*;


    // Tests
    `include "sys_spm_base_test.svh"
    `include "sys_spm_basic_test.svh"
    `include "sys_spm_multi_seq_test.svh"



endpackage
