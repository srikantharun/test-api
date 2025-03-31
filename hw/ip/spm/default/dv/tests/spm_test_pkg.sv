// SPM TEST package
package spm_test_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"


    import svt_uvm_pkg::*;
    import spm_uvm_pkg::*;
    import spm_seq_pkg::*;
    import svt_axi_uvm_pkg::*;
    import axe_uvm_resource_allocator_pkg::*;


    // Tests
    `include "spm_base_test.svh"
    `include "spm_basic_test.svh"
    `include "spm_ecc_full_test.svh"
    `include "spm_singles_wr_test.svh"
    `include "spm_mem_banking_test.svh"
    `include "spm_multi_wr_test.svh"
    `include "spm_multi_seq_wr_test.svh"
    `include "spm_one_transaction_test.svh"
    `include "spm_back_to_back_test.svh"
    `include "spm_long_bursts_test.svh"
    `include "spm_rw_overlap_test.svh"
    `include "spm_partials_wr_test.svh"
    `include "spm_unaligned_full_test.svh"
    `include "spm_unaligned_partials_test.svh"
    `include "spm_back_pressure_test.svh"

endpackage
