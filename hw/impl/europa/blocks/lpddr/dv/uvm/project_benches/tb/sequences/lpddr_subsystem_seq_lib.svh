//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_seq_lib.sv
//------------------------------------------------------------------------------
// Description : This file is the include file for all the sequences used in
//               LPDDR Subsystem Verification Environment.
//------------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_SEQ_LIB_SVH
`define LPDDR_SUBSYSTEM_SEQ_LIB_SVH

 `include "lpddr_subsystem_base_virtual_seq.sv"
 `include "lpddr_subsystem_axi_scheduler_seq.sv"
 `include "lpddr_subsystem_init_seq.sv"
 `include "test_seq/lpddr_subsystem_sanity_test_seq.sv"
 `include "test_seq/lpddr_subsystem_mode_reg_rd_wr_test_seq.sv"
 `include "test_seq/lpddr_subsystem_axi_input_traffic_handling_test_seq.sv"
 `include "test_seq/lpddr_low_power_test_seq.sv"
 `include "test_seq/lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq.sv"
 `include "test_seq/lpddr_subsystem_error_handling_test_seq.sv"
 `include "test_seq/lpddr_subsystem_link_ecc_inline_ecc_test_seq.sv"
 `include "test_seq/lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq.sv"
 `include "test_seq/lpddr_subsystem_page_policy_test_seq.sv"
 `include "test_seq/lpddr_subsystem_page_match_test_seq.sv"
 `include "test_seq/lpddr_subsystem_write_to_read_switching_test_seq.sv"
 `include "test_seq/lpddr_subsystem_lpddr5_masked_write_test_seq.sv"
 `include "test_seq/lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq.sv"
 `include "test_seq/lpddr_management_test_seq.sv"
 //`include "test_seq/lpddr_performance_test_seq.sv"
 `include "test_seq/lpddr_subsystem_addr_translation_test_seq.sv"
`endif //LPDDR_SUBSYSTEM_SEQ_LIB_SVH
