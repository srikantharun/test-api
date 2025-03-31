//------------------------------------------------------------------------------
// Project     : Axelera lpddr Subsystem
// File Name   : lpddr_subsystem_mode_reg_rd_wr_test.sv
// Unit Name   : lpddr_subsystem_mode_reg_rd_wr_test
//------------------------------------------------------------------------------
// Description : This file contains the base virtual sequence for the lpddr
//               Subsystem Verification Environment.
//------------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_MODE_REG_RD_WR_TEST 
`define LPDDR_SUBSYSTEM_MODE_REG_RD_WR_TEST 

class lpddr_subsystem_mode_reg_rd_wr_test extends lpddr_subsystem_base_test;

  `uvm_component_utils(lpddr_subsystem_mode_reg_rd_wr_test)

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments     : string name
  //----------------------------------------------------------------------------
  function new ( string name = "lpddr_subsystem_mode_reg_rd_wr_test",
        uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  function void build_phase ( uvm_phase phase);
    super.build_phase( phase );
    uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_mode_reg_rd_wr_test_seq::type_id::get());
  endfunction: build_phase

endclass : lpddr_subsystem_mode_reg_rd_wr_test

`endif //LPDDR_SUBSYSTEM_MODE_REG_RD_WR_TEST 
