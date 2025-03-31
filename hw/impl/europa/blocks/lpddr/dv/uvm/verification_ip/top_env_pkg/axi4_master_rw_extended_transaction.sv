//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : axi4_master_rw_extended_transaction.sv
// Unit        : axi4_master_rw_extended_transaction
//------------------------------------------------------------------------------
// Description : This file contains 
//------------------------------------------------------------------------------

`ifndef AXI4_MASTER_RW_EXTENDED_TRANSACTION
`define AXI4_MASTER_RW_EXTENDED_TRANSACTION

class axi4_master_rw_extended_transaction extends axi_trans_t;

  //UVM Factory Registration
  `uvm_object_utils_begin(axi4_master_rw_extended_transaction)
  `uvm_object_utils_end

  //--------------------------------------------------------------------------------
  // FUNCTION    : new
  // Arguments   : String name - Name of the Object.
  // Description : Constructor for axi4_master_rw_extended_transaction class object.
  //--------------------------------------------------------------------------------
  function new(string name = "axi4_master_rw_extended_transaction");
    super.new(name);
  endfunction : new

  rand axi4_lpr_hpr_e low_or_high_priority;
  rand axi4_write_traffic_e normal_or_variable_priority;
  rand bit received_vpr_trans_timeout;

  //Selection for AXI USER Signals as given below:
  //awpoison and arpoison signals definition will be considered as addr_user_data[0].

endclass : axi4_master_rw_extended_transaction
`endif //AXI4_MASTER_RW_EXTENDED_TRANSACTION
