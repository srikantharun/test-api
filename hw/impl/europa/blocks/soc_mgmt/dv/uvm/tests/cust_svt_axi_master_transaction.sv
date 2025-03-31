
/**
 * Abstract:
 * This file defines a class that represents a customized AXI Master
 * transaction.  This class extends the AXI VIP's svt_axi_master_transaction
 * class.  It adds pre-defined distribution constraints for transaction
 * weighting, and adds constraints.
 */
`ifndef GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
`define GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV

class cust_svt_axi_master_transaction extends svt_axi_master_transaction;

  int burst_type_fixed_wt = 10;
  int burst_type_incr_wt  = 80;
  //int burst_type_wrap_wt  = 20;

  // Declare user-defined constraints
  constraint master_constraints {
    // addr,burst_length, burst_type, atomic_type, cache_type,
    // data_user,resp_user
    addr inside {[0:28'hFFF_FFFF]};

    atomic_type == svt_axi_transaction::NORMAL;
  }

  /** UVM Object Utility macro */
  `uvm_object_utils_begin(cust_svt_axi_master_transaction)
    `uvm_field_int(burst_type_fixed_wt, UVM_ALL_ON)
    `uvm_field_int(burst_type_incr_wt, UVM_ALL_ON)
    //`uvm_field_int(burst_type_wrap_wt, UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name = "cust_svt_axi_master_transaction");
    super.new(name);
  endfunction : new

endclass : cust_svt_axi_master_transaction

`endif  // GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
