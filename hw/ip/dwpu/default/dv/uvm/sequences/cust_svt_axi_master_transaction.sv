
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
  rand bit allow_4k_bound_cross = 0;

  constraint c_sanity_4k_bound_cross {
    soft allow_4k_bound_cross == 0;
  }

  // Declare user-defined constraints
  constraint master_constraints {
    // addr,burst_length, burst_type, atomic_type, cache_type,
    // data_user,resp_user
    addr inside {[0:28'hFFF_FFFF]};

    atomic_type == svt_axi_transaction::NORMAL;
  }

  /** UVM Object Utility macro */
  `uvm_object_utils_begin(cust_svt_axi_master_transaction)
    `uvm_field_int(allow_4k_bound_cross, UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name = "cust_svt_axi_master_transaction");
    super.new(name);
  endfunction : new

  function bit do_is_valid ( bit silent = 0, int kind = RELEVANT  );
    `uvm_info("do_is_valid", $sformatf("Entered on do_is_valid from cust_svt_axi_master_transaction with allow_4k_bound_cross= %0d", allow_4k_bound_cross), UVM_MEDIUM)
    if(allow_4k_bound_cross) begin
      return 1; //return valid situation
    end
    else begin
      do_is_valid = super.do_is_valid(silent, kind);
    end
    return do_is_valid;
  endfunction : do_is_valid

endclass : cust_svt_axi_master_transaction

`endif  // GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
