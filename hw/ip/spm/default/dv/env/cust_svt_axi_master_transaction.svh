
/**
 * Abstract:
 * This file defines a class that represents a customized AXI Master
 * transaction.  This class extends the AXI VIP's svt_axi_master_transaction
 * class.  It adds pre-defined distribution constraints for transaction
 * weighting, and adds constraints on burst type.
 * It implements the necessary virtual functions like copy(), compare(), etc...
 * by using `uvm_object_utils macro.
 *
 * The transaction instance replaces the default master sequencer's transaction
 * object, which is shown in tests/ts.basic_random_test.sv
 */

`ifndef GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
`define GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV

class cust_svt_axi_master_transaction extends svt_axi_master_transaction;

    int burst_type_fixed_wt = 20;
    int burst_type_incr_wt  = 30;
    int burst_type_wrap_wt  = 40;

    int num_busy_cycles_zero_wt = 500;
    int num_busy_cycles_non_zero_wt = 1;

    // Declare user-defined constraints
    constraint master_constraints {

        burst_type dist {svt_axi_transaction::FIXED := burst_type_fixed_wt,
                    svt_axi_transaction::INCR  := burst_type_incr_wt,
                    svt_axi_transaction::WRAP  := burst_type_wrap_wt
                    };
    }

  /** UVM Object Utility macro */
    `uvm_object_utils_begin(cust_svt_axi_master_transaction)
        `uvm_field_int(burst_type_fixed_wt,UVM_ALL_ON)
        `uvm_field_int(burst_type_incr_wt ,UVM_ALL_ON)
        `uvm_field_int(burst_type_wrap_wt ,UVM_ALL_ON)
    `uvm_object_utils_end

    /** Class Constructor */
    function new (string name = "cust_svt_axi_master_transaction");
        super.new(name);
    endfunction: new

endclass: cust_svt_axi_master_transaction

`endif // GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
