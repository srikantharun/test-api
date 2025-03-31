
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

    //addr == 8;
    //burst_length == 1;
    //burst_size  == svt_axi_transaction::BURST_SIZE_64BIT;
    //burst_type  == svt_axi_transaction::INCR;
    atomic_type == svt_axi_transaction::NORMAL;
    //addr dist {
    //  28'h0                 :/ 10,
    //  [28'h1 : 28'h3F_FFFE] :/ 80,
    //  28'h3F_FFFF           :/ 10,
    //  [28'h1 : 28'h00_00FE] :/ 80,
    //  28'h00_00FF           :/ 10
    //};
    //// AWLEN/ARLEN
    //burst_length dist {
    //  8'd0           :/ 2,
    //  [8'd1 : 8'd254] :/ 10,
    //  8'd255          :/ 2
    //};
    //// AWSIZE/ARSIZE
    //burst_size dist {
    //  3'h0          :/ 2,
    //  [3'h1 : 3'h3] :/ 10
    //  // 3'h7          :/ 2
    //};
    //// AWBURST/ARBURST
    //burst_type dist {
    //  svt_axi_transaction::FIXED := burst_type_fixed_wt,
    //  svt_axi_transaction::INCR  := burst_type_incr_wt
    //  //svt_axi_transaction::WRAP  := burst_type_wrap_wt
    //};
    //atomic_type dist {['h0 : 'h0] :/ 1};
    //cache_type dist {
    //  'h0 :/ 1,
    //  'h1 :/ 0
    //};
    //data_user    dist {['h0 : 'h0]  :/ 1
    //                     };
    //resp_user dist {['h0 : 'h0] :/ 1};
    // AWPROT/ARPROT => 010
    //prot_type dist {['h2 : 'h2] :/ 1};
    //cache_type       dist {'h0 :/ 1,
    //                       'h1 :/ 0
    //                };
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
