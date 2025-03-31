
/**
 * Abstract:
 * This file defines a class that represents a customized AXI Master
 * transaction.  This class extends the AXI VIP's svt_axi_master_transaction
 * class.  It adds pre-defined distribution constraints for transaction
 * weighting, and adds constraints.
 */
`ifndef GUARD_AI_CORE_DPU_CUST_SVT_AXI_MASTER_TRANSACTION_SV
`define GUARD_AI_CORE_DPU_CUST_SVT_AXI_MASTER_TRANSACTION_SV

class cust_svt_axi_master_transaction extends svt_axi_master_transaction;

  int burst_type_fixed_wt = 0;
  int burst_type_incr_wt  = 80;
  int burst_type_wrap_wt  = 20;

  // Declare user-defined constraints
  constraint master_constraints {
    // addr,burst_length, burst_type, atomic_type, cache_type,
    // data_user,resp_user
    soft addr          dist {
                        [23'h0:23'h0FFF] :/ 20,
                        ['h8000 : 'hFFFF] :/ 20  
                       };
    // AWLEN/ARLEN
    burst_length  dist {
                        6'd0          :/ 2,
                       [6'd1 : 6'd62] :/ 10,
                        6'd63         :/ 2
                       };
    // AWSIZE/ARSIZE
    burst_size  dist { 3'h0         :/ 2,
                      [3'h1 : 3'h5] :/ 10,
                       3'h6         :/ 2
                       };
    // AWBURST/ARBURST
    burst_type    dist {svt_axi_transaction::FIXED := burst_type_fixed_wt,
                        svt_axi_transaction::INCR  := burst_type_incr_wt,
                        svt_axi_transaction::WRAP  := burst_type_wrap_wt
                       };
    atomic_type   dist {['h0 :'h0]  :/ 1
                       };
    cache_type       dist {'h0 :/ 1,
                           'h1 :/ 0
                    };
    //data_user    dist {['h0 : 'h0]  :/ 1
    //                     };
    resp_user    dist {['h0 : 'h0]  :/ 1
                         };
    // AWPROT/ARPROT => 010
    prot_type   == 2; 
                       
    //cache_type       dist {'h0 :/ 1,
    //                       'h1 :/ 0
    //                };
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

`endif // GUARD_AI_CORE_DPU_CUST_SVT_AXI_MASTER_TRANSACTION_SV
