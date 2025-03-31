
/**
 * Abstract:
 * This file defines a class that represents a customized AXI Master
 * transaction.  This class extends the AXI VIP's svt_axi_master_transaction
 * class.  It adds pre-defined distribution constraints for transaction
 * weighting, and adds constraints.
 */
`ifndef GUARD_AI_CORE_TOP_CUST_SVT_AXI_MASTER_TRANSACTION
`define GUARD_AI_CORE_TOP_CUST_SVT_AXI_MASTER_TRANSACTION

class ai_core_top_cust_svt_axi_master_transaction extends svt_axi_master_transaction;

  int burst_type_fixed_wt = 20;
  int burst_type_incr_wt  = 30;
  int burst_type_wrap_wt  = 40;

  // Declare user-defined constraints
  constraint master_constraints {
    // addr,burst_length, burst_type, atomic_type, cache_type,
    // data_user,resp_user
    //addr inside {[0:36'hF_FFFF_FFFF]};
      cache_type  == 0;
      atomic_type == 0;
      prot_type   == 0;
       !(addr inside {[36'h0000_0000:36'h0000_FFFF],[36'h0011_0000:36'h001F_FFFF],[36'h0023_0000:36'h002F_FFFF],[36'h0034_0000:36'h007F_FFFF],[36'h0084_0000:36'h008F_FFFF],[36'h0090_8000:36'h009F_FFFF],[36'h00A1_0000:36'h00FF_FFFF],[36'h0102_0000:36'h010F_FFFF],[36'h0104_0000:36'h01FF_FFFF],[36'h0280_0000:36'h03FF_FFFF],[36'h0446_0000:36'h07FF_FFFF],[36'h0A00_0000:36'h0FFF_FFFF],
                     [36'h1012_0000:36'h1021_FFFF],[36'h2012_0000:36'h2021_FFFF],[36'h3012_0000:36'h3021_FFFF], [36'h4012_0000:36'h4021_FFFF], //RESERVED 1
                     [36'h1024_0000:36'h103F_FFFF],[36'h2024_0000:36'h203F_FFFF],[36'h3024_0000:36'h303F_FFFF], [36'h4024_0000:36'h403F_FFFF], //RESERVED 2
                     [36'h1080_8000:36'h1083_FFFF],[36'h2080_8000:36'h2083_FFFF],[36'h3080_8000:36'h3083_FFFF], [36'h4080_8000:36'h4083_FFFFF], //RESERVED MEM
                     [36'h1080_8000:36'h1083_FFFF],[36'h2080_8000:36'h2083_FFFF],[36'h3080_8000:36'h3083_FFFF], [36'h4080_8000:36'h4083_FFFFF], //RESERVED alignment
                     [36'h1091_0000:36'h17FF_FFFF],[36'h2091_0000:36'h27FF_FFFF],[36'h3091_0000:36'h37FF_FFFF],[36'h4091_0000:36'h47FF_FFFF],   //reserved ai core spm
                     [36'h1840_0000:36'h1fff_ffff],[36'h2840_0000:36'h2fff_ffff],[36'h3840_0000:36'h3fff_ffff],[36'h4840_0000:36'h4fff_ffff],   //Reserved ai core mem
                     [36'h5000_0000:36'h6fff_ffff],      //Reserved ai cores 4-6
                     [36'h7101_0000:36'h7fff_ffff],      //Reserved ddr0
                     [36'h1_0000_0000:36'h1_7fff_ffff],  //Reserved
                     [36'h1_c000_0000:36'h8_7fff_ffff],  //Reserved PCIe
                     [36'hc_0000_0000:36'hf_ffff_ffff],  //Reserved ai core 4-16
                     [36'h1001_83ff:36'h1001_ffff],[36'h1002_83ff:36'h1002_ffff],[36'h1003_83ff:36'h1003_ffff],[36'h1004_83ff:36'h1004_ffff],[36'h1005_83ff:36'h1005_ffff],[36'h1006_83ff:36'h1006_ffff],[36'h1007_83ff:36'h1007_ffff],[36'h1009_81ff:36'h1009_ffff],[36'h100b_81ff:36'h100b_ffff],[36'h100c_8fff:36'h100c_ffff],[36'h100d_bfff:36'h100d_ffff],[36'h100e_81ff:36'h100e_ffff],[36'h100f_8fff:36'h100f_ffff],[ 36'h100a7fff:36'h100affff], //descr_mem_outside_demote_aicore0
                     [36'h2001_83ff:36'h2001_ffff],[36'h2002_83ff:36'h2002_ffff],[36'h2003_83ff:36'h2003_ffff],[36'h2004_83ff:36'h2004_ffff],[36'h2005_83ff:36'h2005_ffff],[36'h2006_83ff:36'h2006_ffff],[36'h2007_83ff:36'h2007_ffff],[36'h2009_81ff:36'h2009_ffff],[36'h200b_81ff:36'h200b_ffff],[36'h200c_8fff:36'h200c_ffff],[36'h200d_bfff:36'h200d_ffff],[36'h200e_81ff:36'h200e_ffff],[36'h200f_8fff:36'h200f_ffff],[ 36'h200a7fff:36'h200affff], //descr_mem_outside_demote_aicore1
                     [36'h3001_83ff:36'h3001_ffff],[36'h3002_83ff:36'h3002_ffff],[36'h3003_83ff:36'h3003_ffff],[36'h3004_83ff:36'h3004_ffff],[36'h3005_83ff:36'h3005_ffff],[36'h3006_83ff:36'h3006_ffff],[36'h3007_83ff:36'h3007_ffff],[36'h3009_81ff:36'h3009_ffff],[36'h300b_81ff:36'h300b_ffff],[36'h300c_8fff:36'h300c_ffff],[36'h300d_bfff:36'h300d_ffff],[36'h300e_81ff:36'h300e_ffff],[36'h300f_8fff:36'h300f_ffff],[ 36'h300a7fff:36'h300affff], //descr_mem_outside_demote_aicore2
                     [36'h4001_83ff:36'h4001_ffff],[36'h4002_83ff:36'h4002_ffff],[36'h4003_83ff:36'h4003_ffff],[36'h4004_83ff:36'h4004_ffff],[36'h4005_83ff:36'h4005_ffff],[36'h4006_83ff:36'h4006_ffff],[36'h4007_83ff:36'h4007_ffff],[36'h4009_81ff:36'h4009_ffff],[36'h400b_81ff:36'h400b_ffff],[36'h400c_8fff:36'h400c_ffff],[36'h400d_bfff:36'h400d_ffff],[36'h400e_81ff:36'h400e_ffff],[36'h400f_8fff:36'h400f_ffff],[ 36'h400a7fff:36'h400affff], //descr_mem_outside_demote_aicore3
                     [36'h2800_0000:36'h283f_ffff],[36'h3800_0000:36'h383f_ffff],[36'h4800_000:36'h483f_ffff], //Check how can initialise the other core mem
                     [36'h1008_c000:36'h1008_ffff]});    //trace unit out of range //ISSUE-2322

      addr  dist { [36'h0:36'hFFF_FFFF]              :/ 10,
                        [36'h1000_0000:36'h107F_FFFF]        :/ 80,  // Ai core 1-4 // Exclude the memory to return x propogation because of memory is not initialize in protocol check test
                        [36'h2000_0000:36'h4FFF_FFFF]        :/ 40  // Ai core 1-4
                        //[36'h5000_0000:36'h6FFF_FFFF]        :/ 20,  // Ai core 5-6
                        //[36'h7000_0000:36'hF_FFFF_FFFF]      :/ 10
                       };
    // AWLEN/ARLEN
   // burst_length  dist {
   //                     6'd0          :/ 2,
   //                    [6'd1 : 6'd62] :/ 10,
   //                     6'd63         :/ 2
   //                    };
   // // AWSIZE/ARSIZE
   // burst_size  dist { 3'h0         :/ 2,
   //                   [3'h1 : 3'h5] :/ 10,
   //                    3'h6         :/ 2
   //                    };
   // // AWBURST/ARBURST
    burst_type    dist {svt_axi_transaction::FIXED := burst_type_fixed_wt,
                        svt_axi_transaction::INCR  := burst_type_incr_wt,
                        svt_axi_transaction::WRAP  := burst_type_wrap_wt
                       };
   // atomic_type   dist {['h0 :'h0]  :/ 1
   //                    };
   // cache_type       dist {'h0 :/ 1,
   //                        'h1 :/ 0
   //                 };
   // //data_user    dist {['h0 : 'h0]  :/ 1
   // //                     };
   // resp_user    dist {['h0 : 'h0]  :/ 1
   //                      };
   // // AWPROT/ARPROT => 010
   // prot_type    dist {['h2 : 'h2]  :/ 1
   //                      };
    //cache_type       dist {'h0 :/ 1,
    //                       'h1 :/ 0
    //                };
  }

  /** UVM Object Utility macro */
  `uvm_object_utils_begin(ai_core_top_cust_svt_axi_master_transaction)
     `uvm_field_int(burst_type_fixed_wt,UVM_ALL_ON)
     `uvm_field_int(burst_type_incr_wt ,UVM_ALL_ON)
     `uvm_field_int(burst_type_wrap_wt ,UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new (string name = "ai_core_top_cust_svt_axi_master_transaction");
    super.new(name);
  endfunction: new

endclass: ai_core_top_cust_svt_axi_master_transaction

`endif // GUARD_AI_CORE_TOP_CUST_SVT_AXI_MASTER_TRANSACTION
