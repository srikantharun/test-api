// =============================================================================================================
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                                *** //
// *** Description : This class contains the object members of AW, W Channel to store the txns for    *** //
//                   data comparision, & other misc features                                              *** //
// =============================================================================================================
class aw_channel_obj #(bit[`INT_WIDTH-1:0] AXI_ADDR_WIDTH=40,
                       bit[`INT_WIDTH-1:0] AXI_ID_WIDTH=8);
  
  // ===========================================================================================================
  // AW Channel signal declarations 
  // ===========================================================================================================
  bit [AXI_ADDR_WIDTH-1  : 0]     awaddr; 
  bit [AXI_ID_WIDTH-1    : 0]     awid;
  axi_burst_t                     awburst;
  axi_size_t                      awsize;
  axi_cache_t                     awcache;
  axi_len_t                       awlen;
  axi_prot_t                      awprot;
  bit                             awlock;
  bit                             awready;
  bit                             awvalid;
  // ===========================================================================================================
  // Misc signal declarations 
  // ===========================================================================================================
  bit [`INT_WIDTH-1         : 0] num_bytes;
  bit [`INT_WIDTH-1         : 0] burst_len;
  bit [`INT_WIDTH-1         : 0] total_bytes_transferred;
  bit [`INT_WIDTH-1         : 0] total_bytes_requested;
  real                           txn_req_start_time;
  real                           txn_req_end_time;
  real                           bandwidth;

endclass : aw_channel_obj
