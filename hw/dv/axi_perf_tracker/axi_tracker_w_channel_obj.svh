// =============================================================================================================
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                                *** //
// *** Description : This class contains the object members of W Channel to store the txns for            *** //
//                   data comparision, & other misc features                                              *** //
// =============================================================================================================
class w_channel_obj #(bit[`INT_WIDTH-1:0] AXI_DATA_WIDTH=512);
  
  // ===========================================================================================================
  // W Channel signal declarations 
  // ===========================================================================================================
  bit [AXI_DATA_WIDTH-1    : 0]  wdata [$];
  bit [(AXI_DATA_WIDTH/8)-1: 0]  wstrb [$]; 
  bit                            wlast;
  bit                            wready;
  bit                            wvalid;
  // ===========================================================================================================
  // Misc signal declarations 
  // ===========================================================================================================
  bit [`INT_WIDTH-1         : 0] wr_beat_count;
  bit [`INT_WIDTH-1         : 0] wr_stall_slv;
  bit [`INT_WIDTH-1         : 0] wr_stall_mst;
  bit [`INT_WIDTH-1         : 0] zero_wstrb;
  bit [`INT_WIDTH-1         : 0] valid_wstrb;
  bit [`INT_WIDTH-1         : 0] num_bytes;
  bit [`INT_WIDTH-1         : 0] burst_len;
  bit [`INT_WIDTH-1         : 0] total_bytes_transferred;
  real                           txn_req_start_time;
  real                           txn_req_end_time;
  real                           bandwidth;
  bit                            outstanding_burst;
  
endclass : w_channel_obj
