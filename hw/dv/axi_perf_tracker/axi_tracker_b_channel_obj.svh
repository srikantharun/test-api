// =============================================================================================================
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                                *** //
// *** Description : This class contains the object members of B Channel to store the txns for            *** //
//                   data comparision, & other misc features                                              *** //
// =============================================================================================================
class b_channel_obj #(bit[`INT_WIDTH-1:0] AXI_ID_WIDTH=8);

  // ===========================================================================================================
  // B Channel signal declarations 
  // ===========================================================================================================
  bit [AXI_ID_WIDTH-1      : 0]  bid;
  axi_resp_t                     bresp;
  bit                            bready;
  bit                            bvalid;
  // ===========================================================================================================
  // Misc signal declarations 
  // ===========================================================================================================
  bit [`INT_WIDTH-1         : 0] b_stall_mst, b_stall_slv;
  bit [`INT_WIDTH-1         : 0] num_bytes;
  bit [`INT_WIDTH-1         : 0] burst_len;
  bit [`INT_WIDTH-1         : 0] total_bytes_transferred;
  real                           txn_req_start_time;
  real                           txn_req_end_time;
  real                           bandwidth;

endclass : b_channel_obj
