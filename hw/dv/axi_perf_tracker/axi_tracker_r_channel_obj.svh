// =============================================================================================================
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                                *** //
// *** Description : This class contains the object members of R Channel to store the txns for            *** //
//                   data comparision, & other misc features                                              *** //
// =============================================================================================================
class r_channel_obj #(bit[`INT_WIDTH-1:0] AXI_ID_WIDTH=8, 
                      bit[`INT_WIDTH-1:0] AXI_DATA_WIDTH=512);
  
  // ===========================================================================================================
  // R Channel signal declarations 
  // ===========================================================================================================
  bit [AXI_ID_WIDTH-1      : 0]  rid;
  bit [AXI_DATA_WIDTH-1    : 0]  rdata [$];
  axi_resp_t                     rresp;
  bit                            rlast;
  bit                            rready;
  bit                            rvalid;
  // ===========================================================================================================
  // Misc signal declarations 
  // ===========================================================================================================
  bit [`INT_WIDTH-1         : 0] rd_stall_mst, rd_stall_slv, data_num;
  bit [`INT_WIDTH-1         : 0] rd_beat_count, txn_id;
  bit [`INT_WIDTH-1         : 0] num_bytes;
  bit [`INT_WIDTH-1         : 0] burst_len;
  bit [`INT_WIDTH-1         : 0] total_bytes_transferred;
  real                           txn_req_start_time;
  real                           txn_req_end_time;
  real                           bandwidth;
  bit                            outstanding_burst;

endclass : r_channel_obj
