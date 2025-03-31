// =============================================================================================================
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                                *** //
// *** Description : This class contains the object members of AR Channel to store the txns for           *** //
//                   data comparision, & other misc features                                              *** //
// =============================================================================================================
class ar_channel_obj #(bit[`INT_WIDTH-1:0] AXI_ADDR_WIDTH=40,
                       bit[`INT_WIDTH-1:0] AXI_ID_WIDTH=8);
  
  // ===========================================================================================================
  // AR Channel signal declarations 
  // ===========================================================================================================
  bit [AXI_ADDR_WIDTH-1  : 0]    araddr; 
  bit [AXI_ID_WIDTH-1    : 0]    arid;
  axi_burst_t                    arburst;
  axi_size_t                     arsize;
  axi_cache_t                    arcache;
  axi_len_t                      arlen;
  axi_prot_t                     arprot;
  bit                            arlock;
  bit                            arready;
  bit                            arvalid;
  // ===========================================================================================================
  // Misc signal declarations 
  // ===========================================================================================================
  bit [`INT_WIDTH-1         : 0] num_bytes, ar_stall_slv;
  bit [`INT_WIDTH-1         : 0] burst_len, txn_id;
  bit [`INT_WIDTH-1         : 0] total_bytes_req;
  real                           txn_req_start_time;
  real                           txn_req_end_time;
  real                           bandwidth;

endclass : ar_channel_obj
