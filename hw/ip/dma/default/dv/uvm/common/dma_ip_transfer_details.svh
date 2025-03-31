// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Object defining lines of communication between Stimulus Generating part of the TB and the Checking Part of the DUT. 
//              Check needs to understand what/how each DUT channel is being tested, so it knows what sort of checks to perform.
// Owner: Sultan Khan


`ifndef GUARD_DMA_IP_TRANSFER_DETAILS_SVH
`define GUARD_DMA_IP_TRANSFER_DETAILS_SVH

class dma_ip_transfer_details extends uvm_object;

// --------------------------------------------------------------------
// Types, Members, etc


// --------------------------------------------------------------------
// Information Needed by Checker

int transfer_port_data_width;	                                                                      // DAYA WIDTH of the Transfer Ports
int channels_being_tested;                                                                          // Bit-field Identifies which channel being tested (so bit-0=1 means channel-0)

testing_type_t  type_of_testing[dma_ip_common_pkg::NUM_CHANNELS];  // TYPE of Testing taking place
channel_setup_t channel_setup[dma_ip_common_pkg::NUM_CHANNELS];    // Per-Channel SEtUP Information.  TBD Will become redundant when implement RAL Methods as can collect srtup via mirrrored values

bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0] pre_mem_addr_q[dma_ip_common_pkg::NUM_CHANNELS][$];   // Per-Channel Q. Holds the addresses of the PRELOADED MEM
bit [dma_ip_common_pkg::AXI_S_DATA_WIDTH-1:0] pre_mem_data_q[dma_ip_common_pkg::NUM_CHANNELS][$];   // Per-Channel Q. Holds the DATA      of the PRELOADED MEM

bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0] post_mem_addr_q[dma_ip_common_pkg::NUM_CHANNELS][$];  // Per-Channel Q. Holds the addresses of the POST-SIM MEM (outcome)
bit [dma_ip_common_pkg::AXI_S_DATA_WIDTH-1:0] post_mem_data_q[dma_ip_common_pkg::NUM_CHANNELS][$];  // Per-Channel Q. Holds the DATA      of the POST-SIM MEM (outcome)

axi_transfer_makeup_t   exp_axi_transfer_makeup_q[dma_ip_common_pkg::NUM_CHANNELS][$];  // All AXI-TRANSACTIONS Expected in the DMA Transfers (on a per channel basis)
bit [63:0]              exp_axi_strb_q[dma_ip_common_pkg::NUM_CHANNELS][$];             // For each data-transfer, what the STRB Values expected to be (applicable only for WRITES)

// --------------------------------------------------------------------


  `uvm_object_utils_begin(dma_ip_transfer_details)
  `uvm_object_utils_end

  function new(string name="dma_ip_transfer_details");
      super.new(name);

      transfer_port_data_width	= dma_ip_common_pkg::AXI_S_DATA_WIDTH;		// 512 by default
      channels_being_tested     = '0;                                     // No Channels to be Checked by SCBD, by default (TESTS will define which channels to check)  
      
      foreach (type_of_testing[i]) begin
        type_of_testing[i]      = MODEL_BASED_CSR;
      end

  endfunction : new

endclass : dma_ip_transfer_details

`endif  // GUARD_DMA_IP_TRANSFER_DETAILS_SVH
