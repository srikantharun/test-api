// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:  Simple 1D testcase : ALigned START and END. INC=2. TRANSIZE=512 WIDTH (64-bytes). 128 bytes as 512-byte bus
// Owner: Sultan Khan

`ifndef GUARD_DMA_IP_1D_CH0_UNALIGN_ALIGN_XINC2_TSIZE6_133B_CONT_TEST_SV
`define GUARD_DMA_IP_1D_CH0_UNALIGN_ALIGN_XINC2_TSIZE6_133B_CONT_TEST_SV

class dma_ip_1D_ch0_unalign_align_xinc2_tsize6_133b_cont_test extends dma_ip_rand_transfers_test;

 
  // ------------------------------------------------------------
  // Constraints, which can be redefined in the extended tests
  // Defined here (even empty ones, which can take any-values) just so we have the constraint names for extended tests
 
  // Whether ADDRESSES are aligned or not
  constraint addr_alignment_c {
    src_addr_alignment == UNALIGNED;
    dst_addr_alignment == UNALIGNED;
  }

  // What type of Transfers ot take PLACE
  constraint dma_transfer_type_c {
    transfer_type inside {ONE_D};
  }

  // X-Direction Operation Type
  constraint xtype_c {
    xtype inside {CONTINUE};
  }

  // Address Ranges to be used for SRC/DST Addresses
  constraint addr_start_c {
    src_addr  == 'h1003;   
    dst_addr  == 'h2003;   
  }

  // XINC Selection
  constraint xinc_values_c {
    src_xaddrinc  inside {2};		  
    dst_xaddrinc  inside {2};
  }

  // XBYTESIZE Selection
  constraint xbytesize_values_c {
    src_xbytesize  inside {133};    
    dst_xbytesize  inside {133};
  }

  // TRANSIZE Selection 
  constraint transize_values_c {
    transize inside {6};
  }

  // Number of channels that can be active simultaneously, from 1 to MAX NUM Supported
  constraint num_parallel_channels_active_c {
    channel_selection  inside {0};   // Channel 0 ONLY
  }

  // ------------------------------------------------------------

  /** UVM Component Utility macro */
  `uvm_component_utils(dma_ip_1D_ch0_unalign_align_xinc2_tsize6_133b_cont_test)


  // Class constructor
  function new (string name="dma_ip_1D_ch0_unalign_align_xinc2_tsize6_133b_cont_test", uvm_component parent);
    super.new (name, parent);
    num_of_chans_to_test = 1;     // Only 1 channel to test
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_1D_ch0_unalign_align_xinc2_tsize6_133b_cont_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction


endclass:dma_ip_1D_ch0_unalign_align_xinc2_tsize6_133b_cont_test



`endif // GUARD_DMA_IP_1D_CH0_UNALIGN_ALIGN_XINC2_TSIZE6_133B_CONT_TEST_SV
