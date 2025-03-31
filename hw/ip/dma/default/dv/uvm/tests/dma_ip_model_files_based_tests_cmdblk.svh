// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Testcase Designed to make use of DMA Model Files - but using CMD Blocks for DUT Setup and Operation
// Owner: Sultan Khan


`ifndef GUARD_DMA_IP_MODEL_FILES_BASED_TESTS_CMDBLK_SV
`define GUARD_DMA_IP_MODEL_FILES_BASED_TESTS_CMDBLK_SV

class dma_ip_model_files_based_tests_cmdblk extends dma_ip_model_files_based_tests;

  // ------------------------------------------------------------
  // Redefined Constraints
  
  constraint cmdblk_max_num_c {
    cmdblk_max_num == 1;           // Multiples of 2
  }
  // ------------------------------------------------------------

  /** UVM Component Utility macro */
  `uvm_component_utils(dma_ip_model_files_based_tests_cmdblk)


  // Class constructor
  function new (string name="dma_ip_model_files_based_tests_cmdblk", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_model_files_based_tests_cmdblk", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);

    // Means of Register Setups
    reg_setup_via_csr      = 0;
    reg_setup_via_cmdblk   = 1;
    reg_setup_via_linklist = 0;
  endfunction

  // ------------------------------------------------------------

  // Start of simulation phase 
  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);


  endfunction: start_of_simulation_phase;

  // ------------------------------------------------------------
  extern virtual task  test_dma_channels();
  extern virtual task  cmdblk_corrupt_csr_regs(int channel_idx);
  // ------------------------------------------------------------

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // ------------------------------------------------------------

endclass:dma_ip_model_files_based_tests_cmdblk


// -----------------------------------------------------------------------------------------
// Task to determine which DMA channel to verify (if SINGLE_CHANNEL testing)
//                  or ALL DMA CHannels          (if MULTI-CHANNEL testing, using the same DMA file)
// 
// Re-coded from parent class, as specific to CMD Based Testing


task  dma_ip_model_files_based_tests_cmdblk::test_dma_channels();
bit  [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  memory_segment;         // Available target-Space / Number of CMDBLKs
bit  [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  chan_mem_offset;        // Memory Offset for the channel beign used (within the target memory)
bit  [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  cmdblk_mem_offset;      // Memory Offset for the CMDBLK  being used (within the target memory)
 
int  num_of_dma_channels;
int  multiplier_q[$];                                           

  
   `uvm_info(get_full_name(), $sformatf("Using CMD BLOCK Based Setup and Transfers]"), UVM_LOW)

  if (multi_channel_testing == 1'b0) begin
    // Single channel testing. 
    // Based on the number of CMDBLKs that need to be sent, we split the given PRE-POST memory and adjust the addresses of the transactions accordingly
    
    if (cmdblk_max_num == 1) begin
      setup_dma_channel(channel_selection, 0);                   // SINGLE Channel-Testing. Setup the Channel to be Tested (Chan-Base-ADDR=0, so no addr offsets applied) 
      chk_chan_enabled(channel_selection);                       // Check channel has started transfers before checking END-OF-Transfer (ALL channels IDLE)
    end
    else begin
      memory_segment = '1;
      memory_segment = (memory_segment/cmdblk_max_num)+1;
      `uvm_info(get_full_name(), $sformatf("Calculated Memory Segment=%010h for each CMDBLK [Num of CMDBLKS to Generate=%0d]", memory_segment, cmdblk_max_num), UVM_LOW)
      
      // Work out which memory_segment (base address) each CMDBLK will operate upon - allocate different areas per run-time seeds
      // Do this by 
      //   1) Loading-up Values into a QUEUE, based on max CMDBLKs to issue. So for 4 CMDBLKS to issue, we load up values 0,1,2,3
      //   2) Then shuffle that QUEUEs contents, so the numbers are in random order
      //   3) Define the base address for that CMDblk based on the values popped from the (shuffled) Queue. 
      // So base addresses will be randomly selected for each channel
      
      for (int i=0; i < cmdblk_max_num; i++) begin
        multiplier_q.push_back(i);
      end
      multiplier_q.shuffle();  
      `uvm_info(get_full_name(), $sformatf("CMDBLK Entries in multiplier_q = %0d", multiplier_q.size()), UVM_LOW)
      
      for (int cmdblk_idx=0; cmdblk_idx < cmdblk_max_num; cmdblk_idx++) begin
        `uvm_info(get_full_name(), $sformatf("CMDBLK cmdblk_idx = %0d", cmdblk_idx), UVM_LOW)
        cmdblk_mem_offset = multiplier_q.pop_front() * memory_segment;
        `uvm_info(get_full_name(), $sformatf("Channel-%0d CMDBLK-%0d Base-Address Allocated is %010h", channel_selection, cmdblk_idx, cmdblk_mem_offset), UVM_LOW)
        
        // Determine if each channel uses different (randomized) SRC/DST DMA PORTs for each channel. Or the SAME ONES for each channel
        // When user_defined_portsel = 1 then SRC_MS and DST_MS have been defined by user. Take those values for each channel (So all channels use the same SRC/DST MS values)
        // BUT when user_defined_portsel =0, no user values are defined. So take random values for each channel (so each channel operates on different SRC/DST ports)
        if (user_defined_portsel == 1'b0) begin
          if (!randomize(src_portsel)) `uvm_error(get_full_name(), $sformatf("CMDBLK SINGLE_CHAN Testing : FAILED to randomize src_portsel"))
          if (!randomize(dst_portsel)) `uvm_error(get_full_name(), $sformatf("CMDBLK SINGLE_CHAN Testing : FAILED to randomize dst_portsel"))
        end

        setup_dma_channel(channel_selection, cmdblk_mem_offset);  // SINGLE Channel-Testing. Setup the Channel to be Tested with correct addr offsets for the CMDBLK in question
        chk_chan_enabled(channel_selection);                      // Check channel has started transfers before checking END-OF-Transfer (ALL channels IDLE)
        
        // Generate delays between CMDBLKs
        if (!randomize(cmdblk_dly)) `uvm_error(get_full_name(), $sformatf("CMDBLK SINGLE_CHAN Testing : FAILED to randomize cmdblk_dly"))
        `uvm_info(get_full_name(), $sformatf("PRE  CMDBLK cmdblk_dly = %0d", cmdblk_dly), UVM_LOW)
        clk_vif.await_rising_edge(cmdblk_dly);
        `uvm_info(get_full_name(), $sformatf("DONE CMDBLK cmdblk_dly = %0d", cmdblk_dly), UVM_LOW)
        
      end
    end
     
  end
  else begin

    // MULTI-CHANNEL Testing Enabled. 
    // As we are using the same DMA FILEs then for each channel we need to allocate certain regions of the target memory where the channels operate
    // So divide the target memory into regions (based on the number of channels that we support) and then allocate which memory region a channel should operate under.
    // Arrange such that each channel can operate under different regions of the divided memory (not always the same)
    
    // Work out Memry Segment based on target memory available and num of DMA channels supported
    num_of_dma_channels = dma_ip_common_pkg::NUM_CHANNELS;
    memory_segment = '1;
    memory_segment = (memory_segment/num_of_dma_channels)+1;
    `uvm_info(get_full_name(), $sformatf("Calculated Memory Segment=%010h for each DMA Channel [Num of DMA Channels Supported=%0d]", memory_segment, num_of_dma_channels), UVM_LOW)
    
    // Work out which memory_segment (base address) each supported channel will operate upon - allocate different areas per run-time seeds
    // Do this by 
    //   1) Loading-up Values into a QUEUE, based on channel-IDs. So for 4 channess supported, we load up values 0,1,2,3
    //   2) Then shuffle that QUEUEs contents, so the numbers are in random order
    //   3) Define the base address for a channel based on the values popped from the (shuffledd) Queue. 
    // So base addresses will be randomly selected for each channel
    
    for (int i=0; i < num_of_dma_channels; i++) begin
      multiplier_q.push_back(i);
    end
    multiplier_q.shuffle();  
    
    for (int chan_idx=0; chan_idx < num_of_dma_channels; chan_idx++) begin
      chan_mem_offset = multiplier_q.pop_front() * memory_segment;
      `uvm_info(get_full_name(), $sformatf("Channel-%0d Base-Address Allocated is %010h", chan_idx, chan_mem_offset), UVM_LOW)
      
      // Determine if each channel uses different (randomized) SRC/DST DMA PORTs for each channel. Or the SAME ONES for each channel
      // When user_defined_portsel = 1 then SRC_MS and DST_MS have been defined by user. Take those values for each channel (So all channels use the same SRC/DST MS values)
      // BUT when user_defined_portsel =0, no user values are defined. So take random values for each channel (so each channel operates on different SRC/DST ports)
      if (user_defined_portsel == 1'b0) begin
        if (!randomize(src_portsel)) `uvm_error(get_full_name(), $sformatf("MULTI_CHAN Testing : FAILED to randomize src_portsel"))
        if (!randomize(dst_portsel)) `uvm_error(get_full_name(), $sformatf("MULTI_CHAN Testing : FAILED to randomize dst_portsel"))
      end

      setup_dma_channel(chan_idx, chan_mem_offset);  // MULTI Channel-Testing. Setup each Channel to be tested with different Chan-Base-ADDR (so diff addr offsets applied) 
      chk_chan_enabled(chan_idx);                    // Check channel has started transfers before checking END-OF-Transfer (ALL channels IDLE)
    end
    
  end
  
  // Channels are enabled by virtue of the CH_CTRL value within the CMD-BLK
  wait_all_channels_idle();  // END OF TEST, when all channels are IDLE (if only 1 channel being tested, the other channels are already IDLE)

endtask : test_dma_channels


// -----------------------------------------------------------------------------------------
// Corrupt Key DMA Registers, via Register Accesses while CMDBLK Based Testing is taking place

task  dma_ip_model_files_based_tests_cmdblk::cmdblk_corrupt_csr_regs(int channel_idx);
  bit [63:0] rand_data;
  int        rand_dly;
  
  `uvm_info(get_full_name(), $sformatf("Generating background writes [corruption] to CSR Registers [during CMDBLK Mode testing]"), UVM_LOW)

  forever begin
    
    if (!std::randomize(rand_data)) `uvm_error(get_full_name(), $sformatf("cmdblk_corrupt_csr_regs : FAILED to randomize rand_data"))
    if (!std::randomize(rand_dly) with {rand_dly inside {[50:500]}; }) 
      `uvm_error(get_full_name(), $sformatf("cmdblk_corrupt_csr_regs : FAILED to randomize rand_dly"))
    
    clk_vif.await_rising_edge(rand_dly);
    `uvm_info(get_full_name(), $sformatf("Corrupting CSR Registers [during CMDBLK Mode testing]"), UVM_LOW)
    
    // TBD  - reinstate
  //randcase
  //  10 : DMA_REG_WRITE (DMA_CH_SRC_ADDR     , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_DST_ADDR     , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_CFG          , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_XBYTESIZE    , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_XADDRINC     , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_YROWSIZE     , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_YADDRSTRIDE  , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_TRAN_CFG     , channel_idx, 0, rand_data);
  //  10 : DMA_REG_WRITE (DMA_CH_CTRL         , channel_idx, 0, rand_data);
  //endcase
  end

endtask : cmdblk_corrupt_csr_regs


`endif // GUARD_DMA_IP_MODEL_FILES_BASED_TESTS_CMDBLK_SV
