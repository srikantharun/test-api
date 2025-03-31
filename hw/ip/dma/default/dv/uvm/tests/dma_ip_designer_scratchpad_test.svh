// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   ScratchPad Area for RTL Designer to experiment with DMA Setup and Functionality
//   Independently of verification engineers and checking
// Owner: Sultan Khan

`ifndef __DMA_IP_DESIGNER_SCRATCHPAS_TEST__
`define __DMA_IP_DESIGNER_SCRATCHPAS_TEST__

class dma_ip_designer_scratchpad_test extends dma_ip_base_test;

  bit [63:0] register_mask;        // Defines Which areas are R/W

  // Registration with the factory
  `uvm_component_utils(dma_ip_designer_scratchpad_test)

  // Class constructor
  function new (string name="dma_ip_designer_scratchpad_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_designer_scratchpad_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
    `uvm_info(get_full_name(), $sformatf("START : DMA IP Register Access Test"), UVM_LOW)

    // ----------------------------------------------------------
    // NOTES for RTL Designer : 
    //  Current DMA Registers Defined are located in this file : dma_ip_common_pkg.sv
    //  See Registers under the ENUM TYPE dma_reg_types_enum
    //
    // Register WRITEs all work OK
    // Register Reads Also Work but rdata is not being returned correctly into the testcase (being fixed). ALL OK on the DUT front 
    //
    // To use Register WRITES and READs, use 2 tasks
    //   DMA_REG_WRITE (<REGISTER_NAME>, <CHANNEL_AFFECTED_ELSE_0>, <DMA_INSTANCE_ELSE_0>, <WRITE-DATA>)
    //   DMA_REG_READ  (<REGISTER_NAME>, <CHANNEL_AFFECTED_ELSE_0>, <DMA_INSTANCE_ELSE_0>, <RETURNED-READ-DATA>)
    //
    // Below are examples (remove them if not needed)
    // ----------------------------------------------------------
    
    
    // Test Writes to each Channel
  // for (int chan_idx=0; chan_idx <=3; chan_idx++) begin
  // 
  //   
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_COMMON_MODE              , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_COMMON_STATUS            , chan_idx, wdata); 

  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_CMDBLK_FIFO              , chan_idx, wdata); 

  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_CMDBLK_CTRL              , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_CMDBLK_STATUS            , chan_idx, wdata); 

  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_IRQ_EN                    , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_IRQ_STATUS                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_SWDP_CTRL                 , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_SWDP_STATUS               , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_DP_CTRL                   , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_DP_STATUS                 , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_DBG_OBSERVE               , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_CMDGEN_STATUS             , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_DBG_SCRATCH               , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_DBG_ID                    , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_HW_CAPABILITY             , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_PERF_CTRL                 , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_PERF_STATE                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_PERF_STALL                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_PERF_STALL_IN             , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_PERF_STALL_OUT            , chan_idx, wdata); 

  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_CTRL                    , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_CFG                     , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_SRC_ADDR                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_DST_ADDR                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_XBYTESIZE               , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_YROWSIZE                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_TRAN_CFG                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_XADDRINC                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_YADDRSTRIDE             , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_LINK_DESCR              , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_STATUS                  , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_ERR_INFO                , chan_idx, wdata); 
  //   randomize_data(wdata);  DMA_REG_WRITE(DMA_CH_REQ_BUS_CTRL            , chan_idx, wdata); 

  // end
    
    
    // Test Reads to each Channel
    for (int chan_idx=0; chan_idx <=3; chan_idx++) begin
    
      DMA_REG_READ(DMA_CH_COMMON_MODE              , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_COMMON_STATUS            , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)

//      DMA_REG_READ(DMA_CH_CMDBLK_FIFO              , chan_idx, rdata); 
//      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)

      DMA_REG_READ(DMA_CH_CMDBLK_CTRL              , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_CMDBLK_STATUS            , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)

      DMA_REG_READ(DMA_CH_IRQ_EN                    , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_IRQ_STATUS                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_SWDP_CTRL                 , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_SWDP_STATUS               , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_DP_CTRL                   , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_DP_STATUS                 , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_DBG_OBSERVE               , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_CMDGEN_STATUS             , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_DBG_SCRATCH               , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_DBG_ID                    , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_HW_CAPABILITY             , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_PERF_CTRL                 , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_PERF_STATE                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_PERF_STALL                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_PERF_STALL_IN             , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_PERF_STALL_OUT            , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)

      DMA_REG_READ(DMA_CH_CTRL                    , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_CFG                     , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_SRC_ADDR                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_DST_ADDR                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_XBYTESIZE               , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_YROWSIZE                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_TRAN_CFG                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_XADDRINC                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_YADDRSTRIDE             , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_LINK_DESCR              , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_STATUS                  , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_ERR_INFO                , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)
      DMA_REG_READ(DMA_CH_REQ_BUS_CTRL            , chan_idx, rdata); 
      `uvm_info(get_full_name(),$sformatf("SCRATCHPAD READ-DATA=h%016h", rdata), UVM_LOW)

    end
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    // ----------------------------------------------------------
    // SETUP for 1D Basic Transfer - On Channel 0 Only
    // ----------------------------------------------------------
    // Transfer 64-bytes from SRC ADDR 'h1000 to DEST Addr 'h2000

    // Use BACKDOOR Method to preload SRC Memory with random data - can be used for self-checking in this test
    slvmem_bkdr_write_num_randbyte(0, 'h1000, 64);   // Preload MEMORY in AXI_SLAVE AGENT=0. Start Address 'h10000, 64-random bytes from that location
    slvmem_bkdr_write_num_randbyte(0, 'h2000, 64);   // Preload MEMORY in AXI_SLAVE AGENT=0. Start Address 'h10000, 64-random bytes from that location


    // Global DMA Register Accesses
    // ----------------------
    DMA_REG_WRITE (DMA_CH_COMMON_MODE, 0, 64'h0000_0000_0000_0001);
    DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);
    
    
    
    // Channel Specific Registers
    // --------------------------
    DMA_REG_WRITE (DMA_CH_CFG          , 0, 64'h0000_0000_0000_0016);      // WRITE to set 512b transfer size - 1D transfer.
    
    DMA_REG_WRITE (DMA_CH_SRC_ADDR     , 0, 64'h0000_0000_0000_1000);      // WRITE to src addr
    DMA_REG_WRITE (DMA_CH_DST_ADDR     , 0, 64'h0000_0000_0000_2000);      // WRITE to dst addr
    
    DMA_REG_WRITE (DMA_CH_XBYTESIZE    , 0, 64'h0000_0080_0000_0080);      // WRITE 64B transfer
    DMA_REG_WRITE (DMA_CH_YROWSIZE     , 0, 64'h0000_0000_0000_0000);      // WRITE No 2D striding
    
    DMA_REG_WRITE (DMA_CH_TRAN_CFG     , 0, 64'h0000_0000_0000_0000);      // WRITE set all 0 - not implemented yet
    DMA_REG_WRITE (DMA_CH_XADDRINC     , 0, 64'h0000_0040_0000_0040);      // WRITE to indicated DMA Register - Channel-3. DMA-Instance-0
    DMA_REG_WRITE (DMA_CH_YADDRSTRIDE  , 0, 64'h0000_0040_0000_0040);      // WRITE to indicated DMA Register - Channel-3. DMA-Instance-0
    
    DMA_REG_WRITE (DMA_CH_CTRL         , 0, 64'h0000_0000_01ff_e001);      // WRITE to set max OS to 64 and enable channel
    
    
    DMA_REG_READ (DMA_CH_XADDRINC  , 0, rdata);                        // READ from indicated DMA Register - Channel-0. DMA-Instance-0
    DMA_REG_READ (DMA_CH_XADDRINC  , 1, rdata);                        // READ from indicated DMA Register - Channel-1. DMA-Instance-0
    DMA_REG_READ (DMA_CH_XADDRINC  , 2, rdata);                        // READ from indicated DMA Register - Channel-2. DMA-Instance-0
    DMA_REG_READ (DMA_CH_XADDRINC  , 3, rdata);                        // READ from indicated DMA Register - Channel-3. DMA-Instance-0
    

    // ----------------------------------------------------------
    `uvm_info(get_full_name(), $sformatf("END : DMA IP Register Access Test"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:dma_ip_designer_scratchpad_test

`endif	// __DMA_IP_DESIGNER_SCRATCHPAS_TEST__
