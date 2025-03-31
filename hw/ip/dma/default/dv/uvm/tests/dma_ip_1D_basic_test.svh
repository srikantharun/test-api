// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : 1D Basic Transfer
// Owner       : Sultan Khan

`ifndef __DMA_IP_1D_BASIC_TEST__
`define __DMA_IP_1D_BASIC_TEST__

class dma_ip_1D_basic_test extends dma_ip_base_test;

  bit [63:0] register_mask;        // Defines Which areas are R/W

  // Registration with the factory
  `uvm_component_utils(dma_ip_1D_basic_test)

  // Class constructor
  function new (string name="dma_ip_1D_basic_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_1D_basic_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
    `uvm_info(get_full_name(), $sformatf("START : DMA IP Register Access Test"), UVM_LOW)

    // ----------------------------------------------------------
    // SETUP for 1D Basic Transfer - On Channel 0 Only
    // ----------------------------------------------------------
    // Transfer 512 bits (DATA-WIDTH can be 512/64-bits)
    //          CONTINUE - copy in continuous manner from src to destination
    //
    // From SRC address 1000 to DEST Address 2000
    //
    // SRC/DEST :  Bytes to handle : 64 bytes in X Dimension
    // No 2D (No Y Dimension)
    // SRC/DEST XADDRINC    = 40
    // SRC/DEST YADDRSTRIDE = 40
    
    // BackDoor Preload Memory from Address 'h1000 (SRC Address), with 64 bytes of random-data that will be transfered to destination 
    // Generate 64-bytes of random memory-data
    
    // Following lines of code can now be replaced with a 1 liner - if random data (not USER-Defined DATA) is required to be preloaded 
    //
    // backdoor_mem_wdata=new[64];
    // foreach (backdoor_mem_wdata[i]) begin
    //  randomize_data(wdata);               // wdata is 64-bits
    //  backdoor_mem_wdata[i] = wdata[7:0];  // Memory arranged as bytes per location
    // end
    // slvmem_backdoor_write_num_byte(0, 'h1000, 64, backdoor_mem_wdata);

    slvmem_bkdr_write_num_randbyte(0, 'h1000, 64);   // Preload MEMORY in AXI_SLAVE AGENT=0. Start Address 'h10000, 64-random bytes from that location
    
    
    
    // Global DMA Register Accesses
    // ----------------------
    DMA_REG_WRITE (DMA_CH_COMMON_MODE, 0, 64'h0000_0000_0000_0001);        // Channel 0 : Transfer Configured with Command Format
    DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);                          // Readt Channel Stats - they should all return IDLE ([3:0] = 0s)
    
    // Channel Specific Registers
    // --------------------------
    DMA_REG_WRITE (DMA_CH_CFG          , 0, 64'h0000_0000_0000_0016);      // WRITE to set 512b transfer size - 1D transfer.
    
    DMA_REG_WRITE (DMA_CH_SRC_ADDR     , 0, 64'h0000_0000_0000_1000);      // WRITE to src addr
    DMA_REG_WRITE (DMA_CH_DST_ADDR     , 0, 64'h0000_0000_0000_2000);      // WRITE to dst addr
    
    DMA_REG_WRITE (DMA_CH_XBYTESIZE    , 0, 64'h0000_0040_0000_0040);      // WRITE 64B transfer
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

endclass:dma_ip_1D_basic_test

`endif	// __DMA_IP_1D_BASIC_TEST__
