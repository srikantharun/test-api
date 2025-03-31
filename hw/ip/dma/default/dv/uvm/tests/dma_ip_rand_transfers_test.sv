// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Testcase designed to generate any DMA transfer Scenario - to cehk normal functionality and corner cases
//   Constraints can be redefined in extended tests, to generate more specific scenarios
//   This test is effectively, the dma_ip_rand_transfers_test with new constraints and a run-phase defined 
// Owner: Sultan Khan

`ifndef GUARD_DMA_IP_RAND_TRANSFERS_TEST_SV
`define GUARD_DMA_IP_RAND_TRANSFERS_TEST_SV

class dma_ip_rand_transfers_test extends dma_ip_base_test;

  `define MAX_NUM_CHANNELS  4

  // ------------------------------------------------------------
  // Control Knob
  int num_of_chans_to_test;
  int dma_data_width = 512;  // Default (but updated based on actual config of AXI_VIPs connected to the DUT's AXI Master Data-Ports)

  // ------------------------------------------------------------
  // TYPEDEF 
  typedef enum {ALIGNED, UNALIGNED} addr_alignment_e;
  typedef enum {ONE_D, TWO_D, LINKED_LIST, DIRECT_ACCESS} dma_transfer_types_e;
  typedef enum bit [3:0] {DISABLE  = 4'b0000, 
                          CONTINUE = 4'b0001, 
                          WRAP     = 4'b0010, 
                          FILL     = 4'b0011} x_direction_op_e;
  
  // ------------------------------------------------------------
  // RAND Members to steer the TEST
  
  rand  addr_alignment_e      src_addr_alignment;
  rand  addr_alignment_e      dst_addr_alignment;
  rand  dma_transfer_types_e  transfer_type;
  rand  x_direction_op_e      xtype;

  rand  bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  src_addr;    // 39:0
  rand  bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  dst_addr;    // 39:0
  rand  bit [15:0]  src_xaddrinc;
  rand  bit [15:0]  dst_xaddrinc;
  rand  bit [31:0]  src_xbytesize;
  rand  bit [31:0]  dst_xbytesize;
  rand  bit [3:0]   transize;
  
  randc int         channel_selection;              // Which channels we program up. So, if (say) only 1 channel to use, can select channel 0,1,2,3
 
  
  // ------------------------------------------------------------
  // Constraints, which can be redefined in the extended tests
  // Defined here (even empty ones, which can take any-values) just so we have the constraint names for extended tests

  // Order of Constraints to be solved
  constraint constraint_order_c {
    solve src_addr_alignment before src_addr;
    solve dst_addr_alignment before dst_addr;
  }

  // What type of Transfers ot take PLACE
  constraint dma_transfer_type_c {
    // transfer_type == 
  }

  // X-Direction Operation Type
  constraint xtype_c {
    // xtype ==
  }

  // Address Ranges to be used for SRC/DST Addresses
  constraint addr_start_c {
    src_addr  inside {[0:'hff_ffff_ffff]};      // 40-bits  TBD Should be distribution, with addr near begin and ends
    dst_addr  inside {[0:'hff_ffff_ffff]};      // 40-bits  TBD Should be distribution, with addr near begin and ends

    (src_addr_alignment ==   ALIGNED) ->  src_addr[1:0] inside {2'b00};
    (src_addr_alignment == UNALIGNED) ->  src_addr[1:0] inside {[2'b01:2'b11]};

    (dst_addr_alignment ==   ALIGNED) ->  dst_addr[1:0] inside {2'b00};
    (dst_addr_alignment == UNALIGNED) ->  dst_addr[1:0] inside {[2'b01:2'b11]};
  }

  // XINC Selection
  constraint xinc_values_c {
    src_xaddrinc  inside {[0:'hffff]};
    dst_xaddrinc  inside {[0:'hffff]};
  }

  // XBYTESIZE Selection
  constraint xbytesize_values_c {
    src_xbytesize  inside {[0:'hffff_ffff]};
    dst_xbytesize  inside {[0:'hffff_ffff]};
  }

  // TRANSIZE Selection - We ONLY support 512 or 64 bits (but assume can be any modulo-2 size)
  constraint transize_values_c {
    (dma_data_width == 8)    ->  transize inside {0};
    (dma_data_width == 16)   ->  transize inside {[0:1]};
    (dma_data_width == 32)   ->  transize inside {[0:2]};
    (dma_data_width == 64)   ->  transize inside {[0:3]};
    (dma_data_width == 128)  ->  transize inside {[0:4]};
    (dma_data_width == 256)  ->  transize inside {[0:5]};
    (dma_data_width == 512)  ->  transize inside {[0:6]};
  }

  // Number of channels that can be active simultaneously, from 1 to MAX NUM Supported
  constraint num_parallel_channels_active_c {
    channel_selection            inside {[0:`MAX_NUM_CHANNELS-1]};   // Which channel we usefor operation
  }

  // ------------------------------------------------------------

  /** UVM Component Utility macro */
  `uvm_component_utils(dma_ip_rand_transfers_test)


  // Class constructor
  function new (string name="dma_ip_rand_transfers_test", uvm_component parent);
    super.new (name, parent);
    num_of_chans_to_test = `MAX_NUM_CHANNELS;
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_rand_transfers_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  // ------------------------------------------------------------

  // Start of simulation phase 
  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
    
    // Rand Members are ZERO for TESTs. So, invoke randomization before tests begin, so they have sensible values (as per constraints)
    // Do this n-times, as we have a RANDC on channel-selection (which needs to be consumed entirely)
    for (int channel_idx=0; channel_idx < num_of_chans_to_test; channel_idx++) begin
      if (!this.randomize()) `uvm_error(get_full_name(), $sformatf("[START_OF_SIMULATION] FAILED to initially randomize RAND Members of TEST"))
    end
  endfunction: start_of_simulation_phase;

  // ------------------------------------------------------------
  extern virtual task  setup_dma_channel_transfers();
    
  // ------------------------------------------------------------


  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

    `uvm_info(get_full_name(), $sformatf("START : DMA IP RAND TRANSFER Test"), UVM_LOW)

    setup_dma_channel_transfers();

    `uvm_info(get_full_name(), $sformatf("END : DMA IP RAND TRANSFER Test"), UVM_LOW)
    phase.drop_objection(this);
  endtask

  // ------------------------------------------------------------

endclass:dma_ip_rand_transfers_test





// -----------------------------------------------------------------------------------------
// Task to SETUP DMA Channel Registers, and enable DMA Engine, based on Constraint Settings
// Based on Constraint 
task  dma_ip_rand_transfers_test::setup_dma_channel_transfers();
  int  channels_being_tested[$];
  bit  timeout_valid;

  // Grab size of Transfer Port DATA-WIDTHS, so that TANSIZE selection can be generated correctly (via a control knob) 
  dma_data_width = dma_ip_common_pkg::AXI_S_DATA_WIDTH; 

  // For each of the specified Channels, randomize the necessary members and program up that channel
  for (int channel_idx=0; channel_idx < num_of_chans_to_test; channel_idx++) begin
    if (!this.randomize()) `uvm_error(get_full_name(), $sformatf("[RUN] FAILED to randomize RAND Members of TEST"))
    
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : CHANNEL_IDX=%0d. channel_selection = %0d", channel_idx, channel_selection), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : src_addr_alignment=%s", src_addr_alignment.name()), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : dst_addr_alignment=%s", dst_addr_alignment.name()), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : transfer_type =%s", transfer_type.name), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : xtype         =%s", xtype), UVM_LOW) 

    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : src_addr = 'h%010h", src_addr), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : dst_addr = 'h%010h", dst_addr), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : src_xaddrinc = 'h%04h",  src_xaddrinc), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : dst_xaddrinc = 'h%04h",  dst_xaddrinc), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : src_xbytesize = 'h%08h",  src_xbytesize), UVM_LOW) 
    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : dst_xbytesize = 'h%08h",  dst_xbytesize), UVM_LOW) 

    `uvm_info(get_full_name(), $sformatf("RAND_TRANSFERS : transize = 'h%01h",  transize), UVM_LOW) 

    // Log the channels being tested, as we need to enable them all together later
    channels_being_tested.push_back(channel_selection);

    // Assuming Each channel can be setup to operate independantly upon others
    // Eg while 1 channel may be doing 1D, the other may be doing 2D
    case (transfer_type)
      ONE_D         :
        begin
        
          `uvm_info(get_full_name(), $sformatf("Setting up DMA for 1D-Transfers on Channel-%01d",  channel_selection), UVM_LOW) 

          // Preload Memory, well beyond the range involved in the DMA transfer, bearing in mind address memory limits 
          // TBD how do we know which Data Port is going to be exercised ?
          
          
          if (src_addr inside {['h0 : 'h1000]}) 
            slvmem_bkdr_preload_range(0, "RAND",  'h0, 'h2000);
          else if  (src_addr inside {[axi_vip_cfg.axi_slave_mem_addr_max - 'h1000 : axi_vip_cfg.axi_slave_mem_addr_max]})
            slvmem_bkdr_preload_range(0, "RAND",  axi_vip_cfg.axi_slave_mem_addr_max - 'h2000, axi_vip_cfg.axi_slave_mem_addr_max); 
          else 
            slvmem_bkdr_preload_range(0, "RAND",  src_addr, src_addr + 'h1000); 
 
          // Global DMA Register Accesses
          // ----------------------
          DMA_REG_READ  (DMA_CH_COMMON_MODE, 0, rdata);     // Channel Independent Register
          rdata[channel_selection] = 1'b1;                  // Set specified channel to operate on CMD FOrmat
          DMA_REG_WRITE (DMA_CH_COMMON_MODE, 0, rdata);
          
          // Channel Specific Registers
          // --------------------------
          DMA_REG_WRITE (DMA_CH_SRC_ADDR     , channel_selection, src_addr);
          DMA_REG_WRITE (DMA_CH_DST_ADDR     , channel_selection, dst_addr);

          DMA_REG_WRITE (DMA_CH_XADDRINC     , channel_selection, {16'h0000, dst_xaddrinc, 16'h0000, src_xaddrinc}); 
          DMA_REG_WRITE (DMA_CH_XBYTESIZE    , channel_selection, {dst_xbytesize, src_xbytesize}); 

          // TBD Cater for different BUS Widths here. Not just 512-Data bits
          // TBD - NO Magic Numbers in bits and bit-slices
          DMA_REG_READ  (DMA_CH_CFG          , channel_selection, rdata  );      
          rdata[7:4] = xtype;
          rdata[3:0] = transize;
          DMA_REG_WRITE (DMA_CH_CFG          , channel_selection, rdata  );      
          
          // TBD - To be Implemented
          wdata = '0;
          DMA_REG_WRITE (DMA_CH_TRAN_CFG     , channel_selection, wdata);

          // TBD - To implement RESUME, PAUSE< STOP etc 
          // TBD NO Magic Numbers for Fields
          DMA_REG_READ (DMA_CH_CTRL          , channel_selection, rdata);  
          rdata[31]    = 1'b0;		    // MMU EN
          rdata[30:29] = 2'b00;		    // LL_MS
          rdata[28:27] = 2'b00;	 	    // DST_MS
          rdata[26:25] = 2'b00;       // SRC_MS
          rdata[24:19] = 6'b11_1111;  // DST_OSR_LMT=64   // TBD - changeable ? 
          rdata[18:13] = 6'b11_1111;  // SRC_OSR_LMT=64   // TBD - changeable ?
          rdata[12]    = 1'b0;        // Reserved
          rdata[11]    = 1'b0;        // ECC_ERR_CLR
          rdata[10]    = 1'b0;        // ERR_ERR_EN
          rdata[9]     = 1'b0;        // INTERRUPT_CLR
          rdata[8]     = 1'b0;        // INTERRUPT_EN
          rdata[7:6]   = 2'b00;       // Reserved
          rdata[5]     = 1'b0;        // RESUME
          rdata[4]     = 1'b0;        // PUASE
          rdata[3]     = 1'b0;        // STOP
          rdata[2]     = 1'b0;        // DISABLE
          rdata[1]     = 1'b0;        // CLEAR
          rdata[0]     = 1'b0;        // ENABLE  (DMA Operation not to be enable yet)
          DMA_REG_WRITE (DMA_CH_CTRL         , channel_selection, rdata);
          
        end
      TWO_D         : 
        begin
          // TBD
          `uvm_error(get_full_name(), $sformatf("TBD - NO DMA SETUPS for 2-D Transfers yet in place"))
        end
      LINKED_LIST   : 
        begin
          // TBD
          `uvm_error(get_full_name(), $sformatf("TBD - NO DMA SETUPS for LINKED_LIST Based Transfers yet in place"))
        end
      DIRECT_ACCESS : 
        begin
          // TBD
          `uvm_error(get_full_name(), $sformatf("TBD - NO DMA SETUPS for DIRECT ACCESS Transfers yet in place"))
        end
    endcase
   
  end
      
  // All Channels to be tested now SETUP (but not enabled). Check Their IDLE States Before we enable them 1-by-1 
  // ALL Channels to be IDLE irrespective of which ones being tested and how many being tested   
  DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);     // Channel Independent Register
  for (int i=0; i< `MAX_NUM_CHANNELS; i++) begin
    if (rdata[i] != 1'b0) begin
      `uvm_error(get_full_name(), $sformatf("Expected Channel-%01d to be IDLE before START of Actual Tests [BUSY STATUS = %01d]", i, rdata[i]))
    end
  end
  
  // Enable all the Required Channels we are testing - in random order
  channels_being_tested.shuffle();
  `uvm_info(get_full_name(), $sformatf("Number of Channels Being Tested=%01d",  channels_being_tested.size()), UVM_LOW) 

  foreach (channels_being_tested[i]) begin
    int channel_id;
    
    channel_id = channels_being_tested[i];
    DMA_REG_READ (DMA_CH_CTRL,  channel_id, rdata);
    rdata[0]  = 1'b1;   // ENABLE
    DMA_REG_WRITE (DMA_CH_CTRL, channel_id, rdata);
    `uvm_info(get_full_name(), $sformatf("Enabled Channel=%01d for Testing", channel_id), UVM_LOW)
  end    
  
  // Allow things to proceed before checking any STATUS Registers
  clk_vif.await_rising_edge(10);
  

  // Check for all Channels to become IDLE.
  // TBD And service any interrupts here.
  fork
    // ------------------------------------
    // THREAD 1 - TIMEOUT if all channels never become all IDLE (then need to understand why)
    begin
      timeout_valid = 1'b0;
      clk_vif.await_rising_edge(100000);  // 100000 * 1.25ns = 125us
      timeout_valid = 1'b1;
    end
    // ------------------------------------
    // THREAD 2 - Preriodically check for all Channels IDLE
    begin
      DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);     // Channel Independent Register
      while (rdata[`MAX_NUM_CHANNELS-1:0] != 0) begin
        clk_vif.await_rising_edge(100);
        DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);
      end
    end
    // ------------------------------------
  join_any
  
  if (timeout_valid) 
    `uvm_fatal(get_full_name(), $sformatf("TIMEOUT Waiting for ALL DMA Channels to become IDLE"))
  else
    `uvm_info(get_full_name(), $sformatf("ALL DMA Channels are now IDLE"), UVM_LOW)
  

  
  


 
  // Check for DMA IDLE
  // TBD - clock waits
  

endtask : setup_dma_channel_transfers




`endif // GUARD_DMA_IP_RAND_TRANSFERS_TEST_SV
