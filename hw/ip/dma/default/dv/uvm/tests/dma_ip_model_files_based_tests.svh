// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Testcase Designed to make use of DMA Model Files - Memry Preloading and DUT Setup
// Owner: Sultan Khan

// TBD - How do we setup each channel to do something different, based on Model files.
//     - Will require 4 sets of MODEL files, each representing a channel
//     - Need to exercise all channels together to test Round-Robin Operation 
//
// TBD - if ONLY 1 channel to be tested, the provide means of selecting which channel it will be


`ifndef GUARD_DMA_IP_MODEL_FILES_BASED_TESTS_SV
`define GUARD_DMA_IP_MODEL_FILES_BASED_TESTS_SV

class dma_ip_model_files_based_tests extends dma_ip_base_test;

  localparam MAX_NUM_CHANNELS = dma_ip_common_pkg::NUM_CHANNELS;
  localparam MAX_NUM_PORTS    = dma_ip_common_pkg::NUM_PORTS;

  // ------------------------------------------------------------
  // Control Knob
  bit multi_channel_testing;                             //  0=> SINGLE CHANNEL TESTING (default). 1 => MULTI_CHANNEL Testing (based on the same DMA MODEL files)
  int timeout_all_idle = 1000000;                        //  TIMEOUT polling for all DMA Channels to become IDLE (1000000 * 1.25ns = 1250us)
  int timeout_chan_act = 1000;                           //  TIMEOUT polling for Channel          to become ACTIVE (1000 * 1.25ns = 1250ns)

  bit user_defined_portsel;                              // Identifies if USER has defined SRC_MS/DST_MS via plusargs. Flag relevant ONLY for MULTI Channel Testing

  // Defines means of Register SETUPS (if using CSR, CMD-BLK or Linked_List)
  bit reg_setup_via_csr      = 0;
  bit reg_setup_via_cmdblk   = 0;
  bit reg_setup_via_linklist = 0;

  // ------------------------------------------------------------
  // RAND Members to steer the TEST
  rand int   channel_selection;                           // Defines which channel we use, for SINGLE-Channel Testing.
  int  channels_being_tested_q[$];                        // Holds all the channels that are being tested (which we randmomize to get a random order for channel-enables)

  rand bit [1:0]  src_portsel;                            // Defines which DMA transfer port, we read from (SRC)
  rand bit [1:0]  dst_portsel;                            // Defines which DMA transfer port, we write to  (DST)

  // Related to CMD-BLK Testing Only
  rand int        cmdblk_max_num;                         // Defines number of CLKBLKs to be issued in the test
  rand int        cmdblk_dly;                             // Defines dleay between successive CMDBLKs
  rand bit        cmdblk_token_enb;                       // Enables usage of Token functionalty
  
  // ------------------------------------------------------------

  bit [7:0]       cmd_format_1d      = 8'h0;
  bit [7:0]       cmd_format_1d_full = 8'h1;
  bit [7:0]       cmd_format_2d      = 8'h2;
  bit [7:0]       cmd_format_2d_full = 8'h3;
  bit [7:0]       cmd_format_ll      = 8'h4;

  // ------------------------------------------------------------
  constraint channel_selection_c {
    channel_selection  inside {[0:MAX_NUM_CHANNELS-1]};   // Random Selection of channel to test, for SINGLE-Channel Testing (unless a plusargs is defined)
  }

  constraint dma_mstr_portsel_c {
    src_portsel  inside {[0:MAX_NUM_PORTS-1]};           // Random selection of DMA transfer port for SRC (reads)
    dst_portsel  inside {[0:MAX_NUM_PORTS-1]};           // Random selection of DMA transfer port for DST (writes)
  }

  // ------------------------------------------------------------
  // Related to CMDBLK Testing
  constraint cmdblk_max_num_c {
    cmdblk_max_num == 1;
  }
  
  constraint cmdblk_dly_c {
    cmdblk_dly inside {[1:100]};
  }

  constraint cmdblk_token_enb_c {
    cmdblk_token_enb == 0;
  }

  // ------------------------------------------------------------

  /** UVM Component Utility macro */
  `uvm_component_utils(dma_ip_model_files_based_tests)


  // Class constructor
  function new (string name="dma_ip_model_files_based_tests", uvm_component parent);
    super.new (name, parent);
    
    // Means of Register Setups
    reg_setup_via_csr      = 1;
    reg_setup_via_cmdblk   = 0;
    reg_setup_via_linklist = 0;
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_model_files_based_tests", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  // ------------------------------------------------------------

  // Start of simulation phase 
  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);

    // Rand Members are ZERO for TESTs. So, invoke randomization before tests begin, so they have sensible values (as per constraints)
    if (!this.randomize()) `uvm_error(get_full_name(), $sformatf("[START_OF_SIMULATION] FAILED to initially randomize RAND Members of TEST"))

  endfunction: start_of_simulation_phase;

  // ------------------------------------------------------------
  extern virtual task  setup_dma_channel(int channel_idx, bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0] chan_base_addr);
  extern virtual task  enable_channels();
  extern virtual task  chk_chan_enabled(int channel_idx);
  extern virtual task  wait_all_channels_idle();
  extern virtual task  test_dma_channels();
  extern virtual function string split_using_delimiter_fn(input longint offset, string str,string del, output longint cnt);

  // Tasks to do actual Register SETUPs based on the DMA MODELs cmd.txt file BUT Using different mechanisms
  extern virtual task  setup_csr(int channel_idx, ref dma_ip_transfer_details  test2scbd_details);
  extern virtual task  setup_cmdblk(int channel_idx, ref dma_ip_transfer_details  test2scbd_details);
  extern virtual task  cmdblk_corrupt_csr_regs(int channel_idx);
    
  // ------------------------------------------------------------


  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

    `uvm_info(get_full_name(), $sformatf("START : DMA-MODEL FILES Based Tests"), UVM_LOW)

    // -------------------------------------------------------------------------------
    // Determine if re-using DMA files for MULTI-CHANNEL Testing (DEFAULT is SINGLE CHANNEL Testing)
    if ($test$plusargs("MULTI_CHAN")) begin
      multi_channel_testing = 1'b1;
      `uvm_info("dma_ip_model_files_based_tests", $sformatf("MULTI-CHAN Option Provided (Attempting MULTI-CHANNEL Operation)"), UVM_LOW)
    end

    // For single-channel testing, see if a specific channel needs to be tested (not the randomly chosen one)
    // Likewise for a specific DMA transfer port
    if (multi_channel_testing == 0) begin
      if ($value$plusargs("CHAN=%0d",channel_selection)) begin
        `uvm_info("dma_ip_model_files_based_tests", $sformatf("Ignoring randomly Selected Channel. Using Channel-%0d Instead for Simulations", channel_selection), UVM_LOW)
        if (channel_selection > MAX_NUM_CHANNELS-1) begin
          `uvm_fatal("dma_ip_model_files_based_tests", $sformatf("Channel_Selection=%0d via plusargs cannot exceed number of channels supported [Valid Values : 0-%0d]", channel_selection, MAX_NUM_CHANNELS-1))
        end
      end
      `uvm_info("dma_ip_model_files_based_tests", $sformatf("SINGLE-CHANNEL Operation [On Channel-%0d]", channel_selection), UVM_LOW)
    end

    // Which DMA Transfer Ports to use (applies to SINGLE Channel Testing and MULTI-Channel too)
    // When user options given, then set user_defined_portsel. This will be used in MULTI-Channel testing, to force ALL CHANNELS to use the SAME DMA PORTS
    if ($value$plusargs("SRC_MS=%0d",src_portsel)) begin
      user_defined_portsel = 1'b1;
      `uvm_info("dma_ip_model_files_based_tests", $sformatf("Ignoring randomly Selected Value. Using SRC_MS=%0d Instead for Simulations", src_portsel), UVM_LOW)
      if (src_portsel > MAX_NUM_PORTS-1) begin
        `uvm_fatal("dma_ip_model_files_based_tests", $sformatf("SRC_MS=%0d via plusargs cannot exceed number of DMA-PORTS supported [Valid Values : 0-%0d]", src_portsel, MAX_NUM_PORTS-1))
      end
    end
    if ($value$plusargs("DST_MS=%0d",dst_portsel)) begin
      user_defined_portsel = 1'b1;
      `uvm_info("dma_ip_model_files_based_tests", $sformatf("Ignoring randomly Selected Value. Using DST_MS=%0d Instead for Simulations", dst_portsel), UVM_LOW)
      if (dst_portsel > MAX_NUM_PORTS-1) begin
        `uvm_fatal("dma_ip_model_files_based_tests", $sformatf("DST_MS=%0d via plusargs cannot exceed number of DMA-PORTS supported [Valid Values : 0-%0d]", dst_portsel, MAX_NUM_PORTS-1))
      end
    end
    `uvm_info("dma_ip_model_files_based_tests", $sformatf("DMA TRANSFER PORTS : Using SRC_MS=%0d DST_MS=%0d", src_portsel, dst_portsel), UVM_LOW)

    // -------------------------------------------------------------------------------
    // Actual Testing

    // For CMDBLK Testing - Enable BackGround Corruption of the CSR Registers (via Register accesses)
    if (reg_setup_via_cmdblk) begin
      fork
        cmdblk_corrupt_csr_regs(channel_selection);
      join_none
    end

    // Do DMA Channel Testing using Register Accesses, CMDBLK or Linked-Lists    
    test_dma_channels();

    `uvm_info(get_full_name(), $sformatf("END   : DMA-MODEL FILES Based Tests"), UVM_LOW)

    phase.drop_objection(this);
  endtask

  // ------------------------------------------------------------

endclass:dma_ip_model_files_based_tests


// -----------------------------------------------------------------------------------------
// Function to parse a given string (or file-line) to return the string AFTER N (given offset) delimiting chars (typically spaces)
// COPIED from  https://git.axelera.ai/ai-hw-team/triton/-/blob/main/subip/common/verif/uvm/icdf_common_env/axi_stream_master_file_sequence.sv

function string dma_ip_model_files_based_tests::split_using_delimiter_fn(input longint offset, string str,string del, output longint cnt);
  for (longint i = offset; i < str.len(); i=i+1) begin
    if (str.getc(i) == del) begin
       cnt = i;
       return str.substr(offset,i-1);
    end
  end
endfunction

// -----------------------------------------------------------------------------------------
// Register SETUPS based on the interrogated DMA CMD.txt file details

task  dma_ip_model_files_based_tests::setup_csr(int channel_idx, ref dma_ip_transfer_details  test2scbd_details);

  `uvm_info(get_full_name(), $sformatf("Chan-%0d : Register Setup Using CSR", channel_idx), UVM_INFO)

  // Define what type of testing this channel is doing
  test2scbd_details.type_of_testing[channel_idx]             = dma_ip_common_pkg::MODEL_BASED_CSR;
   
  // Global DMA Register Accesses
  // ----------------------
  DMA_REG_READ  (DMA_CH_COMMON_MODE, 0, rdata);     // Channel Independent Register
  rdata[channel_idx] = 1'b0;                        // Transfer is configured with direct register access (NOT CMD Format)
  DMA_REG_WRITE (DMA_CH_COMMON_MODE, 0, rdata);
  
  // Channel Specific Registers
  // --------------------------
  DMA_REG_WRITE (DMA_CH_SRC_ADDR     , channel_idx, test2scbd_details.channel_setup[channel_idx].src_addr);
  DMA_REG_WRITE (DMA_CH_DST_ADDR     , channel_idx, test2scbd_details.channel_setup[channel_idx].dst_addr);

  // TBD Cater for different BUS Widths here. Not just 512-Data bits
  // TBD - NO Magic Numbers in bits and bit-slices
  DMA_REG_READ  (DMA_CH_CFG          , channel_idx, rdata  );
  rdata[54:51] = test2scbd_details.channel_setup[channel_idx].transform_type;
  rdata[50]    = test2scbd_details.channel_setup[channel_idx].transform_en;
  rdata[47:40] = test2scbd_details.channel_setup[channel_idx].dst_burstlen;
  rdata[39:32] = test2scbd_details.channel_setup[channel_idx].src_burstlen;
  rdata[31:16] = test2scbd_details.channel_setup[channel_idx].fillval;
  rdata[12]    = test2scbd_details.channel_setup[channel_idx].fillval_mode;
  rdata[11:8]  = test2scbd_details.channel_setup[channel_idx].ytype;
  rdata[7:4]   = test2scbd_details.channel_setup[channel_idx].xtype;
  rdata[3:0]   = test2scbd_details.channel_setup[channel_idx].transize;
  DMA_REG_WRITE (DMA_CH_CFG          , channel_idx, rdata  );			

  DMA_REG_WRITE (DMA_CH_XBYTESIZE    , channel_idx, {test2scbd_details.channel_setup[channel_idx].dst_xbytesize, test2scbd_details.channel_setup[channel_idx].src_xbytesize}); 
  DMA_REG_WRITE (DMA_CH_XADDRINC     , channel_idx, {test2scbd_details.channel_setup[channel_idx].dst_xaddrinc, test2scbd_details.channel_setup[channel_idx].src_xaddrinc });  
  DMA_REG_WRITE (DMA_CH_YROWSIZE     , channel_idx, {test2scbd_details.channel_setup[channel_idx].dst_yrowsize, test2scbd_details.channel_setup[channel_idx].src_yrowsize}); 
  DMA_REG_WRITE (DMA_CH_YADDRSTRIDE  , channel_idx, {test2scbd_details.channel_setup[channel_idx].dst_yaddrstride, test2scbd_details.channel_setup[channel_idx].src_yaddrstride });  

  // TBD - To be Implemented
  wdata = '0;
  DMA_REG_WRITE (DMA_CH_TRAN_CFG     , channel_idx, wdata);

  // TBD - To implement RESUME, PAUSE< STOP etc 
  // TBD NO Magic Numbers for Fields
  DMA_REG_READ (DMA_CH_CTRL          , channel_idx, rdata);  
  rdata[31]    = 1'b0;		    // MMU EN
  rdata[30:29] = 2'b00;		    // LL_MS
  rdata[28:27] = test2scbd_details.channel_setup[channel_idx].dst_ms; // DST_MS
  rdata[26:25] = test2scbd_details.channel_setup[channel_idx].src_ms; // SRC_MS
  rdata[24:19] = 6'b11_1111;  // DST_OSR_LMT=64   // TBD - changeable ? 
  rdata[18:13] = 6'b11_1111;  // SRC_OSR_LMT=64   // TBD - changeable ?
  rdata[12]    = 1'b0;        // Reserved
  rdata[11]    = 1'b0;        // ECC_ERR_CLR
  rdata[10]    = 1'b0;        // ERR_ERR_EN
  rdata[9]     = 1'b0;        // INTERRUPT_CLR
  rdata[8]     = 1'b1;        // INTERRUPT_EN
  rdata[7:6]   = 2'b00;       // Reserved
  rdata[5]     = 1'b0;        // RESUME
  rdata[4]     = 1'b0;        // PUASE
  rdata[3]     = 1'b0;        // STOP
  rdata[2]     = 1'b0;        // DISABLE
  rdata[1]     = 1'b0;        // CLEAR
  rdata[0]     = 1'b0;        // ENABLE  (DMA Operation not to be enable yet)
  DMA_REG_WRITE (DMA_CH_CTRL         , channel_idx, rdata);

endtask : setup_csr

// -----------------------------------------------------------------------------------------
// CMDBLK SETUPS based on the interrogated DMA CMD.txt file details

task  dma_ip_model_files_based_tests::setup_cmdblk(int channel_idx, ref dma_ip_transfer_details  test2scbd_details);

 logic [63:0]  cmdblk_makeup[];    // Make uP of the CMDBLK
 int           cmdblk_size;

 // Individual CMDBLK Fields           
 bit [7:0]     cmd_trigger;
 bit [15:0]    cmd_token_cons;
 bit [15:0]    cmd_token_prod;
 bit [7:0]     cmd_config;
 bit [7:0]     cmd_format;
 
 bit [31:0]    cmd_top_token_cons;
 bit [31:0]    cmd_top_token_prod;

 bit [39:0]    cmd_src_addr;
 bit [39:0]    cmd_dst_addr;

 bit [63:0]    cmd_xbytesize;
 bit [63:0]    cmd_xaddrinc;
 bit [63:0]    cmd_yrowsize;
 bit [63:0]    cmd_yaddrstride;
 bit [63:0]    cmd_trans_cfg;
 bit [63:0]    cmd_cfg;
 bit [63:0]    cmd_ctrl;
 
 bit           cmd_type_2D;              // Defines if CMDBLK is 2D (or 1D)
 bit           cmd_type_with_trans_cfg;  // Defines if CMDBLK as TRANS_CFG values

  `uvm_info(get_full_name(), $sformatf("Chan-%0d : Register Setup Using CMD BLOCKS", channel_idx), UVM_INFO)

  // Global DMA Register Accesses
  // ----------------------
  DMA_REG_READ  (DMA_CH_COMMON_MODE, 0, rdata);     // Channel Independent Register
  rdata[channel_idx] = 1'b1;                        // Transfer is configured with CMDBLK Accesses
  DMA_REG_WRITE (DMA_CH_COMMON_MODE, 0, rdata);

  // Enable exec_en in CMDBLK CTRL Register (to allow execution of CMDBLKS)
  // ----------------------
  DMA_REG_READ  (DMA_CH_CMDBLK_CTRL, 0, rdata);     
  rdata[0] = 1'b1;                        
  DMA_REG_WRITE (DMA_CH_CMDBLK_CTRL, 0, rdata);
  

  // CMDBLK Setups
  // -------------
  // Define what type of testing this channel is doing
  test2scbd_details.type_of_testing[channel_idx]             = dma_ip_common_pkg::MODEL_BASED_CMDBLK;

  // Fill-In the CMDBLK Fields
  cmd_trigger        = '0;  // TBD
  cmd_token_cons     = '0;  // TBD
  cmd_token_prod     = '0;  // TBD
  cmd_config         = '0;  // TBD
  cmd_top_token_cons = '0;  // TBD
  cmd_top_token_prod = '0;  // TBD
  cmd_src_addr       = test2scbd_details.channel_setup[channel_idx].src_addr;
  cmd_dst_addr       = test2scbd_details.channel_setup[channel_idx].dst_addr;
  cmd_xbytesize      = {test2scbd_details.channel_setup[channel_idx].dst_xbytesize, test2scbd_details.channel_setup[channel_idx].src_xbytesize};	
  cmd_xaddrinc       = {test2scbd_details.channel_setup[channel_idx].dst_xaddrinc, test2scbd_details.channel_setup[channel_idx].src_xaddrinc };
  cmd_yrowsize       = {test2scbd_details.channel_setup[channel_idx].dst_yrowsize, test2scbd_details.channel_setup[channel_idx].src_yrowsize};
  cmd_yaddrstride    = {test2scbd_details.channel_setup[channel_idx].dst_yaddrstride, test2scbd_details.channel_setup[channel_idx].src_yaddrstride };
  cmd_trans_cfg      = '0;  // TBD
  
  cmd_cfg[54:51]     = test2scbd_details.channel_setup[channel_idx].transform_type;
  cmd_cfg[50]        = test2scbd_details.channel_setup[channel_idx].transform_en;
  cmd_cfg[47:40]     = test2scbd_details.channel_setup[channel_idx].dst_burstlen;
  cmd_cfg[39:32]     = test2scbd_details.channel_setup[channel_idx].src_burstlen;
  cmd_cfg[31:16]     = test2scbd_details.channel_setup[channel_idx].fillval;
  cmd_cfg[12]        = test2scbd_details.channel_setup[channel_idx].fillval_mode;
  cmd_cfg[11:8]      = test2scbd_details.channel_setup[channel_idx].ytype;
  cmd_cfg[7:4]       = test2scbd_details.channel_setup[channel_idx].xtype;
  cmd_cfg[3:0]       = test2scbd_details.channel_setup[channel_idx].transize;

  cmd_ctrl[31]       = 1'b0;		    // MMU EN
  cmd_ctrl[30:29]    = 2'b00;		    // LL_MS
  cmd_ctrl[28:27]    = test2scbd_details.channel_setup[channel_idx].dst_ms; 
  cmd_ctrl[26:25]    = test2scbd_details.channel_setup[channel_idx].src_ms; 
  cmd_ctrl[24:19]    = 6'b11_1111;  // DST_OSR_LMT=64   // TBD - changeable ? 
  cmd_ctrl[18:13]    = 6'b11_1111;  // SRC_OSR_LMT=64   // TBD - changeable ?
  cmd_ctrl[12]       = 1'b0;        // Reserved
  cmd_ctrl[11]       = 1'b0;        // ECC_ERR_CLR
  cmd_ctrl[10]       = 1'b0;        // ERR_ERR_EN
  cmd_ctrl[9]        = 1'b0;        // INTERRUPT_CLR
  cmd_ctrl[8]        = 1'b1;        // INTERRUPT_EN
  cmd_ctrl[7:6]      = 2'b00;       // Reserved
  cmd_ctrl[5]        = 1'b0;        // RESUME
  cmd_ctrl[4]        = 1'b0;        // PUASE
  cmd_ctrl[3]        = 1'b0;        // STOP
  cmd_ctrl[2]        = 1'b0;        // DISABLE
  cmd_ctrl[1]        = 1'b0;        // CLEAR
  cmd_ctrl[0]        = 1'b1;        // ENABLE  (DMA Operation to be enabled)

  // Define Makeup of CMD BLK
  cmd_type_2D             = 1'b0;   // CMDBLK 1D unless otherwise
  cmd_type_with_trans_cfg = 1'b1;   // CMDBLK With TRANS_CFG values, unless otherwise
  
  if ((cmd_yrowsize != 0) || (cmd_yaddrstride != 0))
    cmd_type_2D = 1'b1;             // CMDBLK to be 2D Instead, as have Y values
    
  if (cmd_trans_cfg == 0) begin     // If trans cfg values are ZERO, option to include them in CMDBLK or not
    randcase
      50 : cmd_type_with_trans_cfg = 1'b0;
      50 : cmd_type_with_trans_cfg = 1'b1;  
    endcase
  end
  
  case ({cmd_type_2D, cmd_type_with_trans_cfg})
    2'b00 : begin
              `uvm_info("dma_ip_model_files_based_tests", $sformatf("CMDBLK : Defining 1D Transfer"), UVM_LOW)
              cmd_format       = cmd_format_1d;

              cmdblk_makeup    = new[8];
              cmdblk_makeup[0] = {cmd_config, cmd_format, cmd_token_cons, cmd_token_prod, 8'h00, cmd_trigger};
              cmdblk_makeup[1] = {cmd_top_token_cons, cmd_top_token_prod};
              cmdblk_makeup[2] = {24'h00_0000, cmd_src_addr};
              cmdblk_makeup[3] = {24'h00_0000, cmd_dst_addr};
              cmdblk_makeup[4] = cmd_xbytesize;
              cmdblk_makeup[5] = cmd_xaddrinc;
              cmdblk_makeup[6] = cmd_cfg;
              cmdblk_makeup[7] = cmd_ctrl;
            end
    2'b01 : begin
              `uvm_info("dma_ip_model_files_based_tests", $sformatf("CMDBLK : Defining 1D Transfer - FULL"), UVM_LOW)
              cmd_format       = cmd_format_1d_full;

              cmdblk_makeup    = new[9];
              cmdblk_makeup[0] = {cmd_config, cmd_format, cmd_token_cons, cmd_token_prod, 8'h00, cmd_trigger};
              cmdblk_makeup[1] = {cmd_top_token_cons, cmd_top_token_prod};
              cmdblk_makeup[2] = {24'h00_0000, cmd_src_addr};
              cmdblk_makeup[3] = {24'h00_0000, cmd_dst_addr};
              cmdblk_makeup[4] = cmd_xbytesize;
              cmdblk_makeup[5] = cmd_xaddrinc;
              cmdblk_makeup[6] = cmd_trans_cfg;
              cmdblk_makeup[7] = cmd_cfg;
              cmdblk_makeup[8] = cmd_ctrl;
            end
    2'b10 : begin
              `uvm_info("dma_ip_model_files_based_tests", $sformatf("CMDBLK : Defining 2D Transfer"), UVM_LOW)
              cmd_format       = cmd_format_2d;

              cmdblk_makeup    = new[10];
              cmdblk_makeup[0] = {cmd_config, cmd_format, cmd_token_cons, cmd_token_prod, 8'h00, cmd_trigger};
              cmdblk_makeup[1] = {cmd_top_token_cons, cmd_top_token_prod};
              cmdblk_makeup[2] = {24'h00_0000, cmd_src_addr};
              cmdblk_makeup[3] = {24'h00_0000, cmd_dst_addr};
              cmdblk_makeup[4] = cmd_xbytesize;
              cmdblk_makeup[5] = cmd_xaddrinc;
              cmdblk_makeup[6] = cmd_yrowsize;
              cmdblk_makeup[7] = cmd_yaddrstride;
              cmdblk_makeup[8] = cmd_cfg;
              cmdblk_makeup[9] = cmd_ctrl;
            end
    2'b11 : begin
              `uvm_info("dma_ip_model_files_based_tests", $sformatf("CMDBLK : Defining 2D Transfer - FULL"), UVM_LOW)
              cmd_format       = cmd_format_2d_full;

              cmdblk_makeup    = new[11];
              cmdblk_makeup[0] = {cmd_config, cmd_format, cmd_token_cons, cmd_token_prod, 8'h00, cmd_trigger};
              cmdblk_makeup[1] = {cmd_top_token_cons, cmd_top_token_prod};
              cmdblk_makeup[2] = {24'h00_0000, cmd_src_addr};
              cmdblk_makeup[3] = {24'h00_0000, cmd_dst_addr};
              cmdblk_makeup[4] = cmd_xbytesize;
              cmdblk_makeup[5] = cmd_xaddrinc;
              cmdblk_makeup[6] = cmd_yrowsize;
              cmdblk_makeup[7] = cmd_yaddrstride;
              cmdblk_makeup[8] = cmd_trans_cfg;
              cmdblk_makeup[9] = cmd_cfg;
              cmdblk_makeup[10]= cmd_ctrl;
            end
  endcase
 
  // Load up the CMDBLK into the Channesls FIFO 
  // ----------------------
  // TBD - Change Addresses if possible
  cmdblk_size = cmdblk_makeup.size();
  for (int i=0; i< cmdblk_size; i++) begin
    `uvm_info("dma_ip_model_files_based_tests", $sformatf("CMDBLK : Writing FIFO Entry-%0d : 'h%016h [Channel=%0d]", i, cmdblk_makeup[i], channel_idx), UVM_LOW)
    DMA_REG_WRITE (DMA_CH_CMDBLK_FIFO, 0, cmdblk_makeup[i]);
  end

endtask : setup_cmdblk

// -----------------------------------------------------------------------------------------
// Task to Read DMA MOdels I/O fles, to PRELAOD MEMORY and SETUP DMA Channel Registers for transfers

task  dma_ip_model_files_based_tests::setup_dma_channel(int channel_idx, bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0] chan_base_addr);

  int  test_id = 0;               // Defines which DMA MODEL's test case to use

  // File Handling
  bit status;

  string path_model_files  = "/home/share/europa_dma_stimuli/latest";
  string path_test_area;
  
  int file;
  string filename;
  string filename_pre_mem  = "pre_mem.txt";
  string filename_post_mem = "post_mem.txt";
  string filename_cmd      = "cmd.txt";
  string filename_trans    = "transactions.txt";

  string line;
  int    delim_offset_in;   // For line parsing purposes
  int    delim_offset_out;  // For line parsing purposes
  
  
  // TBD Get rid of Magic Numbers
  
  // To Grab PRE_MEM,txt details - TBD Ranges may change. So need to accommodate this
  bit [63:0]  mem_addr;
  bit [511:0] mem_data;
  bit [63:0]  mem_addr_q[$];
  bit [511:0] mem_data_q[$];
  
  bit [7:0]   mem_data_bytes[];  // Memory Data to access, in byte form
  
  // To Grab CMDs (DUT Setup Values)
  bit [63:0] src_addr;     
  bit [63:0] dst_addr;     
  bit [3:0]  transize;     
  bit [3:0]  xtype;        
  bit [31:0] src_xbytesize;
  bit [31:0] dst_xbytesize;
  bit [31:0] src_xaddrinc;   
  bit [31:0] dst_xaddrinc;   
  bit [3:0]  ytype;        
  bit [31:0] src_yrowsize; 
  bit [31:0] dst_yrowsize; 
  bit [31:0] src_yaddrstride;
  bit [31:0] dst_yaddrstride;
  bit [7:0]  src_burstlen; 
  bit [7:0]  dst_burstlen; 
  bit [15:0] fillval; 
  bit        fillval_mode;   
  bit        transform_en;   
  bit [3:0]  transform_type;

  // These are artifacts of the DMA Model (can be ignored from the cmd.txt file) : #1D, CONTINUE, INC, tran_size
  int          id_ignore;				 // 
  bit  [3:0]   xtype_ignore;     // 
  bit  [15:0]  xaddrinc_ignore;  // 
  bit  [3:0]   transize_ignore;  // 

  // To Grab Transaction Details
  bit [63:0]   strb_value;
  bit [63:0]   strb_value_q[$];

  bit          W_nR;
  bit [39:0]   start_addr;
  bit [39:0]   end_addr;
  bit [8:0]    axid;
  int          burst_len;
  int          burst_size;
  int					 transfer_size;
  int          num_data_transfers;

  dma_ip_common_pkg::axi_transfer_makeup_t  axi_makeup;

  // -------------------------------------------------------------------------------
  // Grab the DMA Model Testcase to use
  if ($value$plusargs("TESTCASE=%0d",test_id))
    `uvm_info("dma_ip_model_files_based_tests", $sformatf("Using test_%0d for Simulations", test_id), UVM_LOW)
  
  // -------------------------------------------------------------------------------
  // Setup Full Path to the DMA Model Test Area, from which to grab the necessary files
  path_test_area = {path_model_files, $sformatf("/test_%0d/", test_id)};
  

  // -------------------------------------------------------------------------------
  // Read the PRE-MEMORY file 
  // -------------------------------------------------------------------------------
  
  filename = {path_test_area, filename_pre_mem};

  `uvm_info("body", $sformatf("Attempting to Open File =%s", filename), UVM_INFO)
  file = $fopen(filename, "r");

  /** Abort if file not found **/
  if (!file) begin
    `uvm_fatal("body", $sformatf("Unable to Open File : %s", filename));
  end

  /** Until the end of the file read the PRE MEM Address and Data Pairs */
  mem_addr_q.delete();
  mem_data_q.delete();
  
  while (!$feof(file)) begin
    status = $fscanf(file, "%b %b", mem_addr, mem_data);
    mem_addr = mem_addr + chan_base_addr;   // Line For MULTI_CHANNEL Testing. (For SINGLE_CHAN_Testing chan_base_addr=0, so exact addr from file is used)
    mem_addr_q.push_back(mem_addr);
    mem_data_q.push_back(mem_data);
    
    // At the Same time, Inform SCBD what the Pre-Loaded Memory is by filling relevant QUEUES with the same details (as part of self-checking)
    test2scbd_details.pre_mem_addr_q[channel_idx].push_back(mem_addr);
    test2scbd_details.pre_mem_data_q[channel_idx].push_back(mem_data);
  end
  $fclose(file);

  // Echo put what was READ-IN from the PRE_MEM TXT file
  for (int i=0; i < mem_addr_q.size(); i++) begin
    `uvm_info("body", $sformatf("PRE_MEM Details Interrogated : ADDR='h%016h  DATA='h%064h", mem_addr_q[i], mem_data_q[i]), UVM_INFO)
  end


  // -------------------------------------------------------------------------------
  // Preload AXI_SLAVE VIP Memory with these data details - byte by byte (using the Memory write_num_byte task)
  // We know which AXI_SLAVE_VIPs MEMORY DATA to program this data into, based on src_portsel (SRC_MS) settings 
  // TBD - what if the data bus is 64-bits and not 512-bits ?
  
  `uvm_info("body", $sformatf("PRE_MEM Details Interrogated : NUM of ITEMS in QUEUE='%0d", mem_addr_q.size()), UVM_INFO)

  for (int i=0; i < mem_addr_q.size(); i++) begin
    int num_bytes;
    
    mem_addr = mem_addr_q[i];   // The Memory Location
    mem_data = mem_data_q[i];   // The Data to be programmed from that location
    num_bytes = 512/8;                   // TBD - This needs to be via a CONFIG for DATA_WIDTHs on AXI_SLAVE_VIPs
    mem_data_bytes = new[num_bytes];
    
    for (int byte_idx=0; byte_idx < num_bytes; byte_idx++) begin
      mem_data_bytes[byte_idx] = mem_data[byte_idx*8 +: 8];
      // `uvm_info("body", $sformatf("PRE_MEM Details : ADDR='h%016h  EXTRACTED_DATA_BYTE[%02d]='h%02h", mem_addr, byte_idx, mem_data_bytes[byte_idx]), UVM_INFO)
    end
    
    // Program correct number of bytes (64bytes for 512-data width) into the relevant AXI_SLAVE VIP Memory
    //
    // VERY IMPORTANT NOTE :
    // 1) When SRC_MS and DST_MS are the same values,  then its the same DMA PORT (AXI_SLAVE VIP) they are accessing. We PRE-LOAD and Chk MEMORY of the same AXI SLAVE VIP
    //
    // 2) When SRC_MS and DST_MS are different values, then different DMA Ports are involved. 1 DMA PORT is used for reads and another DMA Port is used for writes.
    //    In this case, all the AXI SLAVE VIPS need to be preloaded with PRE-MEM DATA, even though only 1 AXI SLAVE VIP wil be checked for POST-MEM Data.
    //    Reason being that the POST-MEM file (and thus checks) doesnt just have the delta-changes expected. But it also has areas of memory which mustnt change (PRE_MEM data + delta changes)
    //    If ONLY the SRC AXI SLAVE VIP is preloaded and the DST AXI-SLAVE VIP is not preloaded as well, then there will be Errors when we do POST-MEM checks as most data will be ZEROs
    // 
    //    Preloading all AXI SLAVE VIPs with PRE-MEM data, for this case, presents no issues as the CHECKER (SCOREBOARD) verifies that the 
    //      a) Channel uses the correct DMA PORT based on the SRC_MS values (It ERRORs otherwise, if the wrong DMA PORT is used)
    //      b) POST-MEM checking is done on the correct AXI SLAVE VIP (so if anything went wrong in transactions across DMA ports) then the Memory checks will fail
    //         Especially if the wrong AXI SLAVE VIP get the data
    
    if (src_portsel == dst_portsel) begin
      slvmem_bkdr_write_num_byte (src_portsel, mem_addr, num_bytes, mem_data_bytes);    // SAME PORT USED for READs/WRITES. So PRE_LOAD DATA into AXI SLAVE VIP given by src_portsel
    end
    else begin
      for (int i=0; i < MAX_NUM_PORTS; i++) begin                                       // DIFF PORTs USED for READs/WRITES. So PRE_LOAD DATA into EVERY available AXI SLAVE VIP
        slvmem_bkdr_write_num_byte (i, mem_addr, num_bytes, mem_data_bytes);
      end
    end
    
  end
  
  // Detail which AXI SLAVE VIP we preloaded. Not done above as there is a loop of pre-loading taking place (so we will get messages for each pre-loading of data)
  if (src_portsel == dst_portsel) begin
    `uvm_info("body", $sformatf("Loaded PRE_MEM Details into AXI_SLAVE-%0d Memory [For CHANNEL-%0d]", src_portsel, channel_idx), UVM_INFO)
  end
  else begin
    `uvm_info("body", $sformatf("Loaded PRE_MEM Details into EACH AXI_SLAVE Memory [For CHANNEL-%0d]", channel_idx), UVM_INFO)
  end


  // -------------------------------------------------------------------------------
  // Read the POST-MEMORY file 
  // -------------------------------------------------------------------------------
  
  filename = {path_test_area, filename_post_mem};

  `uvm_info("body", $sformatf("Attempting to Open File =%s", filename), UVM_INFO)
  file = $fopen(filename, "r");

  /** Abort if file not found **/
  if (!file) begin
    `uvm_fatal("body", $sformatf("Unable to Open File : %s", filename));
  end

  /** Until the end of the file read the PRE MEM Address and Data Pairs */
  mem_addr_q.delete();
  mem_data_q.delete();
  
  while (!$feof(file)) begin
    status = $fscanf(file, "%b %b", mem_addr, mem_data);
    mem_addr = mem_addr + chan_base_addr;   // Line For MULTI_CHANNEL Testing. (For SINGLE_CHAN_Testing chan_base_addr=0, so exact addr from file is used)
    mem_addr_q.push_back(mem_addr);
    mem_data_q.push_back(mem_data);
    
    // At the Same time, Inform SCBD what the POST-Loaded Memory is by filling relevant QUEUES with the same details (as part of self-checking)
    test2scbd_details.post_mem_addr_q[channel_idx].push_back(mem_addr);
    test2scbd_details.post_mem_data_q[channel_idx].push_back(mem_data);
  end
  $fclose(file);

  // Echo put what was READ-IN from the POST_MEM TXT file
  for (int i=0; i < mem_addr_q.size(); i++) begin
    `uvm_info("body", $sformatf("POST_MEM Details Interrogated : ADDR='h%016h  DATA='h%064h", mem_addr_q[i], mem_data_q[i]), UVM_INFO)
  end

  // -------------------------------------------------------------------------------
  // Read the EXPECTED TRANSACTION file 
  // -------------------------------------------------------------------------------
  // NOTE that number of entries on each line varies (x-number of STRB values based on BURST_LEN). BUT 1st few entries are alwasy fixed.
  // So need to interrogate data in a different manner to other files
  //
  // Line-FORMAT
  // WnR START_ADDR END_ADDR TRANSFER_SIZE BURST_LEN STRB0 STRB1 STRBn  (number of STRBs based on BURST_LEN)
   
  
  filename = {path_test_area, filename_trans};

  `uvm_info("body", $sformatf("Attempting to Open File =%s", filename), UVM_INFO)
  file = $fopen(filename, "r");

  /** Abort if file not found **/
  if (!file) begin
    `uvm_fatal("body", $sformatf("Unable to Open File : %s", filename));
  end

  /** Until the end of the file read the Expected AXI Info */
  
  while (!$feof(file)) begin
  
    status = $fgets(line,file);   // Read line from the file

    if (line != "") begin  // In case there is an EMPTY LINE on the very last line (else details are erroneously updated)
    
      // Read the contents of this line using " " as the DELIMITING CHAR. Use OFFSET_IN to navigate the line to the correct CHRS we need (defines DELIM-char Offset)
      // Almost (but not quite) like doing cut -d " " -f1, cut -d " " -f2, cut -d " " -f3 etc on the LINE, but useage is based on last-value of delim_offset_out
      delim_offset_in = 0;
      status = $sscanf(split_using_delimiter_fn(delim_offset_in,line," ",delim_offset_out),"%0d", W_nR);           	delim_offset_in = delim_offset_out+1;   
      status = $sscanf(split_using_delimiter_fn(delim_offset_in,line," ",delim_offset_out),"%0d", start_addr);			delim_offset_in = delim_offset_out+1; 
      status = $sscanf(split_using_delimiter_fn(delim_offset_in,line," ",delim_offset_out),"%0d", end_addr);				delim_offset_in = delim_offset_out+1; 
      status = $sscanf(split_using_delimiter_fn(delim_offset_in,line," ",delim_offset_out),"%0d", transfer_size);		delim_offset_in = delim_offset_out+1; 
      status = $sscanf(split_using_delimiter_fn(delim_offset_in,line," ",delim_offset_out),"%0d", burst_len);				delim_offset_in = delim_offset_out+1;
  
      // Modifications before usage, for MULTI_CHANNEL Testing. (For SINGLE_CHAN_Testing chan_base_addr=0, so exact addr from file is used)
      start_addr = start_addr + chan_base_addr;
      end_addr   = end_addr   + chan_base_addr;
  
      `uvm_info("body", $sformatf("AXI-TRANS Details : W_nR=%1d, start_addr=%010h, end_addr=%010h, transfer_size=%0d,  burst_len=%0d", 
                                   W_nR, start_addr, end_addr, transfer_size, burst_len), UVM_INFO)
  
      // From the BURST_LEN Entry, grab all the subsequent STRB Values (from the same line)
      strb_value_q.delete();                 // Clear the Q of STRB Values
      for (longint i=0; i < burst_len; i++) begin
        status = $sscanf(split_using_delimiter_fn(delim_offset_in,line," ",delim_offset_out),"%0b", strb_value);
        
        if(delim_offset_in >= delim_offset_out) begin
          // Reached END-OF-LINE with no further DELIMIT CHAR. So take the very last item as the STRB value, irrespective of previous assignment
          status = $sscanf(line.substr(delim_offset_in,line.len()-1),"%0b", strb_value);
        end
        else begin
            delim_offset_in = delim_offset_out+1;
        end
        strb_value_q.push_back(strb_value);        // PUSH the interrogated STRB Value onto the relevant QUEUE
      end

      `uvm_info("body", $sformatf("AXI-TRANS STRB Details : Number of STRB Values Interrogated=%0d", strb_value_q.size()), UVM_LOW)
      for (int i=0; i< strb_value_q.size(); i++) begin
        `uvm_info("body", $sformatf("AXI-TRANS STRB Details : STRB[%0d]=%016h", i, strb_value_q[i]), UVM_LOW)
      end

      // transfer_size to ax_size
      case (transfer_size)
        1   : burst_size = 0;
        2   : burst_size = 1;
        4   : burst_size = 2;
        8   : burst_size = 3;
        16  : burst_size = 4;
        32  : burst_size = 5;
        64  : burst_size = 6;
        128 : burst_size = 7;
      endcase

      // Make this AXI MAKEUP available to SCBD here
      axi_makeup.W_nR               = W_nR;              
      axi_makeup.start_addr         = start_addr;        
      axi_makeup.end_addr           = end_addr;          
      axi_makeup.burst_len          = burst_len;         
      axi_makeup.burst_size         = burst_size;     
      axi_makeup.num_data_transfers = burst_len;         // TBD Is it always the case that num_data_transfers = burst_len (or ONLY if transfer_size=64 and DATA_WDITH=64 bytes
      test2scbd_details.exp_axi_transfer_makeup_q[channel_idx].push_back(axi_makeup);
      
      // And the corresponding data-transfer STRB values (which are offloaded based on num_data_transfers of each transaction)
      for (int i=0; i< strb_value_q.size(); i++) begin
        test2scbd_details.exp_axi_strb_q[channel_idx].push_back(strb_value_q[i]);
      end
      
    end
  end
  $fclose(file);

  // -------------------------------------------------------------------------------
  // Read the CMD file - to Determine Register values for the Transfer
  // -------------------------------------------------------------------------------
  // Format of data to be read (single line) is (see DMA MODEL code related to writing out into cmd.txt file)
  // 
  // 19-items
  // src_addr dst_addr transize xtype src_xbytesize dst_xbytesize src_xaddrinc dst_xaddrinc ytype src_yrowsize  dst_yrowsize
  // src_yaddrstride dst_yaddrstride src_burstlen dst_burstlen fillval fillval_mode transform_en transform_type
  //
  // eg
  // 0 01000000000000 0 01 0 0100000000000 01 01 0 0 0 0 0 01000000 01000000 0101 0 0 0
 

  filename = {path_test_area, filename_cmd};

  `uvm_info("body", $sformatf("Attempting to Open File =%s", filename), UVM_INFO)
  file = $fopen(filename, "r");

  /** Abort if file not found **/
  if (!file) begin
    `uvm_fatal("body", $sformatf("Unable to Open File : %s", filename));
  end

  /** Until the end of the file read the PRE MEM Address and Data Pairs */
  while (!$feof(file)) begin
    status = $fscanf(file, "%b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b", 
                            src_addr, dst_addr, transize, xtype, src_xbytesize, dst_xbytesize, src_xaddrinc, dst_xaddrinc,
                            ytype, src_yrowsize, dst_yrowsize, src_yaddrstride, dst_yaddrstride, src_burstlen, dst_burstlen, 
                            fillval, fillval_mode, transform_en, transform_type);
  end
  $fclose(file);

  // Modifications before usage, for MULTI_CHANNEL Testing. (For SINGLE_CHAN_Testing chan_base_addr=0, so exact addr from file is used)
  src_addr = src_addr + chan_base_addr;
  dst_addr = dst_addr + chan_base_addr;

  `uvm_info("body", $sformatf("CMD Details Interrogated : src_addr         ='h%016h", src_addr        ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : dst_addr         ='h%016h", dst_addr        ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : transize         ='h%01h",  transize        ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : xtype            ='h%01h",  xtype           ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : src_xbytesize    ='h%08h",  src_xbytesize   ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : dst_xbytesize    ='h%08h",  dst_xbytesize   ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : src_xaddrinc     ='h%08h",  src_xaddrinc    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : dst_xaddrinc     ='h%08h",  dst_xaddrinc    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : ytype            ='h%01h",  ytype           ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : src_yrowsize     ='h%08h",  src_yrowsize    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : dst_yrowsize     ='h%08h",  dst_yrowsize    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : src_yaddrstride  ='h%08h",  src_yaddrstride ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : dst_yaddrstride  ='h%08h",  dst_yaddrstride ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : src_burstlen     ='h%02h",  src_burstlen    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : dst_burstlen     ='h%02h",  dst_burstlen    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : fillval          ='h%04h",  fillval         ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : fillval_mode     ='h%01b",  fillval_mode    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : transform_en     ='h%01b",  transform_en    ), UVM_INFO)
  `uvm_info("body", $sformatf("CMD Details Interrogated : transform_type   ='h%01h",  transform_type  ), UVM_INFO)
   
   
  // Inform SCBD of the Channel-Setups (in case it requires it for self-checking)
  test2scbd_details.transfer_port_data_width                   = dma_ip_common_pkg::AXI_S_DATA_WIDTH;
  test2scbd_details.channels_being_tested[channel_idx]         = 1'b1;
   
  test2scbd_details.channel_setup[channel_idx].src_addr        = src_addr;
  test2scbd_details.channel_setup[channel_idx].dst_addr        = dst_addr;
  test2scbd_details.channel_setup[channel_idx].transize        = transize;
  test2scbd_details.channel_setup[channel_idx].xtype           = xtype;
  test2scbd_details.channel_setup[channel_idx].src_xbytesize   = src_xbytesize;
  test2scbd_details.channel_setup[channel_idx].dst_xbytesize   = dst_xbytesize;
  test2scbd_details.channel_setup[channel_idx].src_xaddrinc    = src_xaddrinc;
  test2scbd_details.channel_setup[channel_idx].dst_xaddrinc    = dst_xaddrinc;
  test2scbd_details.channel_setup[channel_idx].ytype           = ytype;
  test2scbd_details.channel_setup[channel_idx].src_yrowsize    = src_yrowsize;
  test2scbd_details.channel_setup[channel_idx].dst_yrowsize    = dst_yrowsize;
  test2scbd_details.channel_setup[channel_idx].src_yaddrstride = src_yaddrstride;
  test2scbd_details.channel_setup[channel_idx].dst_yaddrstride = dst_yaddrstride;
  test2scbd_details.channel_setup[channel_idx].src_burstlen    = src_burstlen;
  test2scbd_details.channel_setup[channel_idx].dst_burstlen    = dst_burstlen;
  test2scbd_details.channel_setup[channel_idx].fillval         = fillval;
  test2scbd_details.channel_setup[channel_idx].fillval_mode    = fillval_mode;  
  test2scbd_details.channel_setup[channel_idx].transform_en    = transform_en;  
  test2scbd_details.channel_setup[channel_idx].transform_type  = transform_type;
   
  test2scbd_details.channel_setup[channel_idx].src_ms          = src_portsel;
  test2scbd_details.channel_setup[channel_idx].dst_ms          = dst_portsel;
   
  // -------------------------------------------------------------------------------
  // Program Up the DUT, with the CMD Details and Enable the  Channel
  // -------------------------------------------------------------------------------
  // test2scbd_details.type_of_testing[i] is deined within these tasks (as apply for specific channels)
  if (reg_setup_via_csr)     setup_csr(channel_idx, test2scbd_details);
  if (reg_setup_via_cmdblk)  setup_cmdblk(channel_idx, test2scbd_details);


  channels_being_tested_q.push_back(channel_idx);  // Add channel to be tested into a QUEUE (so we can enable this channel in a randomorder)

endtask : setup_dma_channel

// -----------------------------------------------------------------------------------------
// Task to enable all channels (to be tested), in a random order
// Channel-IDs which are being used for verification are held within the QUEUE : channels_being_tested_q
// This QUEUE is loaded up by setup_dma_channel for every channel being tested

task  dma_ip_model_files_based_tests::enable_channels();

  // All Channels to be tested now SETUP (but not enabled). Check Their IDLE States Before we enable them 1-by-1 
  // ALL Channels to be IDLE irrespective of which ones being tested and how many being tested   
  DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);     // Channel Independent Register
  for (int i=0; i< MAX_NUM_CHANNELS; i++) begin
    if (rdata[i] != 1'b0) begin
      `uvm_error(get_full_name(), $sformatf("Expected Channel-%01d to be IDLE before START of Actual Tests [BUSY STATUS = %01d]", i, rdata[i]))
    end
  end
  
  // Enable all the Required Channels we are testing - in random order
  channels_being_tested_q.shuffle();
  `uvm_info(get_full_name(), $sformatf("Number of Channels Being Tested=%01d",  channels_being_tested_q.size()), UVM_LOW) 

  foreach (channels_being_tested_q[i]) begin
    int channel_id;
  
    channel_id = channels_being_tested_q[i];
    DMA_REG_READ (DMA_CH_CTRL,  channel_id, rdata);
    rdata[0]  = 1'b1;   // ENABLE
    DMA_REG_WRITE (DMA_CH_CTRL, channel_id, rdata);
    `uvm_info(get_full_name(), $sformatf("Enabled Channel=%01d for Testing", channel_id), UVM_LOW)
  end    
  
  // Allow things to proceed before checking any STATUS Registers
  clk_vif.await_rising_edge(10);
  
endtask : enable_channels

// -----------------------------------------------------------------------------------------
// Task to check whether a channel has been enabled (so transfers started) BEFORE we check for all channels to become IDLE (all transfers DONE)
// Suitable for when doing DMA transfers via CMDBLK, as when the last entry into the FIFO is written (to enable DMA transfers), we need to wait for the CMD to
// be offloaded from the FIFO

task  dma_ip_model_files_based_tests::chk_chan_enabled(int channel_idx);
  bit  timeout_valid;

  // Check for Specified Channel to become ACTIVE.
  fork
    // ------------------------------------
    // THREAD 1 - TIMEOUT if specified channel never becomes ACTIVE (then need to understand why)
    begin
      timeout_valid = 1'b0;
      clk_vif.await_rising_edge(timeout_chan_act);
      timeout_valid = 1'b1;
    end
    // ------------------------------------
    // THREAD 2 - Periodically check for channel to become ACTIVE
    begin
      DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);     // Channel Independent Register
      
      while (rdata[channel_idx] == 0) begin               // wait until specified channel becomes ACTIVE 
        clk_vif.await_rising_edge(5);                     // Check with short periods, or danger that DMA transfer over by the 2nd read-check
        DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);
      end
    end
    // ------------------------------------
  join_any
  
  if (timeout_valid) 
    `uvm_fatal(get_full_name(), $sformatf("TIMEOUT Waiting for Chan-%0d to become ACTIVE", channel_idx))
  else
    `uvm_info(get_full_name(), $sformatf("Chan-%0d has become ACTIVE", channel_idx), UVM_LOW)

endtask : chk_chan_enabled

// -----------------------------------------------------------------------------------------
// Task to wait for ALL CHANNELS to become IDLE (if only 1 channel being tested then the others are already IDLE)
// This is used to signify end of test 
// (Checker will determine if it checks when all DMA channels become IDLE, or when each individual channel becomes IDLE)

task  dma_ip_model_files_based_tests::wait_all_channels_idle();
  bit  timeout_valid;

  // Check for all Channels to become IDLE.
  // TBD And service any interrupts here.
  fork
    // ------------------------------------
    // THREAD 1 - TIMEOUT if all channels never become all IDLE (then need to understand why)
    begin
      timeout_valid = 1'b0;
      clk_vif.await_rising_edge(timeout_all_idle);
      timeout_valid = 1'b1;
    end
    // ------------------------------------
    // THREAD 2 - Preriodically check for all Channels IDLE
    begin
      DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);     // Channel Independent Register
      
      if (rdata[MAX_NUM_CHANNELS-1:0] == 0) begin
        // If all channels IDLE immediately after enabling them, then chances are that nothing was transferred (no transfers expected or otherwise)
        clk_vif.await_rising_edge(100);  // Arb value just to see if IRQs are generated (in waves). NO IRQs implies no checking made (SCBD will Error if NO IRQs seen by test-end)   
      end
      else begin
        // At least 1 channel still BUSY. SO POLL Register until all channels IDLE
        while (rdata[MAX_NUM_CHANNELS-1:0] != 0) begin
          clk_vif.await_rising_edge(100);
          DMA_REG_READ  (DMA_CH_COMMON_STATUS, 0, rdata);
        end
      end
    end
    // ------------------------------------
  join_any
  
  if (timeout_valid) 
    `uvm_fatal(get_full_name(), $sformatf("TIMEOUT Waiting for ALL DMA Channels to become IDLE"))
  else
    `uvm_info(get_full_name(), $sformatf("ALL DMA Channels are now IDLE"), UVM_LOW)

  // Additiona Check Following ALL Channels IDLE. Each Channels ENABLE bit should have been self-clearing
  // SO all ENABLES for all channels to be 9
  for (int channel_id=0; channel_id < MAX_NUM_CHANNELS; channel_id++) begin
    DMA_REG_READ (DMA_CH_CTRL,  channel_id, rdata);
    if (rdata[0]  != 1'b0) begin
      `uvm_error(get_full_name(), $sformatf("Chan-%0d : ENABLE-bit remains SET (not SELF-CLEARING) even though channel STATUS is IDLE", channel_id))
    end
  end    

endtask : wait_all_channels_idle

// -----------------------------------------------------------------------------------------
// PLACEHOLDER _ Means to Corrupt CSR Registers during CMDBLK Mode testing

task  dma_ip_model_files_based_tests::cmdblk_corrupt_csr_regs(int channel_idx);

  `uvm_info(get_full_name(), $sformatf("Placeholder - to be defined for CMDBLK Mode testing"), UVM_LOW)

endtask : cmdblk_corrupt_csr_regs

// -----------------------------------------------------------------------------------------
// Task to determine which DMA channel to verify (if SINGLE_CHANNEL testing)
//                  or ALL DMA CHannels          (if MULTI-CHANNEL testing, using the same DMA file)

task  dma_ip_model_files_based_tests::test_dma_channels();
bit  [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  memory_segment;         // Available target-Space / Number of DMA Channels
bit  [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  chan_base_addr;         // Base Address for the channel (within the target memory)
 
int  num_of_dma_channels;
int  multiplier_q[$];                                           

  if (multi_channel_testing == 1'b0) begin
    setup_dma_channel(channel_selection, 0);         // SINGLE Channel-Testing. Setup the Channel to be Tested (Chan-Base-ADDR=0, so no addr offsets applied) 
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
      chan_base_addr = multiplier_q.pop_front() * memory_segment;
      `uvm_info(get_full_name(), $sformatf("Channel-%0d Base-Address Allocated is %010h", chan_idx, chan_base_addr), UVM_LOW)
      
      // Determine if each channel uses different (randomized) SRC/DST DMA PORTs for each channel. Or the SAME ONES for each channel
      // When user_defined_portsel = 1 then SRC_MS and DST_MS have been defined by user. Take those values for each channel (So all channels use the same SRC/DST MS values)
      // BUT when user_defined_portsel =0, no user values are defined. So take random values for each channel (so each channel operates on different SRC/DST ports)
      if (user_defined_portsel == 1'b0) begin
        if (!randomize(src_portsel)) `uvm_error(get_full_name(), $sformatf("MULTI_CHAN Testing : FAILED to randomize src_portsel"))
        if (!randomize(dst_portsel)) `uvm_error(get_full_name(), $sformatf("MULTI_CHAN Testing : FAILED to randomize dst_portsel"))
      end

      setup_dma_channel(chan_idx, chan_base_addr);  // MULTI Channel-Testing. Setup each Channel to be tested with different Chan-Base-ADDR (so diff addr offsets applied) 
    end
    
  end
  
  enable_channels();         // Enable the single channel (for MULTI-Channel Testing, enable all in random order)
  wait_all_channels_idle();  // END OF TEST, when all channels are IDLE (if only 1 channel being tested, the other channels are already IDLE)

endtask : test_dma_channels



`endif // GUARD_DMA_IP_MODEL_FILES_BASED_TESTS_SV
