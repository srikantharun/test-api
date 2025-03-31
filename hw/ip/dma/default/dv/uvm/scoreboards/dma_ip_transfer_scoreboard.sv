// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: SCOREBOARD to check DMA transfers
// Owner      : Sultan Khan

`ifndef __DMA_IP_TRANSFER_SCOREBOARD__
`define __DMA_IP_TRANSFER_SCOREBOARD__

// Names of various analysis ports
`uvm_analysis_imp_decl(_axi_master_trans)
`uvm_analysis_imp_decl(_axi_slave0_trans)
`uvm_analysis_imp_decl(_axi_slave1_trans)

`uvm_analysis_imp_decl(_irq_info)



class dma_ip_transfer_scoreboard extends uvm_scoreboard;

    // DMA IP RAL Model
    dma_ip_reg_block  dma_ip_regmodel;
    uvm_status_e      status;
    
    // Define which AXID-fields contain the Channel-Number (as fields could change in future)
    `define AXID_CHAN_ID_FIELD  1:0

    `define DMA_PORT_0  0
    `define DMA_PORT_1  1
    
    // TBD ADD IRQ Agent, Preloading Mechanism
    uvm_analysis_imp_axi_master_trans #(svt_axi_transaction,dma_ip_transfer_scoreboard)   aimp_axi_master_trans_export;    // AXI-Details via AXI Master  Agent
    uvm_analysis_imp_axi_slave0_trans #(svt_axi_transaction,dma_ip_transfer_scoreboard)   aimp_axi_slave0_trans_export;    // AXI-Details via AXI Slave-0 Agent
    uvm_analysis_imp_axi_slave1_trans #(svt_axi_transaction,dma_ip_transfer_scoreboard)   aimp_axi_slave1_trans_export;    // AXI-Details via AXI Slave-1 Agent

    uvm_analysis_imp_irq_info #(irq_seq_item,dma_ip_transfer_scoreboard)   aimp_irq_info_export;                           // IRQ Information

    // ------------------------------------------
    // Options/Control-Knobs
    int  num_of_ports    = dma_ip_common_pkg::NUM_PORTS;
    int  num_of_channels = dma_ip_common_pkg::NUM_CHANNELS;

    // ------------------------------------------
    // For checking purposes
    bit irq_raised;    
    bit irq_seen;    // Checking Occurs when a DUT IRQ is seen. If test finishes with no IRQs then nothing is checked (we should Error this condition in report phase)  
    bit [dma_ip_common_pkg::NUM_CHANNELS-1:0] irq_line_state;   // Means to identify which DUT IRQ line was asserted (so which channel)
    
    // QUEUEs containing the intercepted AXI-Transactions (for each channel) from the DATA-TRANSFER PORTS 
    // Separate QUEUEs for READs and WRITEs, to make checking much easier (as DMA transfers WRITES while READING, so READS/WRITES will be intermingled in 1 QUEUE)

    int num_act_axi_transfers;                                                               // Holds the total amount of the ACTUA  L READ/WRITE AXI-TRANSFERS                                                      
    int num_exp_axi_transfers;                                                               // Holds the total amount of the EXPECTED READ/WRITE AXI-TRANSFERS                                                      

    svt_axi_transaction   data_port_wr_axi_transfers_q[dma_ip_common_pkg::NUM_CHANNELS][$];  // Holds the details of the ACTUAL WRITE AXI-TRANSFERs on the Data Transfer Ports
    svt_axi_transaction   data_port_rd_axi_transfers_q[dma_ip_common_pkg::NUM_CHANNELS][$];  // Holds the details of the ACTUAL READ  AXI-TRANSFERs on the Data Transfer Ports
        
    bit [63:0]  reg_rdata;  // Related to REGISTER Accesses
    bit [63:0]  reg_wdata;
    
    // ------------------------------------------
    dma_ip_transfer_details  test2scbd_details;

    // ------------------------------------------
    svt_axi_system_env 	axi_system_env_hndl;  // Need Handle to AXI SLAVE VIPs (for checking [reading] Memories affected by DMA transfers)

    // ------------------------------------------
    extern virtual function void write_axi_master_trans(input svt_axi_transaction axi_trans);
    extern virtual function void write_axi_slave0_trans(input svt_axi_transaction axi_trans);
    extern virtual function void write_axi_slave1_trans(input svt_axi_transaction axi_trans);
    extern virtual function void write_irq_info(input irq_seq_item irq_info);

    // TBD Also have similar methods in base-test (can we arrange them to use the same ?)
    extern virtual task slvmem_bkdr_read_byte (int slv_id, bit [39:0] addr, ref bit [7:0] data);
    extern virtual task slvmem_bkdr_read_num_byte (int slv_id, bit [39:0] addr, int num_of_bytes, ref bit [7:0] data[]);
    extern virtual task slvmem_bkdr_read_range (int slv_id, bit [39:0] addr_start, bit [39:0] addr_end, ref bit [7:0] data[]);

    // For Checking and Final Reporting Purposes
    extern virtual task check_mem(int chan_idx);
    extern virtual task check_channel_operation(int chan_idx);
    extern virtual function void check_queues_empty();


    `uvm_component_utils(dma_ip_transfer_scoreboard)
    
    function new(string name = "dma_ip_transfer_scoreboard", uvm_component parent);
        super.new(name,parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        aimp_axi_master_trans_export  = new("aimp_axi_master_trans_export", this);
        aimp_axi_slave0_trans_export  = new("aimp_axi_slave0_trans_export", this);
        aimp_axi_slave1_trans_export  = new("aimp_axi_slave1_trans_export", this);
        aimp_irq_info_export          = new("aimp_irq_info_export", this);
        
        `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("num_of_data_ports = %01d", num_of_ports), UVM_LOW)
        `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("num_of_channels   = %01d", num_of_channels), UVM_LOW)
        
        // Grab Handle for the Test -> SCBD Transfer Details
        if (!uvm_config_db#(dma_ip_transfer_details)::get(this, "", "test2scbd_details", test2scbd_details)) begin
           `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", "Unable to find test2scbd_details object in the uvm_config_db");
        end
    endfunction : build_phase

	  virtual function void end_of_elaboration_phase(uvm_phase phase);
		  super.end_of_elaboration_phase(phase);

		  // Get hand;e for the ENV (from which we navigate to the required AXI SLAVE VIPs)
      if (axi_system_env_hndl == null) begin
        if( !$cast(axi_system_env_hndl,uvm_top.find("*axi_system_env")) ) 
           `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Unable to find ENV component path %s", axi_system_env_hndl))
        else begin
           `uvm_info ("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Found ENV component path %s", axi_system_env_hndl), UVM_LOW)
        end
      end
	  endfunction : end_of_elaboration_phase

    virtual task reset_phase(uvm_phase phase);
        super.reset_phase(phase);
    endtask : reset_phase

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);

        // Generate INFO on what we are testing and what the various QUEUES contain before TESTs Begin (where we have been given the details)

        `uvm_info("test2scbd_details", $sformatf("Given : transfer_port_data_width =%0d", test2scbd_details.transfer_port_data_width), UVM_INFO)
        
        for (int i=0; i < dma_ip_common_pkg::NUM_CHANNELS; i++) begin
          if (test2scbd_details.channels_being_tested[i] == 1'b1) begin

            
            // SETUP Details (if SCBD needs them). TBD - These can be replaced by RAL Register mirror methids
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : src_addr        ='h%016h", i, test2scbd_details.channel_setup[i].src_addr          ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : dst_addr        ='h%016h", i, test2scbd_details.channel_setup[i].dst_addr          ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : transize        ='h%01h",  i, test2scbd_details.channel_setup[i].transize          ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : xtype           ='h%01h",  i, test2scbd_details.channel_setup[i].xtype             ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : src_xbytesize   ='h%08h",  i, test2scbd_details.channel_setup[i].src_xbytesize     ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : dst_xbytesize   ='h%08h",  i, test2scbd_details.channel_setup[i].dst_xbytesize     ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : src_xaddrinc    ='h%04h",  i, test2scbd_details.channel_setup[i].src_xaddrinc      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : dst_xaddrinc    ='h%04h",  i, test2scbd_details.channel_setup[i].src_xaddrinc      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : ytype           ='h%01h",  i, test2scbd_details.channel_setup[i].ytype             ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : src_yrowsize    ='h%08h",  i, test2scbd_details.channel_setup[i].src_yrowsize      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : dst_yrowsize    ='h%08h",  i, test2scbd_details.channel_setup[i].dst_yrowsize      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : src_yaddrstride ='h%04h",  i, test2scbd_details.channel_setup[i].src_yaddrstride   ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : dst_yaddrstride ='h%04h",  i, test2scbd_details.channel_setup[i].dst_yaddrstride   ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : src_burstlen    ='h%02h",  i, test2scbd_details.channel_setup[i].src_burstlen      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : dst_burstlen    ='h%02h",  i, test2scbd_details.channel_setup[i].dst_burstlen      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : fillval         ='h%04h",  i, test2scbd_details.channel_setup[i].fillval           ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : fillval_mode    ='h%01b",  i, test2scbd_details.channel_setup[i].fillval_mode      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : transform_en    ='h%01b",  i, test2scbd_details.channel_setup[i].transform_en      ), UVM_INFO)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : transform_type  ='h%01h",  i, test2scbd_details.channel_setup[i].transform_type    ), UVM_INFO)
            
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : test2scbd_details.type_of_testing = %s", i, test2scbd_details.type_of_testing[i].name()  ), UVM_INFO)

            
            // Pre-MEM Details (Not required for checking purposes but can be used to generate PRE_MEM and POST_MEM Deltas)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : pre_mem_addr_q.size() = %0d", i, test2scbd_details.post_mem_addr_q[i].size() ), UVM_INFO)
            for (int idx=0; idx < test2scbd_details.pre_mem_addr_q[i].size(); idx++) begin
              `uvm_info("test2scbd_details", $sformatf("Chan-%01d PRE_MEM Details Given : ADDR='h%016h  DATA='h%064h", 
                                                                  i, test2scbd_details.pre_mem_addr_q[i][idx], test2scbd_details.pre_mem_data_q[i][idx]), UVM_INFO)
            end
            
            // POST-MEM Details Given
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : post_mem_addr_q.size() = %0d", i, test2scbd_details.post_mem_addr_q[i].size() ), UVM_INFO)
            for (int idx=0; idx < test2scbd_details.post_mem_addr_q[i].size(); idx++) begin
              `uvm_info("test2scbd_details", $sformatf("Chan-%01d POST_MEM Details Given : ADDR='h%016h  DATA='h%064h", 
                                                                  i, test2scbd_details.post_mem_addr_q[i][idx], test2scbd_details.post_mem_data_q[i][idx]), UVM_INFO)
            end
 
            // Number of AXI-Transfers Expected for the channel
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : Number of Expected AXI-Transactions = %0d", 
                                                                                i, test2scbd_details.exp_axi_transfer_makeup_q[i].size() ), UVM_LOW)
            `uvm_info("test2scbd_details", $sformatf("Chan-%01d Details Given : Number of Expected AXI-Transfers (STRB Values) = %0d", 
                                                                                i, test2scbd_details.exp_axi_strb_q[i].size() ), UVM_LOW)
            
 
          end
        end


        // Checking of DMA Transfers
        // -------------------------
        // Wait until we get an IRQ RAISED event (which currently occurs once ALL DMA channels have become IDLE)
        // So if n-channels are being used, then this is when all those n-channels become ALL IDLE
        forever begin
          `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Waiting for irq_raised=1 (current state=%01d]", irq_raised), UVM_LOW);
          wait(irq_raised==1);             // Wait for an IRQ event
          irq_raised = 0;                  // Cancel flag once this was seen

          irq_seen = 1'b1;                // Log that we have seen at least 1 IRQ condition (so done at least 1 set of checks)
          `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Detected irq_raised=1"), UVM_LOW);
          
          // IRQ Received. GO through each channel in turn to see which channel raised it and do relevant checks
          for (int i=0; i < dma_ip_common_pkg::NUM_CHANNELS; i++) begin
            automatic int channel_idx;
            channel_idx = i;

            if (irq_line_state[channel_idx] == 1'b1) begin
            
              // Only do Check if the (DUT) IRQ line that is asserted, is for a channel which is enabled (eg no spurious IRQs from a channel which is not used)
              if (test2scbd_details.channels_being_tested[channel_idx] == 1'b0) begin
                `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Detected IRQ asserted, for CHANNEL-%0d which is not-used or not enabled", channel_idx))
              end
              else begin

                // We only do checks for a Channel-COMPLETION Event (and provided that channel was enabled)
                // TBD, until we have correct indications in an IRQ Status Register, for now we check if the channe; is DISABLED
                dma_ip_regmodel.m_dma_channel_reg_block[channel_idx].ch_ctrl.read(status, reg_rdata);
                
                if (reg_rdata[0] == 1'b1) begin
                  `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("IRQ asserted, for CHANNEL-%0d when it is still indicating ENABLE=1", channel_idx))
                end
                else begin
                  `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Channel Being Verified=%0d [On Channel-COMPLETION]", channel_idx), UVM_LOW);
                  check_mem(channel_idx);                   // Memory COntents post DMA Transfers
                  check_channel_operation(channel_idx);     // AXI-Transactions seen during DMA Transfers
                end
                
              end  
            end  // if ((irq_line_state
          end  // for              
        end  // forever

    endtask : run_phase

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    
    // TBD - Check we did some comparing (else error if no comparing done)
    `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Executing REPORT_PHASE"), UVM_LOW);
    check_queues_empty();
    
  endfunction


endclass : dma_ip_transfer_scoreboard


function void dma_ip_transfer_scoreboard::write_axi_master_trans(input svt_axi_transaction axi_trans);
  svt_axi_transaction  axi_mstr_trans;
  
  $cast(axi_mstr_trans, axi_trans.clone());
  uvm_report_info(get_type_name(), $psprintf("RECEIVED AXI-DETAILS from AXI-MASTER : %s", axi_mstr_trans.sprint()), UVM_LOW);
    
  // TBD - Do we need this info ?  
    
endfunction : write_axi_master_trans


function void dma_ip_transfer_scoreboard::write_axi_slave0_trans(input svt_axi_transaction axi_trans);
  svt_axi_transaction  axi_slv0_trans;
  int                  channel_id;
  
  $cast(axi_slv0_trans, axi_trans.clone());
  uvm_report_info(get_type_name(), $psprintf("RECEIVED AXI-DETAILS from AXI-SLAVE 0 : %s", axi_slv0_trans.sprint()), UVM_LOW);
        
  // Check that the channel-IDs embedded within the AXID AXI-signals, corresponds to the channel which is enabled
  // Error if we get an AXI-Transaction for a given channel but that channel is not being tested
  channel_id = axi_slv0_trans.id[`AXID_CHAN_ID_FIELD];
  if (test2scbd_details.channels_being_tested[channel_id] == 1'b0) begin
    `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("DMA Port-0: Received AXI-Trans. AXID set for channel-%0d but this channel is not being tested. [Chk AXID Decoding. Many Errors will Follow]",
                                                        channel_id));
  end

  // Channel read-write transactions on this SLAVE PORT (Port-0), must only exist according to the channel's SRC_MS and DST_MS settings.
  // Else ERROR because the channel is using the wrong transfer port 
  if (axi_slv0_trans.xact_type == dma_ip_common_pkg::AXI_TRANSACTION_TYPE_WRITE) begin
    if (test2scbd_details.channel_setup[channel_id].dst_ms != `DMA_PORT_0) begin
      `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("DMA Port-0: Received WRITE AXI-Trans from Channel-%0d but its CH_CTRL.DST_MS=%0d",
                                                        channel_id, test2scbd_details.channel_setup[channel_id].dst_ms));
    end
  end
  else begin
    if (test2scbd_details.channel_setup[channel_id].src_ms != `DMA_PORT_0) begin
      `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("DMA Port-0: Received READ AXI-Trans from Channel-%0d but its CH_CTRL.SRC_MS=%0d",
                                                        channel_id, test2scbd_details.channel_setup[channel_id].src_ms));
    end
  end
        
  // Push the AXI_Transfers onto correct QUEUES (2-bits of AXID identifies which channel is issuing the axi-transfers)
  if (axi_slv0_trans.xact_type == dma_ip_common_pkg::AXI_TRANSACTION_TYPE_WRITE) begin
    case (channel_id)
      0 : data_port_wr_axi_transfers_q[0].push_back(axi_slv0_trans);
      1 : data_port_wr_axi_transfers_q[1].push_back(axi_slv0_trans);
      2 : data_port_wr_axi_transfers_q[2].push_back(axi_slv0_trans);
      3 : data_port_wr_axi_transfers_q[3].push_back(axi_slv0_trans);
      default : `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("UNKNOWN channel_id=%0d", channel_id))
    endcase
  end
  else begin
    case (channel_id)
      0 : data_port_rd_axi_transfers_q[0].push_back(axi_slv0_trans);
      1 : data_port_rd_axi_transfers_q[1].push_back(axi_slv0_trans);
      2 : data_port_rd_axi_transfers_q[2].push_back(axi_slv0_trans);
      3 : data_port_rd_axi_transfers_q[3].push_back(axi_slv0_trans);
      default : `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("UNKNOWN channel_id=%0d", channel_id))
    endcase
  end
  
  foreach (data_port_wr_axi_transfers_q[i])
    `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("SIZE of data_port_wr_axi_transfers_q[%0d]=%0d", i, data_port_wr_axi_transfers_q[i].size() ), UVM_LOW);
  foreach (data_port_rd_axi_transfers_q[i])
    `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("SIZE of data_port_rd_axi_transfers_q[%0d]=%0d", i, data_port_rd_axi_transfers_q[i].size() ), UVM_LOW);
  
        
endfunction : write_axi_slave0_trans


function void dma_ip_transfer_scoreboard::write_axi_slave1_trans(input svt_axi_transaction axi_trans);
  svt_axi_transaction  axi_slv1_trans;
  int                  channel_id;
  
  $cast(axi_slv1_trans, axi_trans.clone());
  uvm_report_info(get_type_name(), $psprintf("RECEIVED AXI-DETAILS from AXI-SLAVE 1 : %s", axi_slv1_trans.sprint()), UVM_LOW);

  // Check that the channel-IDs embedded within the AXID AXI-signals, corresponds to the channel which is enabled
  // Error if we get an AXI-Transaction for a given channel but that channel is not being tested
  channel_id = axi_slv1_trans.id[`AXID_CHAN_ID_FIELD];
  if (test2scbd_details.channels_being_tested[channel_id] == 1'b0) begin
    `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("DMA Port-1: Received AXI-Trans. AXID set for channel-%0d but this channel is not being tested. [Chk AXID Decoding. Many Errors will Follow]",
                                                        channel_id));
  end

  // Channel read-write transactions on this SLAVE PORT (Port-0), must only exist according to the channel's SRC_MS and DST_MS settings.
  // Else ERROR because the channel is using the wrong transfer port 
  if (axi_slv1_trans.xact_type == dma_ip_common_pkg::AXI_TRANSACTION_TYPE_WRITE) begin
    if (test2scbd_details.channel_setup[channel_id].dst_ms != `DMA_PORT_1) begin
      `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("DMA Port-1: Received WRITE AXI-Trans from Channel-%0d but its CH_CTRL.DST_MS=%0d",
                                                        channel_id, test2scbd_details.channel_setup[channel_id].dst_ms));
    end
  end
  else begin
    if (test2scbd_details.channel_setup[channel_id].src_ms != `DMA_PORT_1) begin
      `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("DMA Port-1: Received READ AXI-Trans from Channel-%0d but its CH_CTRL.SRC_MS=%0d",
                                                        channel_id, test2scbd_details.channel_setup[channel_id].src_ms));
    end
  end
        
  // Push the AXI_Transfers onto correct QUEUES (2-bits of AXID identifies which channel is issuing the axi-transfers)
  if (axi_slv1_trans.xact_type == dma_ip_common_pkg::AXI_TRANSACTION_TYPE_WRITE) begin
    case (channel_id)
      0 : data_port_wr_axi_transfers_q[0].push_back(axi_slv1_trans);
      1 : data_port_wr_axi_transfers_q[1].push_back(axi_slv1_trans);
      2 : data_port_wr_axi_transfers_q[2].push_back(axi_slv1_trans);
      3 : data_port_wr_axi_transfers_q[3].push_back(axi_slv1_trans);
      default : `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("UNKNOWN channel_id=%0d", channel_id))
    endcase
  end
  else begin
    case (channel_id)
      0 : data_port_rd_axi_transfers_q[0].push_back(axi_slv1_trans);
      1 : data_port_rd_axi_transfers_q[1].push_back(axi_slv1_trans);
      2 : data_port_rd_axi_transfers_q[2].push_back(axi_slv1_trans);
      3 : data_port_rd_axi_transfers_q[3].push_back(axi_slv1_trans);
      default : `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("UNKNOWN channel_id=%0d", channel_id))
    endcase
  end
  
  foreach (data_port_wr_axi_transfers_q[i])
    `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("SIZE of data_port_wr_axi_transfers_q[%0d]=%0d", i, data_port_wr_axi_transfers_q[i].size() ), UVM_LOW);
  foreach (data_port_rd_axi_transfers_q[i])
    `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("SIZE of data_port_rd_axi_transfers_q[%0d]=%0d", i, data_port_rd_axi_transfers_q[i].size() ), UVM_LOW);

endfunction : write_axi_slave1_trans

function void dma_ip_transfer_scoreboard::write_irq_info(input irq_seq_item irq_info);
  irq_seq_item  irq_details;
  
  $cast(irq_details, irq_info);
  uvm_report_info(get_type_name(), $psprintf("RECEIVED IRQ INFO from IRQ_AGENT : %s", irq_details.change.name()), UVM_LOW);

  // Raise local IRQ flag, whenever an IRQ RAISED condition has occured (cleared by the consumer)
  if (irq_details.change ==  irq_pkg::IRQ_JUST_RAISED) begin
    `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("IRQ change Received. Raising irq_raised=1"), UVM_LOW);
    irq_raised = 1;
    irq_line_state = irq_details.irq_line_state;   // And grab details which IRQ Line of the DUT (which channel) is generating the IRQ
  end

  // TBD should use RAL methods to chk/clear any IRQs here
  
  
endfunction : write_irq_info



// --------------------------------------------------------------------------------------------------
// TBD Have Identical Tasks in the BASE-TEST - Maybe they can be removed

// READS a single BYTE from given address of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_transfer_scoreboard::slvmem_bkdr_read_byte (int slv_id, bit [39:0] addr, ref bit [7:0] data);
bit [7:0] readdata;

  if (slv_id < dma_ip_common_pkg::NUM_PORTS) begin
    case (slv_id)
      0 : axi_system_env_hndl.slave[0].read_byte(addr, readdata);
      1 : axi_system_env_hndl.slave[1].read_byte(addr, readdata);
    endcase
  data = readdata;
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, dma_ip_common_pkg::NUM_PORTS), UVM_LOW)
  end
endtask : slvmem_bkdr_read_byte


// READS a series of BYTES from the given address of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_transfer_scoreboard::slvmem_bkdr_read_num_byte (int slv_id, bit [39:0] addr, int num_of_bytes, ref bit [7:0] data[]);
bit [7:0] readdata[];

  readdata = new[num_of_bytes];
  if (slv_id < dma_ip_common_pkg::NUM_PORTS) begin
    case (slv_id)
      0 : axi_system_env_hndl.slave[0].read_num_byte(addr, num_of_bytes, readdata);
      1 : axi_system_env_hndl.slave[1].read_num_byte(addr, num_of_bytes, readdata);
    endcase
    
    foreach (readdata[i]) begin
      data[i] = readdata[i];
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, dma_ip_common_pkg::NUM_PORTS), UVM_LOW)
  end
endtask : slvmem_bkdr_read_num_byte


// READs a series of bytes the given address regions of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_transfer_scoreboard::slvmem_bkdr_read_range (int slv_id, bit [39:0] addr_start, bit [39:0] addr_end, ref bit [7:0] data[]);
bit [7:0]     readdata[];
logic [63:0]  num_bytes_to_access;

  // WORKAROUND. cant do num_bytes_to_access = addr_end - addr_start   (as results depend upon the upper SIGNED bit)
  num_bytes_to_access = 0;
  for (bit [63:0] i = addr_start; i <= addr_end; i++)
    num_bytes_to_access++;

  readdata = new[num_bytes_to_access];

  if (slv_id < dma_ip_common_pkg::NUM_PORTS) begin
    for (bit [63:0] mem_addr=addr_start; mem_addr <= num_bytes_to_access; mem_addr++) begin
      case (slv_id)
        0 : axi_system_env_hndl.slave[0].read_byte(mem_addr, readdata[mem_addr]);
        1 : axi_system_env_hndl.slave[1].read_byte(mem_addr, readdata[mem_addr]);
      endcase
      
      foreach (readdata[i]) begin
        data[i] = readdata[i];
      end
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, dma_ip_common_pkg::NUM_PORTS), UVM_LOW)
  end
endtask : slvmem_bkdr_read_range


// --------------------------------------------------------------------------------------------------
// Checking of AXI SLAVE MEMORY Contents, after DMA transfers over

task dma_ip_transfer_scoreboard::check_mem(int chan_idx);
int num_of_addr;              // Number of Preloaded Addresses to interrogate
int num_of_bytes;             // Number of bytes per MEMORY Reads
  
bit [39:0]   mem_addr;           // Holds the MEM ADDRESS to be read
bit [7:0]    mem_rdata_byte[];   // Holds the READ-data of the POST_MEM region

bit [511:0]  act_mem_rdata;  // ACTUAL   MEM DATA (arranged in the same format as the AXI Data Interface (width))
bit [511:0]  exp_mem_rdata;  // EXPECTED MEM DATA
bit [511:0]  xor_mem_rdata;

bit [1:0]    dst_portsel;    // Value for the channel's DST_MS (defines which DMA TRANSFER PORT the writes took place)

  `uvm_info(get_full_name(), $sformatf("Checking Operation of Channel-%0d",chan_idx ), UVM_LOW) 

  case (test2scbd_details.type_of_testing[chan_idx])
    dma_ip_common_pkg::MODEL_BASED_CSR,
    dma_ip_common_pkg::MODEL_BASED_CMDBLK :
      begin
      
        // -----------------------------------------------------------------------------------
        // POST_MEM Checking - Examine Memory AFTER DMA Transfers DONE (for the given channel)
        // -----------------------------------------------------------------------------------
        
        // Grab contents of AXI SLAVE MEMORY and compare with the expected POST-MEM Details
        // Amount of Memory to Read will be as per the number of addresses in the POST MEM QUEUE (prgrammed by the TEST)
        num_of_addr  = test2scbd_details.post_mem_addr_q[chan_idx].size();
        num_of_bytes = test2scbd_details.transfer_port_data_width/8;
        mem_rdata_byte = new[num_of_bytes];
        
        dst_portsel = test2scbd_details.channel_setup[chan_idx].dst_ms;
        `uvm_info("body", $sformatf("Reading POST_MEM Details from AXI_SLAVE-%0d Memory [For CHANNEL-%0d]", dst_portsel, chan_idx), UVM_INFO)

        // Read each pf the given POST MEM Address areas, and format the read-data for comparisons
        for (int addr_idx=0; addr_idx < num_of_addr; addr_idx++) begin
          mem_addr = test2scbd_details.post_mem_addr_q[chan_idx].pop_front();

          //Grab POST_MEM data from the correct SLAVE PORT
          slvmem_bkdr_read_num_byte (dst_portsel, mem_addr, num_of_bytes, mem_rdata_byte);
          
          // Create the read-data in the same format as the POST MEM DATA (full axi-data width, not byte data)
          for (int byte_idx=0; byte_idx < num_of_bytes; byte_idx++) begin
            act_mem_rdata[byte_idx*8 +: 8] = mem_rdata_byte[byte_idx];
          end
          
          `uvm_info(get_full_name(), $sformatf("POST_MEM Details from AXI_SLAVE-%0d Memory [Channel=%01d. Address='h%010h Data='h%064h]", dst_portsel, chan_idx, mem_addr, act_mem_rdata ), UVM_LOW) 

          // Now Compare this ACTUAL POST_MEM data with the Expected values
          
          exp_mem_rdata = test2scbd_details.post_mem_data_q[chan_idx].pop_front();
          if (act_mem_rdata != exp_mem_rdata) begin
            `uvm_error(get_full_name(), $sformatf("POST_MEM DATA-MISMATCH [Channel=%01d. Address='h%010h]. See next few lines for Full-Details", chan_idx, mem_addr ))
            
            // Give a Breakdown of the Error (which data location error exists)
            xor_mem_rdata = act_mem_rdata ^ exp_mem_rdata;
            `uvm_error(get_full_name(), $sformatf("POST_MEM DATA-MISMATCH [Channel=%01d. Address='h%010h. ACT-Data='h%064h]", chan_idx, mem_addr, act_mem_rdata ))
            `uvm_error(get_full_name(), $sformatf("POST_MEM DATA-MISMATCH [Channel=%01d. Address='h%010h. EXP-Data='h%064h]", chan_idx, mem_addr, exp_mem_rdata ))
            `uvm_error(get_full_name(), $sformatf("POST_MEM DATA-MISMATCH [Channel=%01d. Address='h%010h. XOR-DATA='h%064h]", chan_idx, mem_addr, xor_mem_rdata ))
            
            // Give a Breakdown of the Error (which byte-address and data byte it is)
            for (int byte_idx=0; byte_idx < num_of_bytes; byte_idx++) begin
              bit [7:0]    act_rdata_byte;
              bit [7:0]    exp_rdata_byte;
              
              act_rdata_byte = act_mem_rdata[byte_idx*8 +: 8];
              exp_rdata_byte = exp_mem_rdata[byte_idx*8 +: 8];
              
              if (act_rdata_byte != exp_rdata_byte) begin
                `uvm_error(get_full_name(), $sformatf("POST_MEM DATA-MISMATCH [Channel=%01d. Address='h%010h. BYTE-IDX=%0d. EXP-BYTE=%02h. ACT_BYTE=%02h]", 
                                                       chan_idx, (mem_addr+byte_idx), byte_idx, exp_rdata_byte, act_rdata_byte ))
              end
            end
            
          end  // if (act_mem_rdata != exp_mem_rdata)
        end  // for (int addr_idx=0; addr_idx < num_of_addr; addr_idx++)
      end 
      
      // -----------------------------------------------------------------------------------
                        
    default : `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Chan-%0d : Checks not Implemented for case %s [check_mem]", chan_idx, test2scbd_details.type_of_testing[chan_idx].name()))
  endcase

endtask : check_mem

// --------------------------------------------------------------------------------------------------
// Checking of AXI-Transfers, that had taken place during DMA transfers


task dma_ip_transfer_scoreboard::check_channel_operation(int chan_idx);

axi_transfer_makeup_t  exp_axi_transfer;
svt_axi_transaction    act_axi_transfer;

  `uvm_info(get_full_name(), $sformatf("Checking Operation of Channel-%0d",chan_idx ), UVM_LOW) 

  case (test2scbd_details.type_of_testing[chan_idx])
    dma_ip_common_pkg::MODEL_BASED_CSR,
    dma_ip_common_pkg::MODEL_BASED_CMDBLK :
      begin
       
        // -----------------------------------------------------------------------------------
        // AXI_TRANSACTION Checking - Examine make-up of AXI-Transactions captured during DMA Transfers (for the given channel)
        // -----------------------------------------------------------------------------------
        
        `uvm_info(get_full_name(), $sformatf("Chan-%01d Number of AXI-Entries in WRITE QUEUE = %0d. Number of AXI-Entries in READ QUEUE = %0d", 
                                              chan_idx, data_port_wr_axi_transfers_q[chan_idx].size(), data_port_rd_axi_transfers_q[chan_idx].size() ), UVM_LOW)

        // ----------------------------------------------------------------------------------------------------------------------
        // Number of AXI-Entries (extracted from the data-ports for the channel) must match those expected for the DMA transfers
        // ----------------------------------------------------------------------------------------------------------------------
        // Except when no transfers are expected at all
        
        num_act_axi_transfers = data_port_wr_axi_transfers_q[chan_idx].size() + data_port_rd_axi_transfers_q[chan_idx].size();
        num_exp_axi_transfers = test2scbd_details.exp_axi_transfer_makeup_q[chan_idx].size();
        
        if (num_exp_axi_transfers == 0) begin
          // Not expecting ANY DMA transfers. So Error, if there were actual DMA transfers taking place (transaction.txt file was read correctly if no prior errors)
          if (num_act_axi_transfers != 0) begin
            `uvm_error(get_full_name(), $sformatf("Chan-%01d NOT EXPECTING ANY DMA transfers for this case but it appeares DMA Transfers have occured [ACT_TOTAL=%0d (For All READS/WRITES)]", 
                                                   chan_idx, num_act_axi_transfers ))
          end
          else begin
            `uvm_info(get_full_name(), $sformatf("Chan-%01d NOTHING TO COMPARE. Expected Number of AXI-Transfers=0 ACTUAL Number of AXI_Transfers=0", chan_idx, ), UVM_LOW)
          end
        end
        else begin

          // ----------------------------------------------------------------------------------------------------------------------
          // Have Expected AXI-Transfers to Check Against
          // ----------------------------------------------------------------------------------------------------------------------
          // Now check the make-up of these AXI-Transfers, where possible (based on the expected NUMBER and types of AXI-Transfers)

          // Error upfront if there is a different between EXPECTED and ACTUAL DMA Transfers
          if (num_act_axi_transfers != num_exp_axi_transfers) begin
            `uvm_error(get_full_name(), $sformatf("Chan-%01d MISMATCH Number of AXI-TRANSFERS in QUEUES [EXP_TOTAL=%0d. ACT_TOTAL=%0d (For All READS/WRITES)]", 
                                                         chan_idx, num_exp_axi_transfers, num_act_axi_transfers ))
          end 

          // Now Compare each EXPECTED AXI-TRANSFER Entry with each ACTUAL AXI-TRANSFER ENTRY
          for (int trans_id=0; trans_id < num_exp_axi_transfers; trans_id++) begin
            bit         chk_transfers;
            string      axi_RW_type;
            bit [31:0]  xbytesize;
            bit [15:0]  xaddrinc;
            burst_type_enum   exp_burst_type_e;
            
            chk_transfers = 1'b1;   // Always checking AXI-Transfers, unless QUEUES EMPTY
            exp_axi_transfer = test2scbd_details.exp_axi_transfer_makeup_q[chan_idx].pop_front();
            axi_RW_type = (exp_axi_transfer.W_nR == 1) ? "WRITE" : "READ";
          
            // Check we have (still have) entries in the ACTUAL READ/WRITE AXI-TRANSFER QUEUEs, when Comparing against EXPECTATIONS. ELSE ERROR and no checking to take place
            if (axi_RW_type == "WRITE") begin
              // Handling Expected WRITE Transfers
              if (data_port_wr_axi_transfers_q[chan_idx].size() == 0) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d NOTHING TO COMPARE. Num of ACTUAL WRITE AXI-TRANSFERS in the QUEUE = 0", chan_idx))
                chk_transfers = 1'b0;
              end
              else begin
                act_axi_transfer = data_port_wr_axi_transfers_q[chan_idx].pop_front();
                xbytesize = test2scbd_details.channel_setup[chan_idx].dst_xbytesize;     // How Many BYTEs are being written to DST_ADDR 
                xaddrinc  = test2scbd_details.channel_setup[chan_idx].dst_xaddrinc;      // What the XADDRINC is for DST (WRITES)
              end
            end
            else begin
              // Handling Expected READ Transfers
              if (data_port_rd_axi_transfers_q[chan_idx].size() == 0) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d NOTHING TO COMPARE. Num of ACTUAL READ  AXI-TRANSFERS in the QUEUE = 0", chan_idx))
                chk_transfers = 1'b0;
              end
              else begin
                act_axi_transfer = data_port_rd_axi_transfers_q[chan_idx].pop_front();
                xbytesize = test2scbd_details.channel_setup[chan_idx].src_xbytesize;     // How Many BYTEs are being read from SRC_ADDR 
                xaddrinc  = test2scbd_details.channel_setup[chan_idx].src_xaddrinc;      // What the XADDRINC is for SRC (READS)
              end
            end
            
            // ACTUAL CHECKING of AXI-TRANSFER DETAILS
            // ---------------------------------------
            if (chk_transfers) begin
              // Now do the checks of Important AXI Fields
              
              if (act_axi_transfer.addr != exp_axi_transfer.start_addr) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d ADDR MISMATCH [EXP_ADDR=%010h. ACT_ADDR=%010h][%s AXI-TRANSFER=%0d]", 
                                                       chan_idx, exp_axi_transfer.start_addr, act_axi_transfer.addr, axi_RW_type, trans_id))
              end
              
              // TBD No need to verify end-address (as held by exp_axi_transfer.end_addr). If its wrong, then POST_MEM checks will fail
              
              if (act_axi_transfer.burst_length != exp_axi_transfer.burst_len) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d BURST-LENGTH MISMATCH [EXP_LEN=%010h. ACT_LEN=%010h][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                       chan_idx, exp_axi_transfer.burst_len, act_axi_transfer.burst_length, axi_RW_type, trans_id, act_axi_transfer.addr))
              end
              if (act_axi_transfer.burst_size != exp_axi_transfer.burst_size) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d BURST-SIZE MISMATCH [EXP_SIZE=%010h. ACT_SIZE=%010h][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                       chan_idx, exp_axi_transfer.burst_size, act_axi_transfer.burst_size, axi_RW_type, trans_id, act_axi_transfer.addr))
              end
             
              // BURST_TYPE is dependant upon how many bytes being transferred (num of transfers) per READS/WRITES
              // And if XADDRINC = 0 (for src or dst)
              if      (xaddrinc == 0)                             exp_burst_type_e = dma_ip_common_pkg::FIXED;
              else if (exp_axi_transfer.num_data_transfers == 1)  exp_burst_type_e = dma_ip_common_pkg::FIXED;
              else                                                exp_burst_type_e = dma_ip_common_pkg::INCR;
              
              if (act_axi_transfer.burst_type != exp_burst_type_e) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d BURST-TYPE MISMATCH [EXP_TYPE=%s. ACT_TYPE=%s][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                       chan_idx, exp_burst_type_e, act_axi_transfer.burst_type, axi_RW_type, trans_id, act_axi_transfer.addr))
              end

              // AXPROT values    
              if (act_axi_transfer.prot_type[0] != dma_ip_common_pkg::AXI_TRANSACTION_PROT_UNPRIV) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d PROT-TYPE[0] MISMATCH [EXP_TYPE=UNPRIVILEGED_ACCESS. ACT_TYPE=PRIVILEGED_ACCESS][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                       chan_idx, axi_RW_type, trans_id, act_axi_transfer.addr))
              end
              if (act_axi_transfer.prot_type[1] != dma_ip_common_pkg::AXI_TRANSACTION_PROT_NON_SECURE) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d PROT-TYPE[1] MISMATCH [EXP_TYPE=NON_SECURE_ACCESS. ACT_TYPE=SECURE_ACCESS][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                       chan_idx, axi_RW_type, trans_id, act_axi_transfer.addr))
              end
              if (act_axi_transfer.prot_type[2] != dma_ip_common_pkg::AXI_TRANSACTION_PROT_DATA) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d PROT-TYPE[2] MISMATCH [EXP_TYPE=DATA_ACCESS. ACT_TYPE=INSTRUCTION_ACCESS][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                       chan_idx, axi_RW_type, trans_id, act_axi_transfer.addr))
              end

              // TBD chck cache-line value ???
              
              // Check STRBs/RESP of the individual data-transfers
              // -------------------------------------------------   
              // This depends upon the number of data-transfers per AXI-TRANSACTION
                                     
              if (exp_axi_transfer.num_data_transfers == 0) begin
                `uvm_error(get_full_name(), $sformatf("Chan-%01d NOTHING TO COMPARE. Num of EXPECTED individual DATA-TRASNFERS (BURSTS) = 0", chan_idx))
              end
              else begin
              
                 // Have DATA-BURSTS for this Channel to be compared against
                for (int burst_id=0; burst_id < exp_axi_transfer.num_data_transfers; burst_id++) begin
                  bit [63:0]  exp_strb_value;
                                             
                  // CHECK whether a READ or WRITE TRansaction, to verify if verifying BRESP or RRESP
                  if (axi_RW_type == "WRITE") begin
                    // Checking AXI-WRITEs. WSTRBS and BRESP
                    
                    // Only 1 BRESP per w-transfer (unlike RRESP). See members of svt_axi_transaction 
                    if (act_axi_transfer.bresp != dma_ip_common_pkg::OKAY) begin
                      `uvm_error(get_full_name(), $sformatf("Chan-%01d BRESP MISMATCH. EXPECTED TO BE OKAY [ACT : %s][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                                                             chan_idx, act_axi_transfer.bresp[burst_id], axi_RW_type, trans_id, act_axi_transfer.addr ))
                    end
                    
                    if (test2scbd_details.exp_axi_strb_q[chan_idx].size() == 0) begin
                      `uvm_error(get_full_name(), $sformatf("Chan-%01d NOTHING TO COMPARE. Exhausted STRB QUEUE (size = 0]", chan_idx))
                    end
                    else begin
                      exp_strb_value = test2scbd_details.exp_axi_strb_q[chan_idx].pop_front();
                      
                      if (act_axi_transfer.wstrb[burst_id] != exp_strb_value) begin 
                        `uvm_error(get_full_name(), $sformatf("Chan-%01d WSTRB[%0d] MISMATCH [EXP=%016h. ACT=%016h][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]", 
                                                                    chan_idx, burst_id, exp_strb_value, act_axi_transfer.wstrb[burst_id], axi_RW_type, trans_id, act_axi_transfer.addr ))
                      end
                    end
                  end
                  else begin
                    // Checking AXI_READs. 
                    
                    // CHK RRESP ONLY. 
                    if (act_axi_transfer.rresp[burst_id] != dma_ip_common_pkg::OKAY) begin
                      `uvm_error(get_full_name(), $sformatf("Chan-%01d RRESP[%0d] MISMATCH. EXPECTED TO BE OKAY [ACT : %s][%s AXI-TRANSFER=%0d][AXI_ADDR=%010h]",
                                                                    chan_idx, burst_id, act_axi_transfer.rresp[burst_id].name(), axi_RW_type, trans_id, act_axi_transfer.addr ))
                    end
                    
                    // There are no such thing as Read STRBs within the AXI_PROTOCOL. So discard any that were picked up from the transaction file (for READs)
                    exp_strb_value = test2scbd_details.exp_axi_strb_q[chan_idx].pop_front();   // Popped from QUEUE but discarded

                  end
                
                end  // for (int burst_id=0; burst_id < exp_axi_transfer.num_data_transfers; burst_id++) begin
              end  // if (exp_axi_transfer.num_data_transfers == 0) else
              
              // -------------------------------------------------   
              
            end // if (chk_transfers)
          end  // for (int trans_id=0; trans_id < num_exp_axi_transfers; trans_id++) begin

        end  // if (num_exp_axi_transfers == 0) else
                        
      end // endcase
    default : `uvm_error("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Chan-%0d : Checks not Implemented for case %s [check_channel_operation]", chan_idx, test2scbd_details.type_of_testing[chan_idx].name()))
  endcase

endtask : check_channel_operation

// --------------------------------------------------------------------------------------------------
// Report Phase Checking

function void dma_ip_transfer_scoreboard::check_queues_empty();
  bit  found_issue;
  
  // If NO DUT IRQs have been seen, then no checks were ever made. So various QUEUES will have items unchecked. So Error this major fault in the DUT
  if (irq_seen == 1'b0) begin
     `uvm_error("REPORT_PHASE", $sformatf("Test has ENDED with NO Transaction/Memory CHECKING. No DUT IRQs were ever seen. All Subsequent Errors [QUEUEs NOT EMPTY] are related to this")) 
  end
  
  // All POST Memory QUEUES to be EMPTY (to indicate they have been offloaded and cross-checked)
  // For channels that are not utilized, those QUEUES will not have any data within them.
  //
  // We dont check PRE-MEM QUEUSs as that is what the Memories are programmed up with (by the test) BEFORE DMA Transfers
  // We only have data in the PRE_MEM QUEUES, in case we need to use this information (to get PRE_MEM and POST_MEM Delta changes) 
  
  `uvm_info("DMA_IP_TRANSFER_SCOREBOARD", $sformatf("Executing check_queues_empty"), UVM_LOW);

  for (int i=0; i < dma_ip_common_pkg::NUM_CHANNELS; i++) begin

    // -------------------------------------------------------------------------------------------------
    // POST-MEMORY 
    found_issue = 1'b0;
    if (test2scbd_details.post_mem_addr_q[i].size() != 0) begin
      found_issue = 1'b1;
      `uvm_error("REPORT_PHASE", $sformatf("QUEUE Expected to be EMPTY at END-OF-TESTS : post_mem_addr_q for channel-%0d [NUM OF UNCHECKED ENTRIES=%0d. Details in LOGFILE]", 
                                                                                         i, test2scbd_details.post_mem_addr_q[i].size() )) 
    end
    if (test2scbd_details.post_mem_data_q[i].size() != 0) begin
      found_issue = 1'b1;
      `uvm_error("REPORT_PHASE", $sformatf("QUEUE Expected to be EMPTY at END-OF-TESTS : post_mem_data_q for channel-%0d [NUM OF UNCHECKED ENTRIES=%0d. Details in LOGFILE]", 
                                                                                         i, test2scbd_details.post_mem_data_q[i].size())) 
    end
    
    // Offload Details of ADDR and DATA PAIRED Queues (they will always be in sync [same sizes] as for each addr, there is a corresponding data)
    if (found_issue) begin
      for (int idx=0; idx < test2scbd_details.post_mem_addr_q[i].size(); idx++) begin
        `uvm_info("REPORT_PHASE", $sformatf("Following QUEUE Items remain UNCHECKED [POST_MEM ADDR='h%010h DATA='h%064h (Q_IDX=%01d]]", 
                                                                    test2scbd_details.post_mem_addr_q[idx], test2scbd_details.post_mem_data_q[idx], idx), UVM_LOW) 
      end
    end

    // -------------------------------------------------------------------------------------------------
    // QUEUES related to EXPECTED and ACTUAL AXI TRANSFER to be EMPTY too (There are all independent. Not PAIRED)
    found_issue = 1'b0;
    
    // QUEUE Related to EXPECTED AXI-TRANSFERS 
    if (test2scbd_details.exp_axi_transfer_makeup_q[i].size() != 0) begin
      `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d QUEUE Expected to be EMPTY at END-OF-TESTS : DMA MODEL EXPECTED TRANSFERS exp_axi_transfer_makeup_q [NUM OF UNCHECKED ENTRIES=%0d.]", 
                                                                                         i, test2scbd_details.exp_axi_transfer_makeup_q[i].size())) 
                                                                                         
      for (int idx=0; idx < test2scbd_details.exp_axi_transfer_makeup_q[i].size(); idx++) begin
        `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d UNCHECKED : DMA MODEL EXPECTED AXI-TRANSFER for ADDR=%010h",i, test2scbd_details.exp_axi_transfer_makeup_q[i][idx].start_addr ))
      end
    end
    // QUEUE Related to EXPECTED STRB Values 
    if (test2scbd_details.exp_axi_strb_q[i].size() != 0) begin
      `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d QUEUE Expected to be EMPTY at END-OF-TESTS : DMA MODEL EXPECTED STRBs exp_axi_strb_q [NUM OF UNCHECKED ENTRIES=%0d.]", 
                                                                                         i, test2scbd_details.exp_axi_strb_q[i].size())) 
                                                                                         
      for (int idx=0; idx < test2scbd_details.exp_axi_strb_q[i].size(); idx++) begin
        `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d UNCHECKED : DMA MODEL EXPECTED AXI-TRANSFER WSTRB=%010h",i, test2scbd_details.exp_axi_strb_q[i][idx] ))
      end
    end
    // QUEUE Related to ACTUAL READ AXI-TRANSFERS 
    if (data_port_rd_axi_transfers_q[i].size() != 0) begin
      `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d QUEUE Expected to be EMPTY at END-OF-TESTS : DUT ACTUAL READ AXI-TRANSFERS data_port_rd_axi_transfers_q [NUM OF UNCHECKED ENTRIES=%0d]", 
                                                                                         i, data_port_rd_axi_transfers_q[i].size())) 
                                                                                         
      for (int idx=0; idx < data_port_rd_axi_transfers_q[i].size(); idx++) begin
        `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d UNCHECKED : DUT ACTUAL READ AXI-TRANSFER for ADDR=%010h",i, data_port_rd_axi_transfers_q[i][idx].addr ))
      end
    end
    // QUEUE Related to ACTUAL WRITE AXI-TRANSFERS 
    if (data_port_wr_axi_transfers_q[i].size() != 0) begin
      `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d QUEUE Expected to be EMPTY at END-OF-TESTS :  DUT ACTUAL WRITE AXI-TRANSFERS data_port_wr_axi_transfers_q [NUM OF UNCHECKED ENTRIES=%0d]", 
                                                                                         i, data_port_wr_axi_transfers_q[i].size())) 
                                                                                         
      for (int idx=0; idx < data_port_wr_axi_transfers_q[i].size(); idx++) begin
        `uvm_error("REPORT_PHASE", $sformatf("Channel-%0d UNCHECKED : DUT ACTUAL WRITE AXI-TRANSFER for ADDR=%010h",i, data_port_wr_axi_transfers_q[i][idx].addr ))
      end
    end

    // -------------------------------------------------------------------------------------------------
   // TBD - ANY other QUEUES to be tested (which may have been added later on
   found_issue = 1'b0;


    // -------------------------------------------------------------------------------------------------

  end

endfunction : check_queues_empty

// --------------------------------------------------------------------------------------------------

`endif // __DMA_IP_TRANSFER_SCOREBOARD__

