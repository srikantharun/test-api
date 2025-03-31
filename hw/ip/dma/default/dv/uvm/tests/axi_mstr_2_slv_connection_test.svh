// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Tests Connections between the AXI MASTER VIP and 1 of the AXI SLAVE VIPs
//   To ensure 
//     AXI Master can generate transactions
//     AXI Slave can respond to those transactions
//
//   Primarily used to pipe-clean VIP configurations and features we need to support
//
//   TESTCASE MUST ONLY be used when the AXI MASTER AGENT is connected directly to the AXI SLAVE AGENT (within the DMA IP TestBench)
//   Where the DUT (DMA RTL) is bypassed. define (which provides this direct connection) is AXI_VIP_MSTR_2_SLV_DIRECTTBD
//
// Owner: Sultan.Khan

`ifndef __AXI_MSTR_2_SLV_CONNECTION_TEST__
`define __AXI_MSTR_2_SLV_CONNECTION_TEST__

class axi_mstr_2_slv_connection_test extends dma_ip_base_test;

  // Registration with the factory
  `uvm_component_utils(axi_mstr_2_slv_connection_test)

  // Class constructor
  function new (string name="axi_mstr_2_slv_connection_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("axi_mstr_2_slv_connection_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info(get_full_name(), $sformatf("START : AXI Master 2 AXI Slave Connection Test"), UVM_LOW)

     // Get AXI MASTER to create a series of WRITE/READ transactions to various arbitary addresses
     // (which just happen to correspond to CSR Regsters) and all channels. There is no DUT, so these transactions will go to 1 of the AXI SLAVE VIPS
     //
     // We could have chosen ANY random address
     //
     // ANYTHING which is written to an address, will be read-back 
     
     `ifdef AXI_VIP_MSTR_2_SLV_DIRECT
     
     for (int channel=0; channel <= 7; channel++) begin  // TBD only the channels which are implemented. Rest should have DEC/SLVERR
       for (int reg_idx = 0; reg_idx <= 12; reg_idx++) begin
         randomize_data(wdata);
         
         case (reg_idx)
                // Regname. channel_num, dma_instance, wdata
                // DMA (CSR) Registers
           0  : begin   DMA_REG_WRITE (DMA_CH_CTRL       , channel, wdata);     DMA_REG_READ (DMA_CH_CTRL      , channel, rdata);   end
           1  : begin   DMA_REG_WRITE (DMA_CH_CFG        , channel, wdata);     DMA_REG_READ (DMA_CH_CFG       , channel, rdata);   end
           2  : begin   DMA_REG_WRITE (DMA_CH_SRC_ADDR   , channel, wdata);     DMA_REG_READ (DMA_CH_SRC_ADDR  , channel, rdata);   end
           3  : begin   DMA_REG_WRITE (DMA_CH_DST_ADDR   , channel, wdata);     DMA_REG_READ (DMA_CH_DST_ADDR  , channel, rdata);   end
           4  : begin   DMA_REG_WRITE (DMA_CH_XBYTESIZE  , channel, wdata);     DMA_REG_READ (DMA_CH_XBYTESIZE , channel, rdata);   end
           5  : begin   DMA_REG_WRITE (DMA_CH_YROWSIZE   , channel, wdata);     DMA_REG_READ (DMA_CH_YROWSIZE  , channel, rdata);   end
           6  : begin   DMA_REG_WRITE (DMA_CH_TRAN_CFG   , channel, wdata);     DMA_REG_READ (DMA_CH_TRAN_CFG  , channel, rdata);   end
           7  : begin   DMA_REG_WRITE (DMA_CH_XADDRINC   , channel, wdata);     DMA_REG_READ (DMA_CH_XADDRINC  , channel, rdata);   end
           8  : begin   DMA_REG_WRITE (DMA_CH_YADDRSTRIDE, channel, wdata);     DMA_REG_READ (DMA_CH_YADDRTRIDE, channel, rdata);   end
           9  : begin   DMA_REG_WRITE (DMA_CH_LINK_DESCR , channel, wdata);     DMA_REG_READ (DMA_CH_LINK_DESCR, channel, rdata);   end
           10 : begin   DMA_REG_WRITE (DMA_CH_STATUS     , channel, wdata);     DMA_REG_READ (DMA_CH_STATUS    , channel, rdata);   end
           11 : begin   DMA_REG_WRITE (DMA_CH_ERR_INFO   , channel, wdata);     DMA_REG_READ (DMA_CH_ERR_INFO  , channel, rdata);   end
           12 :begin    DMA_REG_WRITE (DMA_CH_REQ_BUS_CTRL , channel, wdata);   DMA_REG_READ (DMA_CH_REQ_BUS_CTRL , channel, rdata);   end
         endcase 
       
       end
     end

     // Attempt to do preloading of the respective AXI Slave (VIP) Memories, using BACKDORR Accesses
     // uvm_test_top
     env.axi_system_env.slave[0].write_byte('h2_1000, 8'ha5);    // Backdoor value to DMA_CH_CTRL Address. AXI SLAVE-0
     env.axi_system_env.slave[1].write_byte('h2_1000, 8'h5a);    // Backdoor value to DMA_CH_CTRL Address. AXI SLAVE-1
     
     // What gets read-back is based on which AXI_SLAVE we connect to in the TESTBENCH (SLV0 will return a5. Slave1 will return 5a, if abve works)
     DMA_REG_READ (DMA_CH_CTRL      , 0, rdata);              // Read that address
     
     
     // Using a different Write-Method
     backdoor_mem_wdata=new[5];
     backdoor_mem_wdata[0] = 8'h12;
     backdoor_mem_wdata[1] = 8'h34;
     backdoor_mem_wdata[2] = 8'h56;
     backdoor_mem_wdata[3] = 8'h78;
     backdoor_mem_wdata[4] = 8'h9a;
     env.axi_system_env.slave[0].write_num_byte('h2_1000, 5, backdoor_mem_wdata);    // Backdoor value to DMA_CH_CTRL Address. AXI SLAVE-0
     
     backdoor_mem_wdata[0] = 8'hab;
     backdoor_mem_wdata[1] = 8'hcd;
     backdoor_mem_wdata[2] = 8'hef;
     backdoor_mem_wdata[3] = 8'h01;
     backdoor_mem_wdata[4] = 8'h23;
     env.axi_system_env.slave[1].write_num_byte('h2_1000, 5, backdoor_mem_wdata);    // Backdoor value to DMA_CH_CTRL Address. AXI SLAVE-1
     
     // What gets read-back is based on which AXI_SLAVE we connect to in the TESTBENCH  
     DMA_REG_READ (DMA_CH_CTRL      , 0, rdata);              // Read that address
     
     
     
     
     
     
     // Test Other Methods of writing backdoor. COMMENTED OUT as no such METHODS (leads to compile issues)
     // env.axi_system_env.slave[0].write('h2_1000, 64'h1234_5678_9abc_def0);   // Backdoor value to DMA_CH_CTRL Address. AXI SLAVE-0
     // env.axi_system_env.slave[1].write('h2_1000, 64'h9abc_def0_1234_5678);   // Backdoor value to DMA_CH_CTRL Address. AXI SLAVE-0
     // DMA_REG_READ (DMA_CH_CTRL      , 0, rdata);                          // Read that address
     
 
     `else
       `uvm_error(get_full_name(), $sformatf("This testcase must only be run with GLOBAL_DEFINES=+define+AXI_VIP_MSTR_2_SLV_DIRECT "))
     `endif

     // ----------------------------------------------------------
      `uvm_info(get_full_name(), $sformatf("END : AXI Master 2 AXI Slave Connection Test"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:axi_mstr_2_slv_connection_test

`endif	// __AXI_MSTR_2_SLV_CONNECTION_TEST__
