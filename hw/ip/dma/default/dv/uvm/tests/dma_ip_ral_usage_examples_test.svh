// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Examples on how to use RAL Methods, with tests and scoreboards etc
// Owner: Sultan Khan

`ifndef __DMA_IP_RAL_USAGE_EXAMPLES_TEST__
`define __DMA_IP_RAL_USAGE_EXAMPLES_TEST__

class dma_ip_ral_usage_examples_test extends dma_ip_base_test;

  bit [63:0] register_mask;        // Defines Which areas are R/W

  // Registration with the factory
  `uvm_component_utils(dma_ip_ral_usage_examples_test)

  // Class constructor
  function new (string name="dma_ip_ral_usage_examples_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_ral_usage_examples_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
    `uvm_info(get_full_name(), $sformatf("START : DMA IP Register Access Test"), UVM_LOW)

    //  dma_ip_regmodel.m_dma_common_reg_block.
    //    ch_mode;
    //    ch_status;
    //
    //  dma_ip_regmodel.m_dma_channel_reg_block.
    //    ch_ctrl;
    //    ch_cfg;
    //    ch_src_addr;
    //    ch_dst_addr;
    //    ch_xbytesize;
    //    ch_yrowsize;
    //    ch_tran_cfg;
    //    ch_xaddrinc;
    //    ch_yaddrstride;
    //    ch_link_descr;
    //    ch_status;
    //    ch_err_info;
    //    ch_req_bus_ctrl;


    // Global DMA Register Accesses
    // ----------------------

    // AXI-WRITES to Common MODE Register
    dma_ip_regmodel.m_dma_common_reg_block.ch_mode.write(status, 'hFFFF_FFFF_FFFF_FFFF);
    dma_ip_regmodel.m_dma_common_reg_block.ch_mode.write(status, 'hFFFF_FFFF_FFFF_A5A5);
    dma_ip_regmodel.m_dma_common_reg_block.ch_mode.write(status, 'h0000_0000_0000_0001);

    // Get Mirrored Value of this reg
    rdata = dma_ip_regmodel.m_dma_common_reg_block.ch_mode.get_mirrored_value();
    `uvm_info(get_full_name(), $sformatf("RAL : Mirrored Value after WRITE=%016h", rdata), UVM_LOW)
    
    // Actual AXI_READ of that register
    dma_ip_regmodel.m_dma_common_reg_block.ch_mode.read(status, rdata);
    `uvm_info(get_full_name(), $sformatf("RAL : Actual REG Value after READ=%016h", rdata), UVM_LOW)
    
    dma_ip_regmodel.m_dma_common_reg_block.ch_status.write(status, 'h0000_0000_0000_1010);   
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-0 WRITE uvm_status_e=%s", status.name()), UVM_LOW)

    // Channel Specific Register Accesses
    // ----------------------------------

    // Channel-0

    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_src_addr.write(status, 'h0000_0000_0000_1010);    // WRITE to src addr
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-0 WRITE uvm_status_e=%s", status.name()), UVM_LOW)
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_src_addr.read(status, rdata);
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-0 READ uvm_status_e=%s", status.name()), UVM_LOW)



    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_cfg.write(status, 'h0000_0000_0000_0016);         // WRITE to set 512b transfer size - 1D transfer.

    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_src_addr.write(status, 'h0000_0000_0000_1000);    // WRITE to src addr
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_dst_addr.write(status, 'h0000_0000_0000_2000);    // WRITE to dst addr

    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_xbytesize.write(status, 'h0000_0080_0000_0080);   // WRITE 64B transfer
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_yrowsize.write(status,  'h0000_0000_0000_0000);   // WRITE No 2D striding

    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_tran_cfg.write(status,    'h0000_0000_0000_0000); // WRITE set all 0 - not implemented yet
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_xaddrinc.write(status,    'h0000_0040_0000_0040); // WRITE to indicated DMA Register - Channel-3. DMA-Instance-0
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_yaddrstride.write(status, 'h0000_0040_0000_0040); // WRITE to indicated DMA Register - Channel-3. DMA-Instance-0

    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_ctrl.write(status, 'h0000_0000_0000_2000);        // WRITE to set max OS to 64 and enable channel


    // Accessing same register but on different channels    
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_xaddrinc.write(status, 'h0000_0000_0000_0016);    
    dma_ip_regmodel.m_dma_channel_reg_block[1].ch_xaddrinc.write(status, 'h0000_0000_0000_0008);    
    dma_ip_regmodel.m_dma_channel_reg_block[2].ch_xaddrinc.write(status, 'h0000_0000_0000_0004);    
    dma_ip_regmodel.m_dma_channel_reg_block[3].ch_xaddrinc.write(status, 'h0000_0000_0000_0001);    
    
    dma_ip_regmodel.m_dma_channel_reg_block[0].ch_xaddrinc.read(status, rdata);
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-0 Actual REG Value after READ=%016h", rdata), UVM_LOW)
    dma_ip_regmodel.m_dma_channel_reg_block[1].ch_xaddrinc.read(status, rdata);
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-1 Actual REG Value after READ=%016h", rdata), UVM_LOW)
    dma_ip_regmodel.m_dma_channel_reg_block[2].ch_xaddrinc.read(status, rdata);
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-2 Actual REG Value after READ=%016h", rdata), UVM_LOW)
    dma_ip_regmodel.m_dma_channel_reg_block[3].ch_xaddrinc.read(status, rdata);
    `uvm_info(get_full_name(), $sformatf("RAL : CHAN-3 Actual REG Value after READ=%016h", rdata), UVM_LOW)
    
    
    // MMU Accesses for Channel-0
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_cfg[0].write(status, 'h0000_0000_0000_0001); 

    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[0].write(status, 'h0000_0000_0000_0001); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[1].write(status, 'h0000_0000_0000_0002); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[2].write(status, 'h0000_0000_0000_0003); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[3].write(status, 'h0000_0000_0000_0004); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[4].write(status, 'h0000_0000_0000_0005); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[5].write(status, 'h0000_0000_0000_0006); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[6].write(status, 'h0000_0000_0000_0007); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_first[7].write(status, 'h0000_0000_0000_0008); 
    
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[0].write(status, 'h0000_0000_0000_0001); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[1].write(status, 'h0000_0000_0000_0002); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[2].write(status, 'h0000_0000_0000_0003); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[3].write(status, 'h0000_0000_0000_0004); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[4].write(status, 'h0000_0000_0000_0005); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[5].write(status, 'h0000_0000_0000_0006); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[6].write(status, 'h0000_0000_0000_0007); 
    dma_ip_regmodel.m_dma_mmu_reg_block[0].ch_mmu_base[7].write(status, 'h0000_0000_0000_0008); 

    // ----------------------------------------------------------
    `uvm_info(get_full_name(), $sformatf("END : DMA IP Register Access Test"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:dma_ip_ral_usage_examples_test

`endif	// __DMA_IP_RAL_USAGE_EXAMPLES_TEST__
