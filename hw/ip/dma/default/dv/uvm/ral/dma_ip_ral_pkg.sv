// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Manually created RAL model package for DMA IP
// Owner: Sultan Khan

package dma_ip_ral_pkg;
  // Packages import
  import uvm_pkg::*;
  // Macro includes
  `include "uvm_macros.svh"
  import dma_ip_common_pkg::*;
  import dv_base_reg_pkg::*;
  import dma_ral_pkg::*;
  import dma_channel_ral_pkg::*;
  import dma_mmu_ral_pkg::*;

  
  localparam DMA_IP_MMU_BASE_ADDR      = 32'h0000_0000;   // Location of the DMA COMMON Registers
  localparam DMA_IP_COMMON_BASE_ADDR   = 32'h0001_0000;   // Location of the DMA COMMON Registers
  localparam DMA_IP_CHAN_CMB_BASE_ADDR = 32'h0002_0000;   // Locatiom of the very 1st DMA Channel CMB BLK   (Channel-0 CMB BLK)
  localparam DMA_IP_CHAN_REG_BASE_ADDR = 32'h0002_1000;   // Locatiom of the very 1st DMA Channel Registers (Channel-0 Registers)

  localparam DMA_IP_MMU_ADDR_OFFSET    = 32'h0000_1000;   // Address separation between each MMU Entries Per Channel
  localparam DMA_IP_CHAN_ADDR_OFFSET   = 32'h0000_2000;   // Address separation between each DMA Channel Registers (or DMA CMB BLKS)


  // Manually created RAL model block for DMA_IP Sub-system
  class dma_ip_reg_block extends dv_base_reg_block;

    // Registration with factory
    `uvm_object_utils(dma_ip_reg_block)
    // RAL models objects
    rand dma_reg_block                m_dma_common_reg_block;
    rand dma_channel_reg_block        m_dma_channel_reg_block[dma_ip_common_pkg::NUM_CHANNELS];
    rand dma_mmu_reg_block            m_dma_mmu_reg_block[dma_ip_common_pkg::NUM_CHANNELS];

    // Reg map object
    uvm_reg_map dma_ip_map;

    // Class construcotr
    function new(string name = "dma_ip_reg_block");
      super.new(name);
    endfunction: new

   // Provide build function to supply base addr
   function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);

      // Map definition
      dma_ip_map = create_map(base_addr, 0, 8, UVM_LITTLE_ENDIAN, 0);
      default_map    = dma_ip_map;

      // REG_MODEL for the DMA Common Registers
      this.m_dma_common_reg_block = dma_reg_block::type_id::create("m_dma_common_reg_block",,get_full_name());
      this.m_dma_common_reg_block.configure(this, "DMA_IP_COMMON");
      this.m_dma_common_reg_block.build(null);
      dma_ip_map.add_submap(m_dma_common_reg_block.default_map, DMA_IP_COMMON_BASE_ADDR);
      this.m_dma_common_reg_block.lock_model();

      // REG_MODEL for each of the DMA Channel Registers - Take the Channel-Registers and Replicate them n-times
      for (int i = 0; i < dma_ip_common_pkg::NUM_CHANNELS; i++) begin
        string      chan_regblk_name;
        string      chan_cfg_name;
        bit [63:0]  chan_base_addr;
        
        chan_regblk_name = $sformatf("m_dma_channel_reg_block[%01d]", i);
        chan_cfg_name    = $sformatf("DMA_IP_CHAN_REG[%01d]", i);
        chan_base_addr   = DMA_IP_CHAN_REG_BASE_ADDR + (i * DMA_IP_CHAN_ADDR_OFFSET);
        
        `uvm_info("DMA_IP_REG_BLOCK", $sformatf("chan_regblk_name = %s",    chan_regblk_name), UVM_LOW)
        `uvm_info("DMA_IP_REG_BLOCK", $sformatf("chan_cfg_name    = %s",    chan_cfg_name),    UVM_LOW)   
        `uvm_info("DMA_IP_REG_BLOCK", $sformatf("chan_base_addr   = %08h",  chan_base_addr),   UVM_LOW)  
        
        this.m_dma_channel_reg_block[i] = dma_channel_reg_block::type_id::create(chan_regblk_name,,get_full_name());
        this.m_dma_channel_reg_block[i].configure(this, chan_cfg_name);
        this.m_dma_channel_reg_block[i].build(null);
        dma_ip_map.add_submap(m_dma_channel_reg_block[i].default_map, chan_base_addr);
        this.m_dma_channel_reg_block[i].lock_model();
      end
      
      // REG_MODEL for each of the MMU entries per DMA Channel - Take the MMU Registes and Replicate them n-times
      for (int i = 0; i < dma_ip_common_pkg::NUM_CHANNELS; i++) begin
        string      mmu_regblk_name;
        string      mmu_cfg_name;
        bit [63:0]  mmu_base_addr;
        
        mmu_regblk_name = $sformatf("m_dma_mmu_reg_block[%01d]", i);
        mmu_cfg_name    = $sformatf("DMA_IP_MMU_REG[%01d]", i);
        mmu_base_addr   = DMA_IP_MMU_BASE_ADDR + (i * DMA_IP_MMU_ADDR_OFFSET);
        
        `uvm_info("DMA_IP_REG_BLOCK", $sformatf("mmu_regblk_name = %s",    mmu_regblk_name), UVM_LOW)
        `uvm_info("DMA_IP_REG_BLOCK", $sformatf("mmu_cfg_name    = %s",    mmu_cfg_name),    UVM_LOW)   
        `uvm_info("DMA_IP_REG_BLOCK", $sformatf("mmu_base_addr   = %08h",  mmu_base_addr),   UVM_LOW)  
        
        this.m_dma_mmu_reg_block[i] = dma_mmu_reg_block::type_id::create(mmu_regblk_name,,get_full_name());
        this.m_dma_mmu_reg_block[i].configure(this, mmu_cfg_name);
        this.m_dma_mmu_reg_block[i].build(null);
        dma_ip_map.add_submap(m_dma_mmu_reg_block[i].default_map, mmu_base_addr);
        this.m_dma_mmu_reg_block[i].lock_model();
      end

   endfunction : build
  endclass : dma_ip_reg_block

endpackage:dma_ip_ral_pkg
