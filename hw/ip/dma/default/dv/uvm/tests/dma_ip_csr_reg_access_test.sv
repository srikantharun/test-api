// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Testcase to confirm WRITE/READ accesses to all Implemented DMA Registers
// Owner: Sultan Khan

`ifndef __DMA_IP_CSR_REG_ACCESS_TEST__
`define __DMA_IP_CSR_REG_ACCESS_TEST__

class dma_ip_csr_reg_access_test extends dma_ip_base_test;

  bit [63:0] register_mask;        // Defines Which areas are R/W

  // Registration with the factory
  `uvm_component_utils(dma_ip_csr_reg_access_test)

  // Class constructor
  function new (string name="dma_ip_csr_reg_access_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_csr_reg_access_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
    `uvm_info(get_full_name(), $sformatf("START : DMA IP Register Access Test"), UVM_LOW)

    // ----------------------------------------------------------
    // Common (Global) DMA Registers, applicable to all channels

    for (int reg_idx = 0; reg_idx <= 1; reg_idx++) begin
      case (reg_idx)
        0 : begin   dma_register = DMA_CH_COMMON_MODE;        register_mask = 64'h0000_0000_0000_000f;        end
        1 : begin   dma_register = DMA_CH_COMMON_STATUS;      register_mask = 64'h0000_0000_0000_0000;        end  // RO
      endcase
      
      // randomize_data(wdata);
      wdata = '1;
      
      // Regname. channel_num, dma_instance, wdata  (Channel number irrelevant here, as global/common registers)
      DMA_REG_WRITE (dma_register, 0, wdata);  
      DMA_REG_READ  (dma_register, 0, rdata);
      
      exp_data = wdata & register_mask;
      if (rdata != exp_data) begin
        `uvm_error(get_full_name(), $sformatf("Register Write-Read DATA MISMATCH [Reg=%s wdata=h%016h. Reg_MASK=h%016h. EXP read-data=h%016h. ACT read-data=h%016h", 
                                                                                  dma_register.name(), wdata, register_mask, exp_data, rdata))
      end
    end

    // ----------------------------------------------------------
    // CMB Blocks and Channel Registers

    for (int channel=0; channel <= 7; channel++) begin             // TBD only the channels which are implemented. Rest should have DEC/SLVERR
      for (int reg_idx = 0; reg_idx <= 12; reg_idx++) begin

        case (reg_idx)
          0  : begin   dma_register = DMA_CH_CTRL        ;        register_mask = 64'h0000_0000_ffff_ffff;        end  
          1  : begin   dma_register = DMA_CH_CFG         ;        register_mask = 64'h00ff_ffff_ffff_ffff;        end
          2  : begin   dma_register = DMA_CH_SRC_ADDR    ;        register_mask = 64'hffff_ffff_ffff_ffff;        end
          3  : begin   dma_register = DMA_CH_DST_ADDR    ;        register_mask = 64'hffff_ffff_ffff_ffff;        end
          4  : begin   dma_register = DMA_CH_XBYTESIZE   ;        register_mask = 64'hffff_ffff_ffff_ffff;        end
          5  : begin   dma_register = DMA_CH_YROWSIZE    ;        register_mask = 64'hffff_ffff_ffff_ffff;        end
          6  : begin   dma_register = DMA_CH_TRAN_CFG    ;        register_mask = 64'hffff_ffff_ffff_ffff;        end
          7  : begin   dma_register = DMA_CH_XADDRINC    ;        register_mask = 64'h0000_ffff_ffff_ffff;        end
          8  : begin   dma_register = DMA_CH_YADDRSTRIDE ;        register_mask = 64'h0000_ffff_ffff_ffff;        end
          9  : begin   dma_register = DMA_CH_LINK_DESCR  ;        register_mask = 64'hffff_ffff_ffff_ffff;        end
          10 : begin   dma_register = DMA_CH_STATUS      ;        register_mask = 64'h0000_0000_0000_0000;        end
          11 : begin   dma_register = DMA_CH_ERR_INFO    ;        register_mask = 64'h0000_0000_0000_0000;        end
          12 : begin   dma_register = DMA_CH_REQ_BUS_CTRL;        register_mask = 64'hffff_ffff_ffff_ffff;        end
        endcase 

        // randomize_data(wdata);
        wdata = '1;

        // Regname. channel_num, dma_instance, wdata
        DMA_REG_WRITE (dma_register, channel, wdata);  
        DMA_REG_READ  (dma_register, channel, rdata);
        
        exp_data = wdata & register_mask;
        if (rdata != exp_data) begin
          `uvm_error(get_full_name(), $sformatf("Register Write-Read DATA MISMATCH [Reg=%s channel=%01d wdata=h%016h. Reg_MASK=h%016h. EXP read-data=h%016h. ACT read-data=h%016h", 
                                                                                    dma_register.name(), channel, wdata, register_mask, exp_data, rdata))
        end
      
      end
    end

    // ----------------------------------------------------------
    `uvm_info(get_full_name(), $sformatf("END : DMA IP Register Access Test"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:dma_ip_csr_reg_access_test

`endif	// __DMA_IP_CSR_REG_ACCESS_TEST__
