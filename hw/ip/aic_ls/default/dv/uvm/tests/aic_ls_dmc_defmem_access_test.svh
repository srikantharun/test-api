// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: tests IFD/ODR instruction memory access, by writing/reading all the real memories.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_DEFMEM_ACCESS_TEST_SV
`define GUARD_AIC_LS_DMC_DEFMEM_ACCESS_TEST_SV

class aic_ls_dmc_defmem_access_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_dmc_defmem_access_test);

  function new (string name="aic_ls_dmc_defmem_access_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_NONE)

    m_test_iteration = 2;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_NONE)
  endtask

  function void update_data(cfg_data_t wdata, cfg_wstrb_t wstrb, ref cfg_data_t data);
    for (int i=0; i < 8; i++) begin
      if (wstrb[i] == 1) begin
        data[i*8 +: 8] = wdata[i*8 +: 8];
      end
    end
  endfunction

  virtual task main_phase(uvm_phase phase);
    aic_ls_axi_master_read_sequence axi_read;
    aic_ls_axi_master_write_sequence axi_write;
    cfg_addr_t mem_addr, mem_addr_q[$];
    cfg_data_t rdata, wdata, mem_data_q[$];
    cfg_wstrb_t wstrb;

    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    for (int j=0; j < AIC_LS_ENV_DMC_NUM_DEVICE; j++) begin
      for (int i=0; i < AIC_LS_ENV_DMC_DM_DEPTH*8; i=i+8) begin  // actual instr mem goes from 0x0 -> 0x400
        mem_addr = (m_env_cfg.m_cid_offset * m_env_cfg.m_cid) + AIC_LS_ENV_DESCMEM_OFFSET + (AIC_LS_ENV_DEVICE_OFFSET * j ) + i;
        `uvm_info (get_name(), $sformatf("pushing address 0x%0x to queue", mem_addr), UVM_HIGH)
        mem_addr_q.push_back(mem_addr);
        mem_data_q.push_back(0); // init data
      end
    end

    foreach (mem_addr_q[i]) begin
      `uvm_info (get_name(), $sformatf("mem_addr_q[%0d]: 0x%0x", i, mem_addr_q[i]), UVM_LOW)
    end

    for (int iter=0; iter < m_test_iteration; iter++) begin
      foreach (mem_addr_q[i]) begin
        // FD WR
        for (int j=0; j < AIC_LS_ENV_AXI_HP_DATA_W; j++) begin
          wdata[j] = bit'($urandom_range(0,1));
        end

        case ($urandom_range(0,14))
          0:  wstrb = 8'b0000_0001;
          1:  wstrb = 8'b0000_0011;
          2:  wstrb = 8'b0000_0111;
          3:  wstrb = 8'b0000_1111;
          4:  wstrb = 8'b0001_1111;
          5:  wstrb = 8'b0011_1111;
          6:  wstrb = 8'b0111_1111;
          7:  wstrb = 8'b1111_1111;
          8:  wstrb = 8'b1000_0000;
          9:  wstrb = 8'b1100_0000;
          10: wstrb = 8'b1110_0000;
          11: wstrb = 8'b1111_0000;
          12: wstrb = 8'b1111_1000;
          13: wstrb = 8'b1111_1100;
          14: wstrb = 8'b1111_1110;
        endcase

        if (iter==0) wstrb = 8'hFF; // avoid x's in read data later

        cfg_axi_write(mem_addr_q[i], wdata, wstrb);
        update_data(wdata, wstrb, mem_data_q[i]);
        #100ns;

        cfg_axi_read(mem_addr_q[i], rdata);

        if (mem_data_q[i] != rdata) begin
          `uvm_error(get_name(), $sformatf("FD_WR != FD_RD at address: 0x%0x FD_WR: 0x%0x FD_RD: 0x%0x wstrb: 0x%2x", mem_addr_q[i], mem_data_q[i], rdata, wstrb))
        end else begin
          `uvm_info (get_name(), $sformatf("[%0d] FD_WR == FD_RD  to L1 address: 0x%0x is 0x%0x wstrb: 0x%2x", i, mem_addr_q[i], rdata, wstrb), UVM_NONE)
        end
      end
    end

    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_NONE)
  endtask : main_phase
endclass:aic_ls_dmc_defmem_access_test
`endif
