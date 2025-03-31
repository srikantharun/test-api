// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 Memory Test
//  - Backdoor Write L1 then Frontdoor Read
//  - Frontdoor Write L1 then Frontdoor Read
//  - Finally Backdoor Read
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_L1_MEM_TEST_SV
`define GUARD_AIC_DMC_L1_MEM_TEST_SV

class aic_ls_l1_mem_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_l1_mem_test);

  typedef bit[AIC_LS_ENV_AXI_HP_ADDR_W-1:0] hp_addr_t;
  typedef bit[AIC_LS_ENV_AXI_HP_DATA_W-1:0] hp_data_t;
  

  function new (string name="aic_ls_l1_mem_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    // for (int i=0; i < AIC_LS_ENV_DMC_NUM_DEVICE; i++) begin
    //    m_env.m_dmc_data_scb[i].m_sw_bypass_en = 1;
    // end
    m_test_iteration = 10;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task main_phase(uvm_phase phase);
    aic_ls_axi_master_read_sequence axi_read;
    aic_ls_axi_master_write_sequence axi_write;
    hp_addr_t mem_addr, mem_addr_q[$], full_mem_addr;
    hp_data_t bkdr_wdata, bkdr_rdata, rdata, wdata, temp_data;
    data_sb_axis_quarter_data_t data_list[L1_SUB_BANKS_PER_BANK];
    int index;

    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    for (int i=6; i < AIC_LS_ENV_AXI_HP_ADDR_W-1; i++) begin
      mem_addr = m_env_cfg.m_l1_start_addr;
      mem_addr[i] = 1;
      for (int j=0; j < m_test_iteration; j++) begin
        if (mem_addr < m_env_cfg.m_l1_end_addr) begin
          full_mem_addr = mem_addr+ (m_env_cfg.m_cid_offset * m_env_cfg.m_cid);
          full_mem_addr[5:0] = 0;
          mem_addr_q.push_back(full_mem_addr);
          full_mem_addr = full_mem_addr + $urandom_range(2**(i-2), 2**(i-1));
          full_mem_addr[5:0] = 0;
          if (full_mem_addr < m_env_cfg.m_l1_full_end_addr) begin
            mem_addr_q.push_back(full_mem_addr);
          end
        end
      end
    end

    // foreach (mem_addr_q[i]) begin
    //   `uvm_info (get_name(), $sformatf("mem_addr_q[%0d]: 0x%0x", i, mem_addr_q[i]), UVM_LOW)
    // end

    foreach (mem_addr_q[i]) begin

      // BD WR
      index = (mem_addr_q[i] - (m_env_cfg.m_l1_start_addr + (m_env_cfg.m_cid_offset * m_env_cfg.m_cid)))/m_env_cfg.m_pword_size;
      for (int j=0; j < AIC_LS_ENV_AXI_HP_DATA_W; j++) begin
        bkdr_wdata[j] = bit'($urandom_range(0,1));
      end
      bkdr_wdata[31:0] = mem_addr_q[i]; // for ease of waveform debug
      `uvm_info (get_name(), $sformatf("Depositing data for - mem_addr_q[%0d]: 0x%0x. index val is %d", i, mem_addr_q[i], index), UVM_LOW)
      hdl_write(index, bkdr_wdata);

      // FD RD
      axi_read = aic_ls_axi_master_read_sequence::type_id::create("axi_read");
      if (!(axi_read.randomize() with {
          mem_addr        == mem_addr_q[i];
          sequence_length == 1;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_read!")
      end
      axi_read.start(m_env.m_axi_system_env.master[1].sequencer);
      #100ns;
      rdata = axi_read.rsp.data[0];

      if (bkdr_wdata != rdata) begin
        `uvm_error(get_name(), $sformatf("BD_WR != FD_RD at L1 address: 0x%0x BD_WR: 0x%0x FD_RD: 0x%0x", mem_addr_q[i], bkdr_wdata, rdata))
      end else begin
        `uvm_info (get_name(), $sformatf("[%0d] BD_WR == FD_RD to L1 address: 0x%0x is 0x%0x", i, mem_addr_q[i], rdata), UVM_LOW)
      end

      // FD WR
      axi_write = aic_ls_axi_master_write_sequence::type_id::create("axi_write");
      wdata = bkdr_wdata;
      wdata[63:32]=  mem_addr_q[i];
      axi_write.mem_data_q.push_back(wdata);
      if (!(axi_write.randomize() with {
          mem_addr        == mem_addr_q[i];
          sequence_length == 1;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_write!")
      end
      axi_write.start(m_env.m_axi_system_env.master[1].sequencer);
      #100ns;

      // FD RD
      axi_read = aic_ls_axi_master_read_sequence::type_id::create("axi_read");
      if (!(axi_read.randomize() with {
          mem_addr        == mem_addr_q[i];
          sequence_length == 1;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_read!")
      end
      axi_read.start(m_env.m_axi_system_env.master[1].sequencer);
      #100ns;
      rdata = axi_read.rsp.data[0];
      if (wdata != rdata) begin
        `uvm_error(get_name(), $sformatf("FD_WR != FD_RD at L1 address: 0x%0x FD_WR: 0x%0x FD_RD: 0x%0x", mem_addr_q[i], wdata, rdata))
      end else begin
        `uvm_info (get_name(), $sformatf("[%0d] FD_WR == FD_RD  to L1 address: 0x%0x is 0x%0x", i, mem_addr_q[i], rdata), UVM_LOW)
      end

      // BD READ
      bkdr_rdata = hdl_read(index);

      if (bkdr_rdata != rdata) begin
        `uvm_error(get_name(), $sformatf("BD_RD != FD_RD at L1 address: 0x%0x BD_RD: 0x%0x FD_RD: 0x%0x", mem_addr_q[i], bkdr_rdata, rdata))
      end else begin
        `uvm_info (get_name(), $sformatf("[%0d] BD_RD == FD_RD to L1 address: 0x%0x Data: 0x%0x", i, mem_addr_q[i], bkdr_rdata), UVM_LOW)
      end
    end
    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_LOW)
  endtask : main_phase
endclass:aic_ls_l1_mem_test
`endif
