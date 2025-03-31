// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 Memory Test
//  - Backdoor Write L1 then Frontdoor Read
//  - Frontdoor Write L1 then Frontdoor Read
//  - Finally Backdoor Read
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_L1_MEM_B2B_TEST_SV
`define GUARD_AIC_LS_L1_MEM_B2B_TEST_SV

class aic_ls_l1_mem_b2b_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_l1_mem_b2b_test);

  typedef bit[AIC_LS_ENV_AXI_HP_ADDR_W-1:0] hp_addr_t;
  typedef bit[AIC_LS_ENV_AXI_HP_DATA_W-1:0] hp_data_t;
  typedef bit[AIC_LS_ENV_AXI_HP_DATA_W/2-1:0] half_data_t;

  string m_mem_path0;
  string m_mem_path1;
  hp_data_t m_l1_mem[hp_addr_t];

  function new (string name="aic_ls_l1_mem_b2b_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 10;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask
  
  virtual task check_axi_read();
    uvm_object obj;
    v_object v_obj;
    hp_addr_t axi_rd_addr;
    hp_data_t axi_rd_data;
    uvm_event axi_rd_evt = uvm_event_pool::get_global("aic_ls_axi_master_read_sequence_evt");
    axi_rd_evt.wait_trigger_data(obj);
    if (!$cast(v_obj, obj)) begin
      `uvm_fatal(get_name(), "Casting from uvm_object to v_object failed!")
    end
    axi_rd_addr = hp_addr_t'(v_obj.m_64bit_data);
    axi_rd_data = hp_data_t'(v_obj.m_512bit_data);
    if (m_l1_mem.exists(axi_rd_addr)) begin
      if (m_l1_mem[axi_rd_addr] != axi_rd_data) begin
        `uvm_error(get_name(), $sformatf("Data Mismatch! Addr: 0x%0x Data: 0x%0x Exp: 0x%0x", axi_rd_addr, axi_rd_data, m_l1_mem[axi_rd_addr]))
      end else begin
        `uvm_info(get_name(), $sformatf("Data Match! Addr: 0x%0x Data: 0x%0x", axi_rd_addr, axi_rd_data), UVM_LOW)
      end
    end else begin
      `uvm_error(get_name(), $sformatf("Read on uninitialized address! Addr: 0x%0x Data: 0x%0x", axi_rd_addr, axi_rd_data))
    end 
  endtask 

  virtual task main_phase(uvm_phase phase);
    aic_ls_axi_master_read_sequence axi_read, axi_read_q[$];
    aic_ls_axi_master_write_sequence axi_write;
    hp_addr_t mem_addr, mem_addr_q[$], full_mem_addr;
    hp_data_t rdata, wdata;

    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    for (int i=6; i < AIC_LS_ENV_AXI_HP_ADDR_W-1; i++) begin
      mem_addr = m_env_cfg.m_l1_start_addr;
      mem_addr[i] = 1;
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

    foreach (mem_addr_q[i]) begin
      `uvm_info (get_name(), $sformatf("mem_addr_q[%0d]: 0x%0x", i, mem_addr_q[i]), UVM_LOW)
    end

    foreach (mem_addr_q[i]) begin
       // FD WR
      axi_write = aic_ls_axi_master_write_sequence::type_id::create("axi_write");
      for (int j=0; j < AIC_LS_ENV_AXI_HP_DATA_W; j++) begin
        wdata[j] = bit'($urandom_range(0,1));
      end
      wdata[63:32]=  mem_addr_q[i];
      axi_write.mem_data_q.push_back(wdata);
      if (!(axi_write.randomize() with {
          mem_addr        == mem_addr_q[i];
          sequence_length == 1;
          b2b_en          == 1;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_write!")
      end
      axi_write.start(m_env.m_axi_system_env.master[1].sequencer);

      if (m_l1_mem.exists(mem_addr_q[i])) begin
        `uvm_info (get_name(), $sformatf("Updating addr 0x%0x  with data: 0x%0x",  mem_addr_q[i], wdata), UVM_LOW)
      end
      m_l1_mem[mem_addr_q[i]] = wdata;
    end

    #100ns;

    foreach (mem_addr_q[i]) begin
      // FD RD
      axi_read = aic_ls_axi_master_read_sequence::type_id::create("axi_read");
      if (!(axi_read.randomize() with {
          mem_addr        == mem_addr_q[i];
          burst_len       == 1;
          sequence_length == 1;
          b2b_en          == 1;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_read!")
      end
      axi_read_q.push_back(axi_read);
    end

    fork
      begin
        //foreach (axi_read_q[i]) begin
        for (int i=0; i < axi_read_q.size(); i++) begin
          automatic int a_i = i;
          fork begin
            `uvm_info (get_name(), $sformatf("AXI RD %0d of %0d started", a_i, axi_read_q.size()-1), UVM_LOW)
            axi_read_q[a_i].start(m_env.m_axi_system_env.master[1].sequencer);
            `uvm_info (get_name(), $sformatf("AXI RD %0d of %0d done", a_i, axi_read_q.size()-1), UVM_LOW)
          end join_none
        end
      end

      //foreach (axi_read_q[j]) begin
      for (int j=0; j < axi_read_q.size(); j++) begin
        check_axi_read();
        `uvm_info (get_name(), $sformatf("Check AXI RD %0d of %0d done", j,  axi_read_q.size()-1), UVM_LOW)
      end
    join

    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_LOW)
  endtask : main_phase
endclass:aic_ls_l1_mem_b2b_test
`endif
