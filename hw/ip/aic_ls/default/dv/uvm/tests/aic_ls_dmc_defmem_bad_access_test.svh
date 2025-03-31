// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:  tests IFD/ODR instruction memory access, by attempting writing/reading all the unused memory range and making sure we're getting an error.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_DEFMEM_BAD_ACCESS_TEST_SV
`define GUARD_AIC_LS_DMC_DEFMEM_BAD_ACCESS_TEST_SV

class aic_ls_dmc_defmem_bad_access_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_dmc_defmem_bad_access_test);

  function new (string name="aic_ls_dmc_defmem_bad_access_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void start_of_simulation_phase (uvm_phase phase);
    time test_timeout = 5ms;
    super.start_of_simulation_phase(phase);
    // set cfg axi mst and slv agent in config db to be retrieved by non uvm components like report catcher and sequences
    uvm_config_db#(time)::set(null,"*", "TEST_TIMEOUT", test_timeout);
  endfunction: start_of_simulation_phase

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_NONE)
    m_env.m_aic_ls_agt.vif.drv.disable_rdataX_aserrtion <= 1;
    m_test_iteration = 1;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_NONE)
  endtask

  virtual task cfg_test_axi_write(cfg_addr_t addr);
    aic_ls_axi_cfg_if_write_sequence cfg_write;
    cfg_write = aic_ls_axi_cfg_if_write_sequence::type_id::create("cfg_write");
    if (!(cfg_write.randomize() with {
        cfg_addr        == addr;
        cfg_wstrb       == 8'hFF;
        use_random_strb == 1;
        burst_length    == 1;
        sequence_length == 1;
    })) begin
      `uvm_fatal(get_name(), "Randomization failed for cfg_write!")
    end
    cfg_write.cfg_data_q.push_back('0);
    cfg_write.start(m_env.m_axi_system_env.master[0].sequencer);
    if(cfg_write.write_txn.bresp == 2) begin // 2 = AXI_SLVERR_RESPONSE
      `uvm_info(get_name(), $sformatf("Address= 0x%0x and BRESP = %s", addr, cfg_write.write_txn.bresp), UVM_LOW)
    end else begin
      `uvm_error(get_name(), $sformatf("Address= 0x%0x and BRESP = %s", addr, cfg_write.write_txn.bresp))
    end
  endtask

  virtual task cfg_test_axi_read(cfg_addr_t addr);
    aic_ls_axi_cfg_if_read_sequence cfg_read;
    cfg_read = aic_ls_axi_cfg_if_read_sequence::type_id::create("cfg_read");
    if (!(cfg_read.randomize() with {
        cfg_addr        == addr;
        sequence_length == 1;
    })) begin
      `uvm_fatal(get_name(), "Randomization failed for cfg_write!")
    end
    cfg_read.start(m_env.m_axi_system_env.master[0].sequencer);
    foreach(cfg_read.read_tran.rresp[j]) begin
      if(cfg_read.read_tran.rresp[j] == 2) begin // 2 = AXI_SLVERR_RESPONSE
       `uvm_info(get_name(), $sformatf("Address= 0x%0x and RRESP[%0d] = %s", addr, j, cfg_read.read_tran.rresp[j]), UVM_LOW)
      end else begin
       `uvm_error(get_name(), $sformatf("Address= 0x%0x and RRESP[%0d] = %s", addr, j, cfg_read.read_tran.rresp[j]))
      end
    end
  endtask

  virtual task test_seq();
    cfg_addr_t mem_addr, mem_addr_q[$];

    for (int j=0; j < AIC_LS_ENV_DMC_NUM_DEVICE; j++) begin
      for (int i=AIC_LS_ENV_DMC_DM_DEPTH*8; i < AIC_LS_ENV_DEVICE_OFFSET; i=i+8) begin
        mem_addr = (m_env_cfg.m_cid_offset * m_env_cfg.m_cid) + AIC_LS_ENV_DESCMEM_OFFSET + (AIC_LS_ENV_DEVICE_OFFSET * j ) + i;
        `uvm_info (get_name(), $sformatf("pushing address 0x%0x to queue", mem_addr), UVM_HIGH)
        mem_addr_q.push_back(mem_addr);
      end
    end

    foreach (mem_addr_q[i]) begin
      cfg_test_axi_write(mem_addr_q[i]);
      cfg_test_axi_read(mem_addr_q[i]);
    end
  endtask

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    // Lets check the memory part that's not functional!
    test_seq();

    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_NONE)
  endtask : main_phase
endclass:aic_ls_dmc_defmem_bad_access_test
`endif
