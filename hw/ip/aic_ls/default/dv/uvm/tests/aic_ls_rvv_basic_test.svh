// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AIC RVV basic test
//      A very basic test that preloads l1 with random data, and then does 200 reads/writes to it.
// Owner: Rafael Frangulyan Polyak <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_RVV_BASIC_TEST_SV
`define GUARD_AIC_LS_RVV_BASIC_TEST_SV

class aic_ls_rvv_basic_test extends aic_ls_dmc_cmdb_tc_test;
  `uvm_component_utils (aic_ls_rvv_basic_test);

  rvv_sequence_t              rvv_seq;
  int rvv_repeat_cycles = 1;  // how many times will the RVV transaction repeat

  function new (string name="aic_ls_rvv_basic_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_name(), "build_phase() started.",UVM_LOW)
    rvv_seq = rvv_sequence_t::type_id::create("rvv_seq");
    `uvm_info(get_name(), "build_phase() ended.",UVM_LOW)
  endfunction: build_phase

  virtual task configure_phase(uvm_phase phase);
    m_init_l1_en = 1;
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 200;
    rvv_seq.connections_num = AIC_LS_ENV_RVV_CONNECTIONS;
    rvv_seq.repeat_cycles = rvv_repeat_cycles;
    rvv_seq.m_pword_size = m_env_cfg.m_pword_size;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task test_seq();
    `uvm_info(get_name(), "Start of test", UVM_LOW)

    init_l1(); // write to l1 before test starts
    
    for (int iter=0; iter < m_test_iteration; iter++) begin
      fork
        rvv_seq.start(m_env.m_rvv_agent.m_rvv_sequencer);
      join
      #10;
    end

    #20us;
    `uvm_info(get_name(), "End of test", UVM_LOW)
  endtask

endclass:aic_ls_rvv_basic_test
`endif

