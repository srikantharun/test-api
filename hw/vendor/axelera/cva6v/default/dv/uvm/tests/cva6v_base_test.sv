// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Base test. All tests
//              inherit from this class
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef GUARD_CVA6V_BASE_TEST_SV
`define GUARD_CVA6V_BASE_TEST_SV

class cva6v_base_test extends uvm_test;

  `uvm_component_utils(cva6v_base_test)

  cva6v_env                  m_env;
  cva6v_env_cfg              m_env_cfg;
  cva6v_axi_system_cfg       m_axi_sys_cfg;

  // Handles testbench interfaces
  typedef virtual cva6v_rvvi_eot_if#(rvvi_trace_t) cva6v_rvvi_eot_if_t;

  cva6v_rvvi_eot_if_t rvvi_eot_vif;  // virtual peripheral status

  bit                        m_is_regression;

  function new(string name = "cva6v_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(5ms,1);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_name(), "build_phase() started.",UVM_LOW)

    m_env_cfg = cva6v_env_cfg::type_id::create("m_env_cfg");
    m_env = cva6v_env::type_id::create("m_env", this);
    randomize_env_cfg();

    if (m_env_cfg.m_svt_axi_vip_en) begin
      m_axi_sys_cfg = cva6v_axi_system_cfg::type_id::create("m_axi_sys_cfg");
      uvm_config_db#(cva6v_axi_system_cfg)::set(this, "m_env", "m_axi_sys_cfg", m_axi_sys_cfg);
      uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.slave*.sequencer.run_phase", "default_sequence", svt_axi_slv_mem_rsp_seq::type_id::get());
    end

    uvm_config_db#(cva6v_env_cfg)::set(this, "m_env", "m_env_cfg", m_env_cfg);
    void'($value$plusargs("REGRESSION=%0d", m_is_regression));

    if (!uvm_config_db#(cva6v_rvvi_eot_if_t)::get(this, "", "rvvi_eot_vif", rvvi_eot_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find rvvi_eot_vif handle of type %s in uvm_config_db. dbg: %s", $typename(rvvi_eot_vif), $typename(cva6v_rvvi_eot_if_t)))
    end else begin
      `uvm_info("VIF", $sformatf("Found rvvi_eot_vif handle of type %s in uvm_config_db", $typename(rvvi_eot_vif)), UVM_NONE)
    end
  endfunction: build_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    `uvm_info(get_name(), "end_of_elaboration_phase() started.", UVM_LOW)
    uvm_top.set_report_verbosity_level_hier(UVM_NONE); // avoid sim.log full of uvm info
    uvm_top.print_topology();
    `uvm_info(get_name(), "end_of_elaboration_phase() ended.", UVM_LOW)
  endfunction: end_of_elaboration_phase

  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
    uvm_config_db#(cva6v_env)::set(null,"*", "CVA6V_ENV", m_env);
  endfunction: start_of_simulation_phase

  virtual task reset_phase(uvm_phase phase);
    super.reset_phase(phase);
    phase.raise_objection(this);
    `uvm_info(get_name(), "reset_phase() started.",UVM_LOW)
    repeat (2) @ (posedge rvvi_eot_vif.clk_i);
    wait ((rvvi_eot_vif.rst_ni == 1'b1));
    `uvm_info(get_name(), "reset_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask: reset_phase


  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info(get_name(), "configure_phase() started.",UVM_LOW)

    parse_c_mem_log();
    foreach (simple_mem[i]) begin
      m_env.m_axi_system_env.slave[0].axi_slave_mem.write(i, simple_mem[i]);
    end
    m_env.m_axi_system_env.slave[0].axi_slave_mem.set_meminit(3);

    `uvm_info(get_name(), "configure_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask: configure_phase

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    phase.raise_objection(this);
    `uvm_info(get_name(), "main_phase() started.",UVM_LOW)

    rvvi_eot_vif.wait_end_of_test(drain_cycles); // already has timeout mechanism implemented inside

    `uvm_info(get_name(), "main_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask: main_phase

  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    super.final_phase(phase);
    `uvm_info(get_name(), "final_phase() started.",UVM_LOW)
    svr = uvm_report_server::get_server();
    if (svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR)) begin
      `uvm_info(get_name(), "\nSvtTestEpilog: Failed\n", UVM_NONE)
    end else begin
      `uvm_info(get_name, "\nSvtTestEpilog: Passed\n", UVM_NONE)
    end
    `uvm_info(get_name(), "final_phase() ended.",UVM_LOW)
    uvm_top.set_report_verbosity_level_hier(UVM_LOW); // re-enable UVM report catcher and server
  endfunction: final_phase

  virtual function void randomize_env_cfg();
    if (!(m_env_cfg.randomize())) begin
      `uvm_fatal(get_name(), "Randomization failed for m_env_cfg!")
    end
  endfunction

endclass:cva6v_base_test

`endif // GUARD_AI_CORE_LS_BASE_TEST_SV
