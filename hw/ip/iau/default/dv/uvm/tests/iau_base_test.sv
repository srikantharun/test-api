
`ifndef GUARD_IAU_BASE_TEST_SV
`define GUARD_IAU_BASE_TEST_SV
// IAU_DPU base test class
class iau_base_test extends uvm_test;

  `uvm_component_utils(iau_base_test)

  axi_simple_reset_sequence rst_seq;
  iau_env env;

  iau_env_cfg m_env_cfg = new();

  cust_svt_axi_system_configuration cfg;

  uvm_status_e status;

  function new(string name = "iau_base_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    rst_seq  = axi_simple_reset_sequence::type_id::create("rst_seq", this);

    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");

    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    m_env_cfg = iau_env_cfg::type_id::create("m_env_cfg");
    if (!m_env_cfg.randomize()) `uvm_fatal(get_name, "Randomization Failed!")
    m_env_cfg.has_coverage = 1;

    uvm_config_db#(iau_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    env = iau_env::type_id::create("env", this);

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.sequencer.main_phase", "default_sequence", axi_null_virtual_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    uvm_top.set_timeout(10000us,1);
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  virtual task wait_cycles(int cycles = 1);
    repeat (cycles) 
      @(posedge env.axi_system_env.vif.common_aclk);
  endtask

  task check_exec_done();
    bit [63:0] data;
    data = ~0;
    //wait program done by checking IDLE state
    repeat (50) @(posedge env.axi_system_env.vif.common_aclk);
    //wait for state = idle = 0 : program is done
    while (|data[1:0]) begin // IDLE state == 0
      env.regmodel.cmdblk_status.read(status, data);
      `uvm_info ("run_phase", $sformatf("Read cmdblk_status, IDLE: %0d", data[1:0]), UVM_HIGH)
      repeat (100) @(posedge env.axi_system_env.vif.common_aclk);
    end

    `uvm_info ("run_phase", $sformatf("Program finished, iau in IDLE"), UVM_HIGH)
  endtask


  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_LOW)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR)
	 > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
  endfunction: final_phase
endclass

`endif // GUARD_IAU_BASE_TEST_SV
