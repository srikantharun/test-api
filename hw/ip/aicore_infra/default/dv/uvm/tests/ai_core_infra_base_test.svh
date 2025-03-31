`ifndef AI_CORE_INFRA_BASE_TEST_SVH
`define AI_CORE_INFRA_BASE_TEST_SVH
class ai_core_infra_base_test extends uvm_test;

  `uvm_component_utils(ai_core_infra_base_test)

  ai_core_infra_env env;

  axi_simple_reset_sequence           axi_reset_seq;
  axi_master_write_sequence           axi_wr_seq;
  axi_master_read_sequence            axi_rd_seq;

  bit [63:0] axi_write_data;
  bit [39:0] axi_addr_q[$];
  int        core_id;
  function new(string name = "ai_core_infra_base_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    string seq_name;
    super.build_phase(phase);

    env = ai_core_infra_env::type_id::create("env", this);

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());
    axi_reset_seq = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    axi_wr_seq    = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq    = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    uvm_config_db#(int)::get(uvm_root::get(), "", "core_id", core_id);
    `uvm_info(get_name, $sformatf("Got core_id: %0d", core_id), UVM_LOW)
  endtask

  /**
   * Calculate the pass or fail status for the test in the final phase method of the
   * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
   * test will fail.
   */
  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_NONE)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) +
        svr.get_severity_count(UVM_WARNING) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_NONE)
  endfunction: final_phase


endclass
`endif
