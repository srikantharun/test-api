// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_COMMON_SEQ_LIB_ENV_SV
`define GUARD_COMMON_SEQ_LIB_ENV_SV

class common_seq_lib_env extends uvm_env;

  `uvm_component_utils(common_seq_lib_env)

  svt_axi_system_env axi_system_env;
  axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  cust_svt_axi_system_configuration axi_cfg;

  /** Class Constructor */
  function new(string name = "common_seq_lib_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    axi_cfg = cust_svt_axi_system_configuration::type_id::create("axi_cfg");
    uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", axi_cfg);
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)

  endfunction : connect_phase

endclass : common_seq_lib_env

`endif  // GUARD_COMMON_SEQ_LIB_ENV_SV

