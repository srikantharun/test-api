// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_FABRIC_CSL_ENV_SV
`define GUARD_FABRIC_CSL_ENV_SV

class fabric_csl_env extends uvm_env;

  `uvm_component_utils(fabric_csl_env)

  svt_axi_system_env axi_system_env;
  axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  cust_svt_axi_system_configuration axi_cfg;
  pve_fabric_configuration pve_fabric_cfg;

  /** Class Constructor */
  function new(string name = "fabric_csl_env", uvm_component parent = null);
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

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)

    super.end_of_elaboration_phase(phase);
    //TODO: remove after SolvNet issue #01760068 is resolved
    foreach (axi_system_env.slave[i]) begin
      axi_system_env.slave[i].monitor.checks.disable_check(axi_system_env.slave[i].monitor.checks.signal_valid_awmpam_when_awvalid_high_check);
      axi_system_env.slave[i].monitor.checks.disable_check(axi_system_env.slave[i].monitor.checks.signal_valid_armpam_when_arvalid_high_check);
    end
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction : end_of_elaboration_phase


endclass : fabric_csl_env

`endif  // GUARD_FABRIC_CSL_ENV_SV

