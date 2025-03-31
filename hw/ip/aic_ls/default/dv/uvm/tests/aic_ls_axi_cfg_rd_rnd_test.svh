// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Random AXI Wr/Rd txn from LP master.
//   Tests only access and ignore read data from registers
//   as they are verified functionally in other tests.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_AXI_CFG_RD_RND_TEST_SV
`define GUARD_AIC_LS_AXI_CFG_RD_RND_TEST_SV

class aic_ls_rnd_axi_demoter extends aic_ls_demoter;
  `uvm_object_utils(aic_ls_rnd_axi_demoter)

  function new(string name="aic_ls_rnd_axi_demoter");
   super.new(name);
  endfunction

  function action_e catch();
    bit err;
    err = string_search(get_message(), "Monitor Check for X or Z on RDATA when RVALID is high"); // ignore X in rdata
    err = err | string_search(get_message(), "does not match mirrored value"); // ignore mirrored value
    if (err) begin
       set_severity(UVM_INFO);
    end
    return THROW;
  endfunction
endclass

// AI Core LS AXI random test-case class
class aic_ls_axi_cfg_rd_rnd_test extends aic_ls_base_test;

  // Registration with the factory
  `uvm_component_utils(aic_ls_axi_cfg_rd_rnd_test)

  uvm_reg m_reg_list[$];
  aic_ls_rnd_axi_demoter m_axi_rnd_demoter;

  // Class Constructor
  function new(string name = "aic_ls_axi_cfg_rd_rnd_test", uvm_component parent = null);
    super.new(name, parent);
    m_lp_axi_override = 1;
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_HIGH)
    super.build_phase(phase);
    // Apply the svt_axi_random_sequence
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.master[0].sequencer.main_phase", "default_sequence", svt_axi_master_random_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.master[0].sequencer.configure_phase", "default_sequence", svt_axi_master_random_sequence::type_id::get());
    m_axi_rnd_demoter = new();
    uvm_report_cb::add(null, m_axi_rnd_demoter);
    `uvm_info("build_phase", "Exiting...", UVM_HIGH)
  endfunction : build_phase

  virtual task pre_configure_phase(uvm_phase phase);
    super.pre_configure_phase(phase);
    uvm_config_db#(int unsigned)::set(this, "m_env.m_axi_system_env.master[0].sequencer.svt_axi_master_random_sequence", "sequence_length", 100);
    cust_svt_lp_axi_master_read_transaction::m_is_rd_not_wr = 0;
    m_env.m_aic_ls_agt.vif.drv.disable_rdataX_aserrtion <= 1;
  endtask: pre_configure_phase

  virtual task pre_main_phase(uvm_phase phase);
    super.pre_main_phase(phase);
    uvm_config_db#(int unsigned)::set(this, "m_env.m_axi_system_env.master[0].sequencer.svt_axi_master_random_sequence", "sequence_length", 1000);
    cust_svt_lp_axi_master_read_transaction::m_is_rd_not_wr = 1;
  endtask: pre_main_phase

  virtual task post_main_phase(uvm_phase phase);
    super.post_main_phase(phase);
    `uvm_info (get_name(), "post_main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    m_env.m_ls_regmodel.get_registers(m_reg_list);
    foreach (m_reg_list[i]) begin
      `uvm_info(get_name(), $sformatf("Reg[%0d] %s Addr: 0x%0x", i, m_reg_list[i].get_full_name(), m_reg_list[i].get_address()), UVM_NONE)
    end
    #100us;
    phase.drop_objection(this);
    `uvm_info (get_name(), "post_main_phase() ended.", UVM_LOW)
  endtask : post_main_phase

endclass : aic_ls_axi_cfg_rd_rnd_test
`endif

