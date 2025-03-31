// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Inherited test from Alpha. Does AXI
//   transactions to HP AXI interface to L1 that generates
//   random transactions using built in SVT sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_AXI_CFG_RND_TEST_SV
`define GUARD_AIC_LS_AXI_CFG_RND_TEST_SV


class aic_ls_axi_cfg_random_transaction extends svt_axi_master_transaction;
  `uvm_object_utils(aic_ls_axi_cfg_random_transaction)
 
  typedef enum {
    CSR,
    CMDB,
    MEM
  } reg_type_t;

  rand reg_type_t m_reg_type;
  rand int unsigned m_addr_index;

  // Declare user-defined constraints
  constraint master_constraints {

    m_addr_index <= 19;  // addr offset varies from 0x00000 to (0x80000-1)

    // make sure our addresses make sense
    if (m_reg_type == CSR) addr == 'h200_0000 + ((1 << m_addr_index)-1);
    else if (m_reg_type == CMDB) addr == 'h280_0000 + ((1 << m_addr_index)-1);
    else addr == 'h300_0000 + ((1 << m_addr_index)-1);

    // AWLEN/ARLEN
    burst_length dist {
      6'd0           :/ 2,
      [6'd1 : 6'd62] :/ 10,
      6'd63          :/ 2
    };
    // AWSIZE/ARSIZE
    burst_size dist {
      3'h0          :/ 2,
      [3'h1 : 3'h5] :/ 10,
      3'h6          :/ 2
    };
    // AWBURST/ARBURST
    burst_type dist {
      svt_axi_transaction::FIXED := 30,
      svt_axi_transaction::INCR  := 40,
      svt_axi_transaction::WRAP  := 30
    };
    atomic_type == 0;
    cache_type  == 0;
    resp_user == 0;
    
    solve m_reg_type, m_addr_index before addr;
  }

  function new(string name = "cust_svt_axi_master_transaction");
    super.new(name);
  endfunction : new

endclass : aic_ls_axi_cfg_random_transaction



// AI Core LS AXI random test-case class
class aic_ls_axi_cfg_rnd_test extends aic_ls_base_test;

  // Registration with the factory
  `uvm_component_utils(aic_ls_axi_cfg_rnd_test)
  
  aic_ls_rnd_axi_demoter m_axi_rnd_demoter;

  // Class Constructor
  function new(string name = "aic_ls_axi_cfg_rnd_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_HIGH)
    super.build_phase(phase);

    // Apply the svt_axi_random_sequence
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.master[0].sequencer.main_phase",
                                            "default_sequence",
                                            svt_axi_master_random_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(
        this, "m_env.m_axi_system_env.master[0].sequencer.svt_axi_master_random_sequence",
        "sequence_length", 5000);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.slave[1].sequencer.run_phase",
                                            "default_sequence",
                                            axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("build_phase", "Exiting...", UVM_HIGH)
    m_init_l1_en = 1;
    set_type_override_by_type (svt_axi_master_transaction::get_type(), aic_ls_axi_cfg_random_transaction::get_type());
    m_axi_rnd_demoter = new();
    uvm_report_cb::add(null, m_axi_rnd_demoter);
  endfunction : build_phase
  
  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
    //m_env.m_tkn_mgr_ref_mdl.m_refmodel_en = 0; // disable refmodel connected to AXI txns
  endfunction: start_of_simulation_phase
  
  virtual task reset_phase(uvm_phase phase);
    super.reset_phase(phase);
    phase.raise_objection(this);
    m_env.m_aic_ls_agt.vif.drv.disable_rdataX_aserrtion <= 1;
    phase.drop_objection(this);
  endtask: reset_phase

endclass : aic_ls_axi_cfg_rnd_test
`endif

