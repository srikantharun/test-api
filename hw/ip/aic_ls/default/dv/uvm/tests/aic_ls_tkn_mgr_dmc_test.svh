// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Test that generates headers with prod/cons token for aic ls IFDs/ODRs
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_TKN_MGR_DMC_TEST_SV
`define GUARD_AIC_LS_TKN_MGR_DMC_TEST_SV

class aic_ls_tkn_mgr_dmc_test extends aic_ls_dmc_cmdb_tc_test;
  `uvm_component_utils (aic_ls_tkn_mgr_dmc_test);

  bit m_swep_en = 0;
  bit m_en_token_delay = 1;


  function new (string name="aic_ls_tkn_mgr_dmc_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  virtual function void build_phase(uvm_phase phase);
    `uvm_info(get_name(), "build_phase() started.",UVM_LOW)
    if (m_en_token_delay) begin
      set_type_override_by_type (token_agent_seq_item::get_type(), aic_ls_token_delay_seq_item::get_type());
    end
    super.build_phase(phase);
    `uvm_info(get_name(), "build_phase() ended.",UVM_LOW)
  endfunction: build_phase

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 3;
    enable_cmdblk();
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task post_main_phase(uvm_phase phase);
    super.post_main_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "post_main_phase() started.", UVM_LOW)
    reset_ls(); // for toggle coverage of valid signals going low
    phase.drop_objection(this);
    `uvm_info (get_name(), "post_main_phase() ended.", UVM_LOW)
  endtask

  virtual function void randomize_sequences();
    foreach (AIC_LS_DMC_IFD_DEVICE[i]) begin
      m_ifd_seq[i] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",i));
      m_ifd_seq[i].m_enable_cmdb = 0; // enable is done in test separately
    end
    foreach (AIC_LS_DMC_ODR_DEVICE[i]) begin
      m_odr_seq[i] = aic_ls_odr_seq_t::type_id::create($sformatf("m_odr_seq_%0d",i));
      m_odr_seq[i].m_enable_cmdb = 0; // enable is done in test separately
    end

    foreach (m_ifd_seq[i]) begin
      m_ifd_seq[i].m_prev_tlast_count = m_ifd_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_ifd_seq[i].randomize() with {
        m_ag_cmd_format          == CMDFORMAT_LINEAR;
        m_device                 == AIC_LS_DMC_IFD_DEVICE[i];
        m_use_token_mechanism    == 1;
        m_cid                    == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
    end
    foreach (m_odr_seq[i]) begin
      m_odr_seq[i].m_prev_tlast_count = m_odr_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_odr_seq[i].randomize() with {
        m_ag_cmd_format          == CMDFORMAT_LINEAR;
        m_device                 == AIC_LS_DMC_ODR_DEVICE[i];
        m_use_token_mechanism    == 1;
        m_cid                    == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_odr_seq!")
      end
    end
  endfunction
endclass:aic_ls_tkn_mgr_dmc_test
`endif

