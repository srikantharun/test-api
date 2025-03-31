// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test
//              Using Def Based Command Format
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_DEFBASED_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_DEFBASED_TEST_SV

class aic_ls_dmc_cmdb_defbased_test extends aic_ls_dmc_cmdb_tc_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_defbased_test);

  addr_gen_cmdformat_t m_command_format;

  function new (string name="aic_ls_dmc_cmdb_defbased_test", uvm_component parent);
    super.new (name, parent);
    m_command_format = CMDFORMAT_DEF_BASED;
    m_test_iteration = 7;
  endfunction : new

  virtual function void randomize_sequences();
    int unsigned num_bytes;
    int unsigned tlast_count;
    foreach (AIC_LS_DMC_IFD_DEVICE[i]) begin
      m_ifd_seq[i] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",i));
    end
    foreach (AIC_LS_DMC_ODR_DEVICE[i]) begin
      m_odr_seq[i] = aic_ls_odr_seq_t::type_id::create($sformatf("m_odr_seq_%0d",i));
    end
    foreach (m_ifd_seq[i]) begin
      m_ifd_seq[i].m_prev_tlast_count = m_ifd_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_ifd_seq[i].randomize() with {
        m_device          == AIC_LS_DMC_IFD_DEVICE[i];
        m_ag_cmd_format   == m_command_format;
        m_cid == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
    end
    foreach (m_odr_seq[i]) begin
      m_odr_seq[i].m_prev_tlast_count = m_odr_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_odr_seq[i].randomize() with {
        m_device          == AIC_LS_DMC_ODR_DEVICE[i];
        m_ag_cmd_format   == m_command_format;
        m_cid == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_odr_seq!")
      end
    end
  endfunction
endclass:aic_ls_dmc_cmdb_defbased_test
`endif

