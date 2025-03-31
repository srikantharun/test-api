// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test
//              Using L1 TC Fabric
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_DMC_CMDB_TC_TEST_SV
`define GUARD_AIC_DMC_DMC_CMDB_TC_TEST_SV

class aic_ls_dmc_cmdb_tc_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_tc_test);

  addr_gen_cmdformat_t m_cmd_format_q[$];
  int unsigned m_num_dim_q[$];
  int unsigned m_num_wait_per_iter =  1;

  function new (string name="aic_ls_dmc_cmdb_tc_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void randomize_sequences();
    foreach (AIC_LS_DMC_IFD_DEVICE[i]) begin
      m_ifd_seq[i] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",i));
    end
    foreach (AIC_LS_DMC_ODR_DEVICE[i]) begin
      m_odr_seq[i] = aic_ls_odr_seq_t::type_id::create($sformatf("m_odr_seq_%0d",i));
    end
    foreach (m_ifd_seq[i]) begin
      m_ifd_seq[i].m_prev_tlast_count = m_ifd_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_ifd_seq[i].randomize() with {
        if (m_cmd_format_q.size()!= 0) m_ag_cmd_format inside {m_cmd_format_q};
        if (m_num_dim_q.size()!= 0) m_ag_num_dim inside {m_num_dim_q};
        m_device == AIC_LS_DMC_IFD_DEVICE[i];
        m_cid == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
    end
    foreach (m_odr_seq[i]) begin
      m_odr_seq[i].m_prev_tlast_count = m_odr_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_odr_seq[i].randomize() with {
        if (m_cmd_format_q.size()!= 0) m_ag_cmd_format inside {m_cmd_format_q};
        if (m_num_dim_q.size()!= 0) m_ag_num_dim inside {m_num_dim_q};
        m_device          == AIC_LS_DMC_ODR_DEVICE[i];
        m_cid == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_odr_seq!")
      end
    end
  endfunction

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 10;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task test_seq();
    for (int iter=0; iter < m_test_iteration; iter++) begin
      randomize_sequences();
      `uvm_info (get_name(), "randomize_sequences() done!", UVM_LOW)
      fork
        m_ifd_seq[0].start(null); // mvm ifd0
        m_ifd_seq[1].start(null); // mvm ifd1
        m_ifd_seq[2].start(null); // mvm ifd2
        m_ifd_seq[3].start(null); // mvm ifdw
        m_ifd_seq[4].start(null); // dwpu ifd0
        m_ifd_seq[5].start(null); // dwpu ifd1
        m_odr_seq[0].start(null); // mvm odr
        m_odr_seq[1].start(null); // dwpu_odr
      join

      repeat (m_num_wait_per_iter) #50us; // for all mmio accesses to be done (they are the bottle neck)

      foreach (m_ifd_tlast_count[i]) begin  // update tlast index, so that in the next run, we wait for the correct signal
        update_tlast(.tlast_index(i), .is_ifd_not_odr(1));
      end
      foreach (m_odr_tlast_count[i]) begin  // update tlast index, so that in the next run, we wait for the correct signal
        update_tlast(.tlast_index(i), .is_ifd_not_odr(0));
      end
      `uvm_info (get_name(), $sformatf("Test Iteration %0d done.", iter), UVM_LOW)
      m_env.reset_addr_gen_refmodel();
    end
  endtask

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    test_seq();

    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_LOW)
  endtask : main_phase
endclass:aic_ls_dmc_cmdb_tc_test
`endif

