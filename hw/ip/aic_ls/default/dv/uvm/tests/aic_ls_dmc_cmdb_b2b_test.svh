// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test
//              Using L1 TC Fabric
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_DMC_CMDB_B2B_TEST_SV
`define GUARD_AIC_DMC_DMC_CMDB_B2B_TEST_SV

class aic_ls_dmc_cmdb_b2b_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_b2b_test);

  int unsigned m_ptr_index[AIC_LS_ENV_DMC_NUM_DEVICE];
  int unsigned m_device_start = 0;
  int unsigned m_device_end = AIC_LS_ENV_DMC_NUM_DEVICE;
  addr_gen_cmdformat_t m_cmd_format_q[$];
  int unsigned m_num_dim_q[$];
  bit m_toggle_odr_addr;
  bit m_set_odr_addr = 1;

  function new (string name="aic_ls_dmc_cmdb_b2b_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void randomize_sequences(int dev, bit is_last);
    if (dev < AIC_LS_ENV_IFD_NUM_DEVICE) begin
      m_ifd_seq[dev] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",dev));
      m_ifd_seq[dev].m_enable_cmdb = 0;
      if (!(m_ifd_seq[dev].randomize() with {
        if (m_cmd_format_q.size()!= 0) m_ag_cmd_format inside {m_cmd_format_q};
        if (m_num_dim_q.size()!= 0) m_ag_num_dim inside {m_num_dim_q};
        m_device == AIC_LS_DMC_IFD_DEVICE[dev];
        m_cid == m_env.m_env_cfg.m_cid;
        m_wait_for_status == is_last;
        m_wait_data_done_en == 0;
        m_ag_dim_def_ptr  == m_ptr_index[dev]*4; // avoid overlapping pointers
        m_ag_loop_def_ptr == m_ptr_index[dev]*4 + 64; // avoid overlapping pointers
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
      if (m_ifd_seq[dev].m_ag_cmd_format inside {CMDFORMAT_DEF_BASED, CMDFORMAT_OFFSET_BASED}) begin
        m_ptr_index[dev] += 1;
        if (m_ptr_index[dev]==15) begin
          m_ptr_index[dev] = 0;
          `uvm_info (get_name(), "resetting m_ptr_index to 0", UVM_LOW)
        end
      end
    end else begin
      m_odr_seq[dev-AIC_LS_ENV_IFD_NUM_DEVICE] = aic_ls_odr_seq_t::type_id::create($sformatf("m_odr_seq_%0d",dev-AIC_LS_ENV_IFD_NUM_DEVICE));
      m_odr_seq[dev-AIC_LS_ENV_IFD_NUM_DEVICE].m_enable_cmdb = 0;
      m_toggle_odr_addr = !m_toggle_odr_addr;
      if (!(m_odr_seq[dev-AIC_LS_ENV_IFD_NUM_DEVICE].randomize() with {
        if (m_cmd_format_q.size()!= 0) m_ag_cmd_format inside {m_cmd_format_q};
        if (m_num_dim_q.size()!= 0) m_ag_num_dim inside {m_num_dim_q};
        m_device          == AIC_LS_DMC_ODR_DEVICE[dev-AIC_LS_ENV_IFD_NUM_DEVICE];
        // toggle b2b address so they don't mess with scoreboarding (i.e. do not try to write when SB expects data from it)
        if (dev-AIC_LS_ENV_IFD_NUM_DEVICE == 0 && m_set_odr_addr) m_ag_mem_baseaddr == 'h800_0000 + m_env.m_env_cfg.m_cid * (1 << 28) + (m_toggle_odr_addr * 'h10_0000);
        if (dev-AIC_LS_ENV_IFD_NUM_DEVICE == 1 && m_set_odr_addr) m_ag_mem_baseaddr == 'h820_0000 + m_env.m_env_cfg.m_cid * (1 << 28) + (m_toggle_odr_addr * 'h10_0000);
        m_cid == m_env.m_env_cfg.m_cid;
        m_wait_for_status == is_last;
        m_ag_dim_def_ptr  == m_ptr_index[dev]*4; // avoid overlapping pointers
        m_ag_loop_def_ptr == m_ptr_index[dev]*4 + 64; // avoid overlapping pointers
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_odr_seq!")
      end
      if (m_odr_seq[dev-AIC_LS_ENV_IFD_NUM_DEVICE].m_ag_cmd_format inside {CMDFORMAT_DEF_BASED, CMDFORMAT_OFFSET_BASED}) begin
        m_ptr_index[dev] += 1;
        if (m_ptr_index[dev]==15) begin
          m_ptr_index[dev] = 0;
          `uvm_info (get_name(), $sformatf("resetting m_ptr_index[%0d] to 0", dev), UVM_LOW)
        end
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
    for (int dev=m_device_start; dev < m_device_end; dev++) begin
      enable_cmdblk(dev);
      for (int iter=0; iter < m_test_iteration; iter++) begin
        randomize_sequences(dev, (iter==m_test_iteration-1));
        pre_configure_seq(dev);
        case (dev)
          0: m_ifd_seq[0].start(null); // mvm ifd0
          1: m_ifd_seq[1].start(null); // mvm ifd1
          //2: m_ifd_seq[2].start(null); // mvm ifd2
          3: m_ifd_seq[3].start(null); // mvm ifdw
          4: m_ifd_seq[4].start(null); // dwpu ifd0
          5: m_ifd_seq[5].start(null); // dwpu ifd1
          6: m_odr_seq[0].start(null); // mvm odr
          7: m_odr_seq[1].start(null); // dwpu_odr
        endcase
        `uvm_info (get_name(), $sformatf("Iteration %0d of %0d for %s done", iter, m_test_iteration-1, AIC_LS_DMC_DEVICE_NAME[dev]), UVM_LOW)
      end
    end
  endtask

  virtual task pre_configure_seq(int dev);
    // place holder for flexibility
  endtask

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);
    test_seq();
    #10us; // wait for all b2b txns to finish
    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_LOW)
  endtask : main_phase

endclass:aic_ls_dmc_cmdb_b2b_test
`endif

