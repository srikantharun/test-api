// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test
//              Using L1 TC Fabric
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_VTRSP_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_VTRSP_TEST_SV

class aic_ls_vtrsp_demoter extends aic_ls_demoter;
  `uvm_object_utils(aic_ls_vtrsp_demoter)

  function new(string name="aic_ls_vtrsp_demoter");
   super.new(name);
  endfunction

  function action_e catch();
    bit err;
    err = string_search(get_message(), "Monitor Check for X or Z on RDATA when RVALID is high");
    if (err) begin
       set_severity(UVM_INFO);
    end
    return THROW;
  endfunction
endclass

class aic_ls_dmc_cmdb_vtrsp_test extends aic_ls_dmc_cmdb_tc_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_vtrsp_test);

  int unsigned m_seq_counter;
  rand bit[1:0] m_vtrsp_mode;
  cfg_addr_t m_mem_base_addr;
  cfg_addr_t m_mem_offset;
  int m_mem_offset_increment = 'h06_0000;
  aic_ls_vtrsp_demoter m_vtrsp_demoter;
  bit m_alternating_vtrsp=1;
  bit m_wait_status = 1;
  bit m_wait_data_done = 1;
  int unsigned m_seq_index, m_ptr_index;
  aic_ls_device_index_t m_device_index[3];
  aic_ls_device_index_t m_current_device;
  bit m_vtrsp_supported;
  string m_irq_status;
  int unsigned test_iter = 0; // needed for ifdw ref model checking

  constraint C_VRTSP_MODE { soft m_vtrsp_mode dist { 1:=20, [2:3]:/ 80}; }

  function new (string name="aic_ls_dmc_cmdb_vtrsp_test", uvm_component parent);
    super.new (name, parent);
    m_seq_index =  0; // m_odr = 0, d_odr = 1
    m_irq_status = "";
    //m_device_index = DWPU_ODR;
    m_device_index ={MVM_ODR, DWPU_ODR, MVM_IFDW};
    m_vtrsp_supported = 1;
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_name(), "build_phase() started.",UVM_LOW)
    m_vtrsp_demoter = new();
    uvm_report_cb::add(null, m_vtrsp_demoter); // https://git.axelera.ai/ai-hw-team/triton/-/issues/2705
  endfunction

  virtual function void randomize_sequences();
    if (!(this.randomize())) begin
      `uvm_fatal(get_name(), "Randomization failed for aic_ls_dmc_cmdb_vtrsp_test!")
    end
    if (m_alternating_vtrsp==1) begin
      if (m_seq_counter%2==1) m_vtrsp_mode = 0; // disable vtrsp on odd index
    end
    m_mem_base_addr = m_env.m_env_cfg.m_l1_full_start_addr;

    m_seq_index = $urandom_range(0,2); //  m_odr = 0, d_odr = 1, m_ifdw = 2
    // m_seq_index = 0; //  for testing
    case (m_seq_index)
      0 : m_current_device = MVM_ODR;
      1 : m_current_device = DWPU_ODR;
      2 : m_current_device = MVM_IFDW;
    endcase
    `uvm_info (get_name(), $sformatf("creating sequence for %s new base address will be 0x%0x, offset is 0x%0x", m_current_device, (m_mem_base_addr + m_mem_offset), m_mem_offset), UVM_LOW)

    `uvm_info (get_name(), $sformatf("test_iter is %0d", test_iter), UVM_LOW)
    if (m_seq_index != 2) begin
      m_odr_seq[m_seq_index] = aic_ls_odr_seq_t::type_id::create($sformatf("m_odr_seq_%0d",m_seq_index));
      m_odr_seq[m_seq_index].m_prev_tlast_count = m_ifd_tlast_count[m_seq_index]; // set prev tlast count before randomize to add in post randomize of the seq
      m_odr_seq[m_seq_index].m_enable_cmdb = 0;
      m_odr_seq[m_seq_index].m_debug_data_en = 0;
      m_odr_seq[m_seq_index].m_use_icdf_post_memory = m_vtrsp_supported;
      m_odr_seq[m_seq_index].iteration = test_iter;
      m_odr_seq[m_seq_index].m_irq_status_field = m_irq_status; // this is the error we're looking for in VTRSP case.
      if (!(m_odr_seq[m_seq_index].randomize() with {
        m_device == AIC_LS_DMC_ODR_DEVICE[m_seq_index];
        if (m_cmd_format_q.size()== 0) m_ag_cmd_format != CMDFORMAT_LINEAR;
        else m_ag_cmd_format inside {m_cmd_format_q};
        m_ag_vtrsp_mode == m_vtrsp_mode;
        m_ag_mem_baseaddr == m_mem_base_addr + m_mem_offset;
        m_wait_data_done_en == m_wait_data_done;
        m_wait_for_status == m_wait_status;
        m_cid == m_env.m_env_cfg.m_cid;
        m_ag_dim_def_ptr  == m_ptr_index * 4; // avoid overlapping pointers
        m_ag_loop_def_ptr == (m_ptr_index * 4) + 64; // avoid overlapping pointers
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
      if (m_odr_seq[m_seq_index].m_ag_cmd_format inside {CMDFORMAT_DEF_BASED, CMDFORMAT_OFFSET_BASED}) begin
        m_ptr_index += 1;
        if (m_ptr_index==15) begin
          m_ptr_index = 0;
          `uvm_info (get_name(), "resetting m_ptr_index to 0", UVM_LOW)
        end
      end
    end else begin  // other case is IFDW!
      m_ifd_seq[MVM_IFDW] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",MVM_IFDW));
      m_ifd_seq[MVM_IFDW].m_prev_tlast_count = m_ifd_tlast_count[MVM_IFDW]; // set prev tlast count before randomize to add in post randomize of the seq
      m_ifd_seq[MVM_IFDW].m_enable_cmdb = 0;
      m_ifd_seq[MVM_IFDW].iteration = test_iter;
      m_ifd_seq[MVM_IFDW].m_irq_status_field = m_irq_status; // this is the error we're looking for in VTRSP case.
      if (!(m_ifd_seq[MVM_IFDW].randomize() with {
        m_device == AIC_LS_DMC_IFD_DEVICE[MVM_IFDW];
        if (m_cmd_format_q.size()== 0) m_ag_cmd_format != CMDFORMAT_LINEAR;
        else m_ag_cmd_format inside {m_cmd_format_q};
        m_ag_vtrsp_mode == m_vtrsp_mode;
        m_ag_mem_baseaddr == m_mem_base_addr + m_mem_offset;
        m_wait_data_done_en == m_wait_data_done;
        m_wait_for_status == m_wait_status;
        m_cid == m_env.m_env_cfg.m_cid;
        m_ag_dim_def_ptr  == m_ptr_index * 4; // avoid overlapping pointers
        m_ag_loop_def_ptr == (m_ptr_index * 4) + 64; // avoid overlapping pointers
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
      if (m_ifd_seq[MVM_IFDW].m_ag_cmd_format inside {CMDFORMAT_DEF_BASED, CMDFORMAT_OFFSET_BASED}) begin
        m_ptr_index += 1;
        if (m_ptr_index==15) begin
          m_ptr_index = 0;
          `uvm_info (get_name(), "resetting m_ptr_index to 0", UVM_LOW)
        end
      end
    end
    `uvm_info (get_name(), $sformatf("VTRSP_MODE[%0d]: %0d", m_seq_counter, m_vtrsp_mode), UVM_LOW)
    m_seq_counter += 1;
    m_mem_offset += m_mem_offset_increment;
  endfunction

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 8;
    foreach (m_device_index[i]) begin
      m_env.m_dmc_data_scb[m_device_index[i]].set_vtrsp_enable(m_vtrsp_supported);
    end
    m_env.m_aic_ls_agt.vif.drv.disable_rdataX_aserrtion <= m_vtrsp_supported; // https://git.axelera.ai/ai-hw-team/triton/-/issues/2705
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task test_seq();
    cfg_data_t irq_status, hw_capability;
    foreach (m_device_index[i]) begin
      m_env.m_ral.write_reg(.regblock_num(m_device_index[i]),  .data(1), .name("cmdblk_ctrl"));
      `uvm_info (get_name(), $sformatf("Enabled cmdblk in iteration for device %s done.", m_device_index[i].name()), UVM_LOW)
    end
    for (int iter=0; iter < m_test_iteration; iter++) begin
      `uvm_info (get_name(), $sformatf("preparing for sequence iteration %0d", iter), UVM_LOW)
      test_iter = iter;
      randomize_sequences();
      if (m_seq_index != 2) m_odr_seq[m_seq_index].start(null);
      else m_ifd_seq[MVM_IFDW].start(null);
      `uvm_info (get_name(), $sformatf("sequence done for test iteration %0d done.", iter), UVM_LOW)
      if (m_seq_index != 2) update_tlast(.tlast_index(m_seq_index), .is_ifd_not_odr(0));  // update tlast index, so that in the next run, we wait for the correct signal
      else update_tlast(.tlast_index(MVM_IFDW), .is_ifd_not_odr(1));
    end
    
    repeat (m_test_iteration) #1us;
    for (int iter=0; iter < m_test_iteration; iter++) begin

      // read status
      if (iter==m_test_iteration-1) begin
        read_register(m_current_device, "cmdblk_status", "state", 1, 0);
        m_env.m_ral.read_reg(.regblock_num(m_current_device),  .data(irq_status), .name("irq_status"));
        trigger_reg_evt(.device_index(m_current_device), .reg_name("irq_status")); // for func_cov
        m_env.m_ral.read_reg(.regblock_num(m_current_device),  .data(hw_capability), .name("hw_capability"));
        if (irq_status != 0 && m_vtrsp_supported) begin
          `uvm_error(get_name(), $sformatf("Unexpected IRQ assertion for %s! IRQ val: 0x%0x", m_current_device.name(), irq_status))          
        end else begin
          `uvm_info(get_name(), $sformatf("IRQ value correct for %s! IRQ val: 0x%0x", m_current_device.name(), irq_status), UVM_LOW)
        end
        if (hw_capability[34] != m_vtrsp_supported) begin
          `uvm_error(get_name(), $sformatf("VTRSP_PRESENT=%0d asserted for %s! hw_capability: 0x%0x", m_vtrsp_supported, m_current_device.name(), hw_capability))
        end else begin
          `uvm_info(get_name(), $sformatf("VTRSP_PRESENT=%0d for %s! hw_capability: 0x%0x", m_vtrsp_supported, m_current_device.name(), hw_capability), UVM_LOW)
        end

        foreach (m_device_index[i]) begin
          read_register(m_device_index[i], "cmdblk_status", "state", 1, 0);
        end
      end
      `uvm_info (get_name(), $sformatf("Test Iteration %0d done.", iter), UVM_NONE)
    end
  endtask
endclass:aic_ls_dmc_cmdb_vtrsp_test
`endif

