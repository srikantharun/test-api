// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: This test triggers, interrupts, checks and clears cmdb vtrsp_err error
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_VTRSP_IRQ_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_VTRSP_IRQ_TEST_SV

class dmc_addr_vtrsp_irq_item extends dmc_addr_gen_seq_item;
  `uvm_object_utils(dmc_addr_vtrsp_irq_item)

  static bit m_enable_vtrsp_irq;


  constraint C_VTRSP_WRT_LEN {
    //((m_format^header_vector_mode)+1) - when we're casting, vec_mode=1 and format=0, thus XOR yields 1, otherwise 0. casting makes VTRSP length twice as long, thus we need to take this into account
    (m_vtrsp_mode != 0 && m_num_dim==4 && m_enable_vtrsp_irq==0) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_inner_length_b * m_inner_length_c * m_inner_length_d * m_outer_length_a * m_outer_length_b * m_outer_length_c * m_outer_length_d) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
    (m_vtrsp_mode != 0 && m_num_dim==3 && m_enable_vtrsp_irq==0) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_inner_length_b * m_inner_length_c * m_outer_length_a * m_outer_length_b * m_outer_length_c) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
    (m_vtrsp_mode != 0 && m_num_dim==2 && m_enable_vtrsp_irq==0) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_inner_length_b * m_outer_length_a * m_outer_length_b) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
    (m_vtrsp_mode != 0 && m_num_dim==1 && m_enable_vtrsp_irq==0) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_outer_length_a) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;

    (m_vtrsp_mode != 0 && m_num_dim==4 && m_enable_vtrsp_irq==1) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_inner_length_b * m_inner_length_c * m_inner_length_d * m_outer_length_a * m_outer_length_b * m_outer_length_c * m_outer_length_d) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) != 0;
    (m_vtrsp_mode != 0 && m_num_dim==3 && m_enable_vtrsp_irq==1) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_inner_length_b * m_inner_length_c * m_outer_length_a * m_outer_length_b * m_outer_length_c) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) != 0;
    (m_vtrsp_mode != 0 && m_num_dim==2 && m_enable_vtrsp_irq==1) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_inner_length_b * m_outer_length_a * m_outer_length_b) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) != 0;
    (m_vtrsp_mode != 0 && m_num_dim==1 && m_enable_vtrsp_irq==1) -> soft ((m_format^header_vector_mode)+1)*(m_inner_length_a * m_outer_length_a) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) != 0;
  }

  function new (string name = "dmc_addr_vtrsp_irq_item");
    super.new (name);
  endfunction
endclass

class aic_ls_dmc_cmdb_vtrsp_irq_test extends aic_ls_dmc_cmdb_vtrsp_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_vtrsp_irq_test);

  int unsigned vtrsp_err_bit = 25; // this is the bit in irq_err that represents vtrsp error
  int unsigned m_irq_iteration = 10;

  function new (string name="aic_ls_dmc_cmdb_vtrsp_irq_test", uvm_component parent);
    super.new (name, parent);
    set_type_override_by_type(dmc_addr_gen_seq_item::get_type(), dmc_addr_vtrsp_irq_item::get_type());
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    m_test_iteration = 0;
    m_alternating_vtrsp = 0;
    m_wait_status = 1;
    m_irq_status = "err_vtrsp";
    //m_cmd_format_q.push_back(CMDFORMAT_3DIM_FALLBACK);
  endtask

  virtual task set_vtrsp_irq_en(bit en);
    string field_name;
    m_env.m_ral.write_reg(.regblock_num(m_current_device),  .data(0), .name("irq_en")); // disable first
    if (en) begin
      repeat(20) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait for previous write to take effect
      m_env.m_ral.write_reg(.regblock_num(m_current_device),  .data(1'b1), .name("irq_en"), .field("err_vtrsp"));
    end
  endtask

  virtual task clear_vtrsp_irq_status();
    cfg_data_t irq_status;
    string field_name;
    m_env.m_ral.read_reg(.regblock_num(m_current_device),  .data(irq_status), .name("irq_status"));
    m_env.m_ral.write_reg(.regblock_num(m_current_device),  .data(irq_status), .name("irq_status"));
  endtask

  virtual task check_irq_status(bit has_err=1);
    cfg_data_t irq_status, exp_status;
    exp_status[vtrsp_err_bit] = 1 & has_err;
    m_env.m_ral.read_reg(.regblock_num(m_current_device),  .data(irq_status), .name("irq_status"));
    trigger_reg_evt(.device_index(m_current_device), .reg_name("irq_status")); // for func_cov
    if (irq_status[vtrsp_err_bit] != exp_status[vtrsp_err_bit]) begin
      `uvm_error(get_name(),  $sformatf("IRQ status Error! Exp: 0x%0x Act: 0x%0x", exp_status, irq_status))
    end else begin
      `uvm_info(get_name(),  $sformatf("IRQ status 0x%0x", irq_status), UVM_LOW)
    end
  endtask

  virtual task test_seq();
    cfg_data_t irq_status, hw_capability;
    int irq_indx;

    for (int iter=0; iter < m_irq_iteration; iter++) begin
      foreach (m_device_index[i]) begin  // enabling each VTRSP device!
        m_env.m_ral.write_reg(.regblock_num(m_device_index[i]),  .data(1), .name("cmdblk_ctrl"));
        `uvm_info (get_name(), $sformatf("Enabled cmdblk in iteration for device %s done.", m_device_index[i].name()), UVM_LOW)
      end
      dmc_addr_vtrsp_irq_item::m_enable_vtrsp_irq=1;
      m_wait_data_done = 0;  // make sure we're not actually waiting to check all data done, as it will raise an error
      randomize_sequences();  // randomization will create m_current_device for this iteration
      if (m_current_device == MVM_IFDW) m_env.m_dmc_data_scb[m_current_device].m_ifdw_vtrsp_err_en = 1;  // ifdw irq is enabled in a different way
      else m_env.m_dmc_ref_mdl[m_current_device].m_vtrsp_err_en = 1;
      set_vtrsp_irq_en(1);
      if (m_current_device == MVM_IFDW) m_ifd_seq[m_current_device].start(null);
      else m_odr_seq[m_seq_index].start(null);
      `uvm_info (get_name(), $sformatf("m_odr_seq done for test iteration %0d done.", iter), UVM_NONE)
      repeat(1000) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait for sequence to finish, MMIO txns take some time

      // Expect the error status to be asserted
      `uvm_info (get_name(), $sformatf("[%0d] Expecting IRQ for %s VTRSP_ERR", iter, m_current_device.name()), UVM_NONE)
      check_irq_status(1);
      irq_indx = remap_index(m_current_device);
      check_expected_irq(.exp_irq(1), .indx(irq_indx));

      `uvm_info (get_name(), $sformatf("[%0d] Targetting %s. Disabling IRQ_EN for VTRSP Error!", iter, m_current_device.name()), UVM_NONE)
      set_vtrsp_irq_en(0);
      repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // after disabling interrupt, wait for some time before checking IRQ signal
      check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

      `uvm_info (get_name(), $sformatf("[%0d] Targetting %s clearing VTRSP_ERR status!", iter, m_current_device.name()), UVM_NONE)
      clear_vtrsp_irq_status();
      repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // after clearing interrupt, wait for some time before checking IRQ signal
      check_irq_status(0);

      set_vtrsp_irq_en(1);
      repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // after disabling interrupt, wait for some time before checking IRQ signal
      check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

      reset_ls(); // reset LS, only way to recover according to designers
      m_env.reset_addr_gen_refmodel();
      dmc_addr_vtrsp_irq_item::m_enable_vtrsp_irq=0;
      if (m_current_device == MVM_IFDW) m_env.m_dmc_data_scb[m_current_device].m_ifdw_vtrsp_err_en = 0;  // ifdw irq is enabled in a different way
      else m_env.m_dmc_ref_mdl[m_current_device].m_vtrsp_err_en = 0;

      `uvm_info (get_name(), $sformatf("[%0d] Starting recovery txn for %s.", iter, m_current_device.name()), UVM_NONE)
      m_env.m_ral.write_reg(.regblock_num(m_current_device),  .data(0), .name("cmdblk_ctrl"));
      m_wait_data_done = 1;  // before running a valid sequence, enable the check.
      `uvm_info (get_name(), $sformatf("Enabled cmdblk in iteration %0d done.", iter), UVM_NONE)
      super.test_seq();
      `uvm_info (get_name(), $sformatf("IRQ Iteration %0d done.", iter), UVM_NONE)
    end
  endtask

endclass:aic_ls_dmc_cmdb_vtrsp_irq_test
`endif

