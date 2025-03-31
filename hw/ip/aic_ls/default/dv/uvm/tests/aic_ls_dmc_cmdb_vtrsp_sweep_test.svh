// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR VTRSP test sweeping
//    VTRSP Mode with VTRSP length
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_VTRSP_SWEEP_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_VTRSP_SWEEP_TEST_SV

class dmc_addr_gen_vtrsp_sweep_seq_item extends dmc_addr_gen_seq_item;
  `uvm_object_utils(dmc_addr_gen_vtrsp_sweep_seq_item)

  static int m_vtrsp_len;

  constraint C_VTRSP_SWEEP {
    (m_num_dim==4) -> (m_inner_length_a * m_inner_length_b * m_inner_length_c * m_inner_length_d * m_outer_length_a * m_outer_length_b * m_outer_length_c * m_outer_length_d) == m_vtrsp_len;
    (m_num_dim==3) -> (m_inner_length_a * m_inner_length_b * m_inner_length_c * m_outer_length_a * m_outer_length_b * m_outer_length_c) == m_vtrsp_len;
    (m_num_dim==2) -> (m_inner_length_a * m_inner_length_b * m_outer_length_a * m_outer_length_b) == m_vtrsp_len;
    (m_num_dim==1) -> (m_inner_length_a * m_outer_length_a) == m_vtrsp_len;
  }

  function new (string name = "dmc_addr_gen_vtrsp_sweep_seq_item");
    super.new (name);
  endfunction

  virtual function void set_high_mbsize();
    if (m_high_mbsize) begin
      for (int i=30; i >= 20; i--) begin
        m_mem_bsize[i] = 1; // from parent class, now always set to 1 value instead of random, do not violate icdf constraint
      end
    end
  endfunction

  function void post_randomize();
    m_dim_offset_a = 0; // zero out offset to ensure padding does not happen
    m_dim_offset_b = 0; // zero out offset to ensure padding does not happen
    m_dim_offset_c = 0; // zero out offset to ensure padding does not happen
    m_dim_offset_d = 0; // zero out offset to ensure padding does not happen
    m_outer_stride_a = 1; // use simplest setting
    m_outer_stride_b = 1; // use simplest setting
    m_outer_stride_c = 1; // use simplest setting
    m_outer_stride_d = 1; // use simplest setting
    m_inner_stride_a = 1; // use simplest setting
    m_inner_stride_b = 1; // use simplest setting
    m_inner_stride_c = 1; // use simplest setting
    m_inner_stride_d = 1; // use simplest setting
    m_dim_width_a = (m_inner_length_a > m_outer_length_a) ? m_inner_length_a : m_outer_length_a; // avoid padding. make sure dim width is large enough
    m_dim_width_b = (m_inner_length_b > m_outer_length_b) ? m_inner_length_b : m_outer_length_b; // avoid padding. make sure dim width is large enough
    m_dim_width_c = (m_inner_length_c > m_outer_length_c) ? m_inner_length_c : m_outer_length_c; // avoid padding. make sure dim width is large enough
    m_dim_width_d = (m_inner_length_d > m_outer_length_d) ? m_inner_length_d : m_outer_length_d; // avoid padding. make sure dim width is large enough
    m_high_mbsize =  1;
    set_high_mbsize();
    set_fields_to_cmd();
    cmd_struct_to_array();
    m_cmd_q[0][55:48] = m_cmd_format;
  endfunction
endclass

class aic_ls_dmc_cmdb_vtrsp_sweep_test extends aic_ls_dmc_cmdb_vtrsp_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_vtrsp_sweep_test);

  int m_sweep_vtrsp_mode;
  int m_vtrsp_len_q[$];

  function new (string name="aic_ls_dmc_cmdb_vtrsp_sweep_test", uvm_component parent);
    super.new (name, parent);
    m_wait_status = 1; // avoid b2b VTRSP since we are using static variables
    m_irq_status = "";
    set_type_override_by_type(dmc_addr_gen_seq_item::get_type(), dmc_addr_gen_vtrsp_sweep_seq_item::get_type());
  endfunction : new

  virtual function void randomize_sequences();
    super.randomize_sequences();
    if (m_seq_index != 2) m_odr_seq[m_seq_index].m_ag_vtrsp_mode = m_sweep_vtrsp_mode;
    else m_ifd_seq[MVM_IFDW].m_ag_vtrsp_mode = m_sweep_vtrsp_mode;
  endfunction

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 2;
    m_vtrsp_len_q.push_back(64);  // func cov target multiple of PWORD
    m_vtrsp_len_q.push_back(128); // func cov target multiple of PWORD
    m_vtrsp_len_q.push_back(192); // func cov target multiple of PWORD
    m_vtrsp_len_q.push_back(256); // func cov target multiple of PWORD
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task test_seq();
    for (int v=1; v < 4; v++) begin // VTRSP MODE: 1 INT8, 2: FP16 3: FP32
      m_sweep_vtrsp_mode = v;
      //m_mem_offset = 0;
      foreach (m_vtrsp_len_q[i]) begin
        `uvm_info (get_name(), $sformatf("started vmode %0d, test_seq %0d",v, i), UVM_LOW)
        // m_mem_offset = 0;
        dmc_addr_gen_vtrsp_sweep_seq_item::m_vtrsp_len = m_vtrsp_len_q[i];
        m_mem_offset_increment = 256*512;  // 256 bit is the longest VTRSP sequence, and 512 is amount of bits per word. this is the simplest way to ensure entries don't overlap
        super.test_seq();
      end
    end
  endtask
endclass:aic_ls_dmc_cmdb_vtrsp_sweep_test
`endif
