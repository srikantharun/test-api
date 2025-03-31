// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Decompression Test
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_DECOMPRESSION_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_DECOMPRESSION_TEST_SV

class aic_ls_dmc_cmdb_decompression_test extends aic_ls_base_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_decompression_test)

  ifdw_decompression_seq_item m_stream_item_q[$];
  bit m_start_nondecomp_device = 1;
  int unsigned m_min_stream_length = 100;
  int unsigned m_max_stream_length = 4096;
  bit m_stream_header_error = 0;
  bit m_uncomp_len_error = 0;
  bit m_comp_len_error = 0;
  bit m_wait_data_done = 1;
  string m_irq_status_field="";

  function new (string name="aic_ls_dmc_cmdb_decompression_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void create_ifdw_stream();
    ifdw_decompression_seq_item decomp_item;
    int stream_length;
    int rand_counter;
    for (int i=0; i < AIC_LS_ENV_IFD_NUM_DEVICE; i++) begin
      decomp_item = ifdw_decompression_seq_item::type_id::create($sformatf("decomp_item_%0d", i));
      m_stream_item_q.push_back(decomp_item);
    end
    foreach (m_stream_item_q[i]) begin
      stream_length = $urandom_range(m_min_stream_length,m_max_stream_length);
      if (i==MVM_IFDW) begin
        do begin
          if (!(m_stream_item_q[i].randomize() with {
            m_stream_length == stream_length;
            m_stream_header_err == m_stream_header_error;
            m_uncomp_len_err == m_uncomp_len_error;
            m_comp_len_err == m_comp_len_error;
          })) begin
            `uvm_fatal(get_name(), $sformatf("Randomization failed for m_stream_item_q_%0d!", i))
          end
          rand_counter += 1;
          if (rand_counter > 100) begin
            `uvm_fatal(get_name(), $sformatf("Randomization failed for m_stream_item_q_%0d!", i))
          end
          `uvm_info(get_name(), $sformatf("IFDW Stream: try #%0d", rand_counter), UVM_LOW)
        end while (!m_stream_item_q[i].check_scheme_length(FVC, MIN_FVC_COMPRESSED_NUM));  // Here just in case. shouldn't ever fail.
        `uvm_info(get_name(), $sformatf("IFDW Stream: %s", m_stream_item_q[i].convert2string()), UVM_NONE)
        sample_compression_cov(m_stream_item_q[i]); // for func cov
      end
    end
  endfunction

  virtual function void sample_compression_cov(ifdw_decompression_seq_item d_item);
    compression_scheme_t comp;
    compression_error_t comp_err;
    bit has_err, is_subheader;
    int compressed_len, uncompressed_len;

    has_err = d_item.m_stream_header_err || d_item.m_uncomp_len_err || d_item.m_comp_len_err;
    if (has_err) begin
      if (d_item.m_uncomp_len_err) begin
        comp_err = INVALID_UNCOMP_SIZE;
      end else if (d_item.m_comp_len_err) begin
        comp_err = INVALID_COMP_SIZE;
      end else if (d_item.m_stream_header_err) begin
        comp_err = INVALID_STREAM_HEADER;
      end
    end
    foreach (d_item.headers_q[i]) begin  // associative array, i here is the index in the compressed array of the header
      
      if (i==0) begin  // first one is the global header
        decomp_stream_header_t header = decomp_stream_header_t'(d_item.headers_q[i]);

        is_subheader = 0;
        uncompressed_len = header.stream_length;
      end else begin
        decomp_substream_header_t header = decomp_substream_header_t'(d_item.headers_q[i]);

        is_subheader = 1;
        has_err = d_item.m_stream_header_err || d_item.m_uncomp_len_err || d_item.m_comp_len_err;
        comp = header.compression_scheme;
        compressed_len   = header.compressed_stream_length;
        uncompressed_len = header.uncompressed_stream_length;
      end
      m_env.m_cov.ifdw_compression_cg.sample(is_subheader, comp, comp_err, has_err, compressed_len, uncompressed_len);
      `uvm_info(get_name(), $sformatf("Sample coverage! comp: %s | comp_err: %s | has_error: %0d | compressed_len: %0d | uncompressed_len: %0d", comp, comp_err, has_err, compressed_len, uncompressed_len), UVM_LOW)
    end
  endfunction

  virtual function void randomize_sequences();
    int linear_read_len;
    for (int i=0; i < AIC_LS_ENV_IFD_NUM_DEVICE; i++) begin
      if (m_stream_item_q[i] == null) begin
        `uvm_fatal(get_name(), $sformatf("m_stream_item_q_%0d is null!", i))
      end else begin
        if (i==MVM_IFDW) linear_read_len = m_stream_item_q[i].m_compressed_pword_q.size();
        else linear_read_len = $urandom_range(1,4096);
      end
      m_ifd_seq[i] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",i));
      m_ifd_seq[i].m_prev_tlast_count = m_ifd_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      m_ifd_seq[i].m_enable_wr_to_l1 = 0;
      m_ifd_seq[i].m_irq_status_field = m_irq_status_field;
      m_ifd_seq[i].m_decomp_item_h = m_stream_item_q[i];
      if (i != MVM_IFDW) m_ifd_seq[i].m_irq_status_field = "dp_decomp_access_error";
      if (!(m_ifd_seq[i].randomize() with {
        m_device == AIC_LS_DMC_IFD_DEVICE[i];
        m_ag_cmd_format == CMDFORMAT_LINEAR;
        m_ag_decompression_en == 1;
        m_ag_length == linear_read_len;
        m_cid == m_env.m_env_cfg.m_cid;
        if (i != MVM_IFDW) m_wait_data_done_en == 0;
        if (i == MVM_IFDW) m_wait_data_done_en == m_wait_data_done;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
    end
  endfunction

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 3;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task test_seq();
    cfg_data_t irq_status, hw_capability;
    for (int iter=0; iter < m_test_iteration; iter++) begin
      create_ifdw_stream();
      randomize_sequences();
      m_env.m_dmc_data_scb[MVM_IFDW].set_uncompressed_stream(m_stream_item_q[MVM_IFDW].m_full_pword_q);
      fork
        if (m_start_nondecomp_device) m_ifd_seq[MVM_IFD0].start(null);
        if (m_start_nondecomp_device) m_ifd_seq[MVM_IFD1].start(null);
        if (m_start_nondecomp_device) m_ifd_seq[MVM_IFD2].start(null);
        m_ifd_seq[MVM_IFDW].start(null);
        if (m_start_nondecomp_device) m_ifd_seq[DWPU_IFD0].start(null);
        if (m_start_nondecomp_device) m_ifd_seq[DWPU_IFD1].start(null);
      join
      #1us;
      m_ifd_tlast_count[MVM_IFDW] = m_ifd_seq[MVM_IFDW].m_tlast_count;
      `uvm_info (get_name(), $sformatf("Test Iteration %0d done.", iter), UVM_NONE)
      m_env.reset_addr_gen_refmodel();

      // read status
      for (int i=0; i < AIC_LS_ENV_IFD_NUM_DEVICE; i++) begin
        if (i== MVM_IFDW || m_start_nondecomp_device) begin
          m_env.m_ral.read_reg(.regblock_num(i),  .data(irq_status), .name("irq_status"));
          trigger_reg_evt(.device_index(i), .reg_name("irq_status")); // for func_cov
          m_env.m_ral.read_reg(.regblock_num(i),  .data(hw_capability), .name("hw_capability"));
        end
        if (i== MVM_IFDW) begin
          if (irq_status != 0) begin
            `uvm_error(get_name(), $sformatf("Unexpected IRQ assterion! IRQ val: 0x%0x", irq_status))
          end else begin
            `uvm_info(get_name(), $sformatf("IRQ value correct for MVM_IFDW! IRQ val: 0x%0x", irq_status), UVM_LOW)
          end
          if (hw_capability[33] != 1) begin
            `uvm_error(get_name(), $sformatf("DECOMP_PRESENT not asserted for IFDW! hw_capability: 0x%0x", hw_capability))
          end else begin
            `uvm_info(get_name(), $sformatf("DECOMP_PRESENT asserted for IFDW! hw_capability: 0x%0x", hw_capability), UVM_LOW)
          end
        end else begin
          if (m_start_nondecomp_device) begin
            if (irq_status[16] != 1'b1) begin
              `uvm_error(get_name(), $sformatf("DP_DECOMP_ACCESS_ERROR not asserted for %s! IRQ val: 0x%0x", AIC_LS_DMC_DEVICE_NAME[i], irq_status))
            end else begin
              `uvm_info(get_name(), $sformatf("DP_DECOMP_ACCESS_ERROR asserted for %s! IRQ val: 0x%0x", AIC_LS_DMC_DEVICE_NAME[i], irq_status), UVM_LOW)
            end
            if (hw_capability[33] != 0) begin
              `uvm_error(get_name(), $sformatf("DECOMP_PRESENT asserted for %s! hw_capability: 0x%0x", AIC_LS_DMC_DEVICE_NAME[i], hw_capability))
            end else begin
              `uvm_info(get_name(), $sformatf("DECOMP_PRESENT negated for %s! hw_capability: 0x%0x", AIC_LS_DMC_DEVICE_NAME[i], hw_capability), UVM_LOW)
            end
          end
        end
      end
    end
    if (m_start_nondecomp_device) begin
      reset_ls(); // simply get rid of garbage items in scorebaords caused by decomp error
    end
  endtask

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    `uvm_info (get_name(), "main_phase() started.", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);
    phase.raise_objection(this);

    test_seq();
    #10us;

    phase.drop_objection(this);
    `uvm_info (get_name(), "main_phase() ended.", UVM_LOW)
  endtask : main_phase
endclass:aic_ls_dmc_cmdb_decompression_test
`endif

