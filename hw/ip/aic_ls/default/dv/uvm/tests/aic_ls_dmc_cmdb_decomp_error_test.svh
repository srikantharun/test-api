// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFDW Decompression Error Test
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_DECOMP_ERROR_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_DECOMP_ERROR_TEST_SV

class aic_ls_dmc_cmdb_decomp_error_test extends aic_ls_dmc_cmdb_decompression_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_decomp_error_test)

  function new (string name="aic_ls_dmc_cmdb_decomp_error_test", uvm_component parent);
    super.new (name, parent);
     m_start_nondecomp_device = 0;
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 1;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual function void set_irq_status_field(compression_error_t err, bit has_err);
     case (err)
      INVALID_STREAM_HEADER: m_irq_status_field = "decomp_invalid_stream_header";
      INVALID_COMP_SIZE    : m_irq_status_field = "decomp_invalid_compressed_size";
      INVALID_UNCOMP_SIZE  : m_irq_status_field = "decomp_invalid_uncompressed_size";
    endcase
    if (has_err==0) m_irq_status_field = "";
  endfunction

  virtual task set_decomp_irq_en(compression_error_t err, bit en);
    string field_name;
    case (err)
      INVALID_STREAM_HEADER: field_name = "decomp_invalid_stream_header";
      INVALID_COMP_SIZE    : field_name = "decomp_invalid_compressed_size";
      INVALID_UNCOMP_SIZE  : field_name = "decomp_invalid_uncompressed_size";
    endcase
    m_env.m_ral.write_reg(.regblock_num(MVM_IFDW),  .data(0), .name("irq_en")); // disable first
    if (en) begin
      #20ns;
      m_env.m_ral.write_reg(.regblock_num(MVM_IFDW),  .data(1'b1), .name("irq_en"), .field(field_name));
    end
  endtask

  virtual task clear_decomp_irq_status();
    cfg_data_t irq_status;
    string field_name;
    #1us; // wait longer to not miss delayed errors
    m_env.m_ral.read_reg(.regblock_num(MVM_IFDW),  .data(irq_status), .name("irq_status"));
    m_env.m_ral.write_reg(.regblock_num(MVM_IFDW),  .data(irq_status), .name("irq_status"));
  endtask

  virtual task check_irq_status(compression_error_t err, bit has_err=1);
    cfg_data_t irq_status, exp_status;
    int index;
    case (err)
      INVALID_STREAM_HEADER: index = 17;
      // INVALID_SCHEME_HEADER: index = 18;
      INVALID_COMP_SIZE    : index = 19;
      INVALID_UNCOMP_SIZE  : index = 20;
    endcase
    exp_status[index] = 1 & has_err;
    m_env.m_ral.read_reg(.regblock_num(MVM_IFDW),  .data(irq_status), .name("irq_status"));
    trigger_reg_evt(.device_index(MVM_IFDW), .reg_name("irq_status")); // for func_cov
    if (irq_status[index] != exp_status[index]) begin
      `uvm_error(get_name(),  $sformatf("IRQ status Error! Exp: 0x%0x Act: 0x%0x", exp_status, irq_status))
    end else begin
      `uvm_info(get_name(),  $sformatf("IRQ status 0x%0x", irq_status), UVM_LOW)
    end
  endtask

  virtual task test_seq();
    int irq_indx;
    bit exp_irq;
    compression_error_t compression_error;
    `uvm_info (get_name(), "test_seq started", UVM_LOW)

    for (int iter = 0; iter < m_test_iteration; iter++) begin
      for (int err_type=0; err_type < compression_error.num(); err_type++) begin  // we now have 3 types of error. scheme_header cant be wrong
        m_stream_header_error = 0;
        m_uncomp_len_error = 0;
        m_comp_len_error = 0;
        compression_error = compression_error_t'(err_type);
        case (compression_error)
          INVALID_STREAM_HEADER: m_stream_header_error = 1;
          INVALID_COMP_SIZE    : m_comp_len_error      = 1;
          INVALID_UNCOMP_SIZE  : m_uncomp_len_error    = 1;
        endcase
        m_wait_data_done = 0; 
        set_irq_status_field(compression_error, 1);
        create_ifdw_stream();
        randomize_sequences();
        m_env.m_dmc_data_scb[MVM_IFDW].set_uncompressed_stream(m_stream_item_q[MVM_IFDW].m_full_pword_q);
        m_env.m_dmc_data_scb[MVM_IFDW].m_ifd_compression_err_en = 1;
        m_env.m_aic_ls_agt.vif.drv.disable_decomp_assertion <= 1;

        `uvm_info (get_name(), $sformatf("[%0d] Targetting IFDW! Enabling %s! IRQ_EN",  iter, compression_error.name()), UVM_LOW)
        set_decomp_irq_en(compression_error, 1);
        m_ifd_seq[MVM_IFDW].start(null);

        // Expect the error status to be asserted
        exp_irq = 1;
        `uvm_info (get_name(), $sformatf("[%0d] Expecting %s IRQ for MVM_IFDW %s", iter, compression_error.name(), (exp_irq)? "YES": "NO"), UVM_LOW)

        check_irq_status(compression_error);
        irq_indx = remap_index(MVM_IFDW);
        check_expected_irq(.exp_irq(exp_irq), .indx(irq_indx));

        `uvm_info (get_name(), $sformatf("[%0d] Targetting MVM_IFDW. Disabling IRQ_EN for %s Error!", iter, compression_error.name()), UVM_LOW)
        set_decomp_irq_en(compression_error, 0);
        #50ns;
        check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

        `uvm_info (get_name(), $sformatf("Targetting MVM_IFDW clearing %s status!",  compression_error.name()), UVM_LOW)
        clear_decomp_irq_status();
        #100ns;
        check_irq_status(compression_error, 0);

        set_decomp_irq_en(compression_error, 1);
        #100ns;
        check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

        reset_ls(); // reset LS, only way to recover according to designers
        m_ifd_tlast_count[MVM_IFDW] = 0;
        m_stream_header_error = 0;
        m_uncomp_len_error = 0;
        m_comp_len_error = 0;
        m_wait_data_done = 1;
        set_irq_status_field(compression_error, 0);
        m_env.m_aic_ls_agt.vif.drv.disable_decomp_assertion <= 0;

        #1us;
        create_ifdw_stream();
        randomize_sequences();
        m_env.m_dmc_data_scb[MVM_IFDW].set_uncompressed_stream(m_stream_item_q[MVM_IFDW].m_full_pword_q);
        `uvm_info (get_name(), $sformatf("[%0d] Starting recovery txn for MVM_IFDW %s.", iter, compression_error.name()), UVM_LOW)

        m_ifd_seq[MVM_IFDW].start(null);
        check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

        `uvm_info (get_name(), $sformatf("[Iter: %0d] Recovery for MVM_IFDW with %s ended.", iter,  compression_error.name()), UVM_LOW)
        m_env.reset_addr_gen_refmodel();
      end
    end
    reset_ls(); // clean up scoreboards in the end. garbage data can still exist after recovery
  endtask

endclass:aic_ls_dmc_cmdb_decomp_error_test
`endif

