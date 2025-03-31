// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: This test triggers, interrupts, checks and clears cmdb addr_out_of_range error
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_ADDR_OUT_OF_RANGE_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_ADDR_OUT_OF_RANGE_TEST_SV

class dmc_addr_out_of_range_item extends dmc_addr_gen_seq_item;
  `uvm_object_utils(dmc_addr_out_of_range_item)

  function new (string name = "dmc_addr_out_of_range_item");
    super.new (name);
  endfunction

  static bit m_addr_range_err_en = 1;

  function void post_randomize();
    int num_dim = get_valid_dims();
    int old_size = m_mem_bsize;
    if (m_addr_range_err_en) begin
      m_mem_bsize = 64; // generate address out of range
      set_fields_to_cmd();
      cmd_struct_to_array();
      m_cmd_q[0][55:48] = m_cmd_format;
      `uvm_info(get_name(), $sformatf("Setting m_mem_bsize from %0d to %0d", old_size, m_mem_bsize), UVM_LOW)
    end else begin
      super.post_randomize();
    end
  endfunction
endclass

class aic_ls_dmc_cmdb_addr_out_of_range_test extends aic_ls_dmc_cmdb_tc_test  /*aic_ls_dmc_cmdb_1dev_tc_test*/;
  `uvm_component_utils (aic_ls_dmc_cmdb_addr_out_of_range_test)

  addr_gen_cmdformat_t m_command_format;

  function new (string name="aic_ls_dmc_cmdb_addr_out_of_range_test", uvm_component parent);
    super.new (name, parent);
    m_command_format = CMDFORMAT_DEF_BASED;
    set_type_override_by_type(dmc_addr_gen_seq_item::get_type(), dmc_addr_out_of_range_item::get_type());
    m_test_iteration = 5;
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
        m_device          == AIC_LS_DMC_IFD_DEVICE[i];
        m_ag_cmd_format   == m_command_format;
        m_cid  == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
    end
    foreach (m_odr_seq[i]) begin
      m_odr_seq[i].m_prev_tlast_count = m_odr_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_odr_seq[i].randomize() with {
        m_device          == AIC_LS_DMC_ODR_DEVICE[i];
        m_ag_cmd_format   == m_command_format;
        m_cid  == m_env.m_env_cfg.m_cid;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_odr_seq!")
      end
    end
  endfunction

  virtual task start_dmc_txn(int dev);
    case (dev)
      6: m_odr_seq[0].start(null); // mvm odr
      7: m_odr_seq[1].start(null); // dwpu_odr
      default: m_ifd_seq[dev].start(null);
    endcase
  endtask

  virtual task test_seq();
    int ls_device, irq_indx;
    bit exp_irq;
    cfg_data_t rdata, wdata;
    `uvm_info (get_name(), "test_seq started", UVM_LOW)

    for (int iter = 0; iter < m_test_iteration; iter++) begin
      for (int ls_device = 0; ls_device < AIC_LS_ENV_DMC_NUM_DEVICE; ls_device++) begin
        dmc_addr_out_of_range_item::m_addr_range_err_en = 1;
        `uvm_info (get_name(), $sformatf("Targetting device %0d started.", ls_device), UVM_LOW)
        randomize_sequences();

        `uvm_info (get_name(), $sformatf("Targetting device %0d Enabling Addr Out of Range! IRQ_EN",  ls_device), UVM_LOW)
        m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b1), .name("irq_en"), .field("err_addr_out_of_range"));
        m_env.m_dmc_ref_mdl[ls_device].m_addr_out_of_range_en = 1;
        start_dmc_txn(ls_device);

        // Expect the error status to be asserted
        exp_irq = (m_env.m_dmc_ref_mdl[ls_device].m_last_addr_out_of_range);
        `uvm_info (get_name(), $sformatf("Expecting IRQ for %s? %s",  AIC_LS_DMC_DEVICE_NAME[ls_device], (exp_irq)? "YES": "NO"), UVM_LOW)

        m_env.m_ral.read_reg(.regblock_num(ls_device),  .data(rdata), .name("irq_status"), .field("err_addr_out_of_range"));
        trigger_reg_evt(.device_index(ls_device), .reg_name("irq_status")); // for func_cov
        if (rdata != exp_irq) begin
          `uvm_error(get_name(), $sformatf("Addr Out of Range Status error for LS device %s. Exp: %0d Act: %0d", AIC_LS_DMC_DEVICE_NAME[ls_device], exp_irq, rdata))
        end
        irq_indx = remap_index(ls_device);
        check_expected_irq(.exp_irq(exp_irq), .indx(irq_indx));

        `uvm_info (get_name(), $sformatf("Targetting device %s Disabling Addr Out of Range! IRQ_EN: 0x%0x.",  AIC_LS_DMC_DEVICE_NAME[ls_device], wdata), UVM_LOW)
        m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b0), .name("irq_en"), .field("err_addr_out_of_range"));
        #50ns;
        check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

        `uvm_info (get_name(), $sformatf("Targetting device %s Clearing Addr Out of Range status! IRQ_Status wdata: 0x%0x.",  AIC_LS_DMC_DEVICE_NAME[ls_device], wdata), UVM_LOW)
        m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b1), .name("irq_status"), .field("err_addr_out_of_range"));
        #100ns;
        m_env.m_ral.read_reg(.regblock_num(ls_device),  .data(rdata), .name("irq_status"));
        trigger_reg_evt(.device_index(ls_device), .reg_name("irq_status")); // for func_cov
        if (rdata != 0) begin
          `uvm_error(get_name(), $sformatf("Addr Out of Range Status did not clear for LS device %s, IRQ val: 0x%0x", AIC_LS_DMC_DEVICE_NAME[ls_device], rdata))
        end
        m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b1), .name("irq_en"), .field("err_addr_out_of_range"));
        #10ns;
        check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

        dmc_addr_out_of_range_item::m_addr_range_err_en = 0;
        m_env.m_dmc_ref_mdl[ls_device].m_addr_out_of_range_en = 0;
        reset_ls(); // reset LS, only way to recover according to designers
        case (ls_device)
          5: m_odr_tlast_count[0] = 0;
          6: m_odr_tlast_count[1] = 0;
          default: m_ifd_tlast_count[ls_device] = 0;
        endcase
        randomize_sequences();
        `uvm_info (get_name(), $sformatf("Starting recovery txn for device %s.", AIC_LS_DMC_DEVICE_NAME[ls_device]), UVM_LOW)

        start_dmc_txn(ls_device);
        check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));

        `uvm_info (get_name(), $sformatf("[Iter: %0d] Targetting device %s ended.", iter, AIC_LS_DMC_DEVICE_NAME[ls_device]), UVM_LOW)
        m_env.reset_addr_gen_refmodel();
      end
    end
  endtask
endclass:aic_ls_dmc_cmdb_addr_out_of_range_test
`endif

