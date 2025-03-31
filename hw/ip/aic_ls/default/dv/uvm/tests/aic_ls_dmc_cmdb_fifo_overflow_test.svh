// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: This test triggers, interrupts, checks and clears cmdb fifo overflow error
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_FIFO_OVERFLOW_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_FIFO_OVERFLOW_TEST_SV

class aic_ls_dmc_cmdb_fifo_overflow_test extends aic_ls_dmc_cmdb_b2b_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_fifo_overflow_test)

  int m_fifo_count=aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH;

  function new (string name="aic_ls_dmc_cmdb_fifo_overflow_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_name(), "build_phase() started.",UVM_LOW)
  endfunction : build_phase

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 1;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task irq_seq(int ls_device);
    int irq_indx;
    cfg_data_t rdata, wdata;
    // IRQ checking
    m_env.m_ral.read_reg(.regblock_num(ls_device),  .data(rdata), .name("irq_status"), .field("cmdblk_cmd_dropped"));
    trigger_reg_evt(.device_index(ls_device), .reg_name("irq_status")); // for func_cov
    if (rdata != 1) begin
      `uvm_error(get_name(), $sformatf("cmdblk_cmd_dropped Status did not assert for LS device %0d", ls_device))
    end

    irq_indx = remap_index(ls_device);
    check_expected_irq(.exp_irq(1'b1), .indx(irq_indx));
    `uvm_info (get_name(), $sformatf("Targetting device %0d expected IRQ (of 1) check done.", ls_device), UVM_LOW)

    `uvm_info (get_name(), $sformatf("Targetting device %0d Disabling cmdblk_cmd_dropped Error! IRQ_EN: 0x%0x.",  ls_device, wdata), UVM_LOW)
    m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b0), .name("irq_en"), .field("cmdblk_cmd_dropped"));
    repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait for write txn to take effect
    check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));
    `uvm_info (get_name(), $sformatf("Targetting device %0d expected IRQ (of 0) check done.", ls_device), UVM_LOW)

    `uvm_info (get_name(), $sformatf("Targetting device %0d Clearing cmdblk_cmd_dropped Error status! IRQ_Status wdata: 0x%0x.",  ls_device, wdata), UVM_LOW)
    m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b1), .name("irq_status"), .field("cmdblk_cmd_dropped"));
    repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait for write txn to take effect
    m_env.m_ral.read_reg(.regblock_num(ls_device),  .data(rdata), .name("irq_status"), .field("cmdblk_cmd_dropped"));
    trigger_reg_evt(.device_index(ls_device), .reg_name("irq_status")); // for func_cov
    if (rdata != 0) begin
      `uvm_error(get_name(), $sformatf("cmdblk_cmd_dropped Error Status did not clear for LS device %0d", ls_device))
    end
    m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b1), .name("irq_en"), .field("cmdblk_cmd_dropped"));
    repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait for write txn to take effect
    check_expected_irq(.exp_irq(1'b0), .indx(irq_indx));
    `uvm_info (get_name(), $sformatf("Targetting device %0d expected IRQ (of 0) check done.", ls_device), UVM_LOW)

    m_env.m_ral.write_reg(.regblock_num(ls_device),  .data(1'b1), .name("irq_en"), .field("cmdblk_cmd_dropped")); // reenable at the end
  endtask

  // Linear, defbased and offset defbased consume 1 fifo count, 3dim fallback 2 fifo count, and 4dim fallback 3 fifo count
  // This function will target to fill the device fifo to almost full condition
  function void set_cmdformat(ref int fifo_val);
    int cmd_fifo_len;
    m_cmd_format_q.delete();
    if (fifo_val > 3) begin
      cmd_fifo_len = $urandom_range(1,3);
    end else if (fifo_val == 3) begin
      cmd_fifo_len = $urandom_range(1,2);
    end else begin
      cmd_fifo_len = 1;
    end
    case (cmd_fifo_len)
      1: begin
         m_cmd_format_q.push_back(CMDFORMAT_DEF_BASED);
         m_cmd_format_q.push_back(CMDFORMAT_LINEAR);
         m_cmd_format_q.push_back(CMDFORMAT_OFFSET_BASED);
      end
      2: m_cmd_format_q.push_back(CMDFORMAT_3DIM_FALLBACK);
      default: m_cmd_format_q.push_back(CMDFORMAT_4DIM_FALLBACK);
    endcase
    fifo_val -= cmd_fifo_len;
  endfunction


  virtual task test_seq();
    int fifo_count;

    for (int dev=0; dev < m_device_end; dev++) begin
      fifo_count = m_fifo_count;
      m_env.m_ral.write_reg(.regblock_num(dev),  .data(0), .name("cmdblk_ctrl")); // disable cmdblk to easily fill FIFO
      m_env.m_ral.write_reg(.regblock_num(dev),  .data(1'b1), .name("irq_en"), .field("cmdblk_cmd_dropped"));
      // For FIFO almost full
      while (fifo_count > 1) begin
        set_cmdformat(fifo_count);
        randomize_sequences(dev, 0);
        if (dev < AIC_LS_ENV_IFD_NUM_DEVICE) m_ifd_seq[dev].start(null);
        else begin
          m_odr_seq[dev - AIC_LS_ENV_IFD_NUM_DEVICE].m_start_stream = 0; // control in test
          m_odr_seq[dev - AIC_LS_ENV_IFD_NUM_DEVICE].start(null);
        end
        `uvm_info (get_name(), $sformatf("FIFO almost full done for %s with fifocount = %0d", AIC_LS_DMC_DEVICE_NAME[dev], fifo_count), UVM_LOW)
      end
      read_register(.device_index(dev), .name("cmdblk_status"), .field("fifo_cnt"), .poll(1), .poll_val(m_fifo_count-1)); // poll for pull
      trigger_reg_evt(.device_index(dev), .reg_name("cmdblk_status")); // for func_cov

      // For FIFO Full
      set_cmdformat(fifo_count);
      randomize_sequences(dev, 0);
      if (dev < AIC_LS_ENV_IFD_NUM_DEVICE) m_ifd_seq[dev].start(null);
      else begin
        m_odr_seq[dev - AIC_LS_ENV_IFD_NUM_DEVICE].m_start_stream = 0; // control in test
        m_odr_seq[dev - AIC_LS_ENV_IFD_NUM_DEVICE].start(null);
      end
      `uvm_info (get_name(), $sformatf("FIFO full done for %s with fifocount = %0d", AIC_LS_DMC_DEVICE_NAME[dev], fifo_count), UVM_LOW)
      read_register(.device_index(dev), .name("cmdblk_status"), .field("fifo_cnt"), .poll(1), .poll_val(m_fifo_count)); // poll for full
      trigger_reg_evt(.device_index(dev), .reg_name("cmdblk_status")); // for func_cov

      // For FIFO Overflow
      fifo_count = m_fifo_count; // renew count to device forces to be queue w/ new command
      set_cmdformat(fifo_count);
      randomize_sequences(dev, 0);
      if (dev < AIC_LS_ENV_IFD_NUM_DEVICE) m_ifd_seq[dev].start(null);
      else begin
        m_odr_seq[dev - AIC_LS_ENV_IFD_NUM_DEVICE].m_start_stream = 0; // control in test
        m_odr_seq[dev - AIC_LS_ENV_IFD_NUM_DEVICE].start(null);
      end
      `uvm_info (get_name(), $sformatf("FIFO overflow done for %s with fifocount = %0d", AIC_LS_DMC_DEVICE_NAME[dev], fifo_count), UVM_LOW)

      fork
        begin
          //Enable cmdblk
          m_env.m_ral.write_reg(.regblock_num(dev),  .data(1), .name("cmdblk_ctrl"));
          repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait for write txn to take effect
          read_register(.device_index(dev), .name("cmdblk_status"), .field("state"), .poll(1), .poll_val(0));
          trigger_reg_evt(.device_index(dev), .reg_name("cmdblk_status")); // for func_cov
        end
        forever begin
          if (dev < AIC_LS_ENV_IFD_NUM_DEVICE) @(posedge m_env.m_axi_system_env.vif.common_aclk);
          else begin
            `uvm_info (get_name(), $sformatf("gen_axi_stream started for %s", AIC_LS_DMC_DEVICE_NAME[dev]), UVM_LOW)
            gen_axi_stream(dev-AIC_LS_ENV_IFD_NUM_DEVICE);
            `uvm_info (get_name(), $sformatf("gen_axi_stream done for %s", AIC_LS_DMC_DEVICE_NAME[dev]), UVM_LOW)
          end
        end
      join_any
      disable fork;
      irq_seq(dev);
    end

    reset_ls(); // only way to recover from error as LS has no error handling
    repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk); // wait after reset before starting next iteration
    super.test_seq(); // recovery
  endtask


endclass:aic_ls_dmc_cmdb_fifo_overflow_test
`endif

