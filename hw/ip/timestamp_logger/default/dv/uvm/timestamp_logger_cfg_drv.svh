// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_CFG_DRV_SVH
`define GUARD_TIMESTAMP_LOGGER_CFG_DRV_SVH

class timestamp_logger_cfg_drv extends uvm_driver#(timestamp_logger_cfg_item);

  timestamp_logger_env_cfg                              m_env_cfg;
  virtual axi_intf#(.DW(`DW),.AW(`AW),.IDW(`SIDW))      cfg_vif;
  axi_cmdblock_driver#(.DW(`DW), .AW(`AW), .IDW(`SIDW)) cfg_drv;
  uvm_analysis_port#(timestamp_logger_cfg_item)         ap;

  timestamp_logger_model                                m_model;
  axi_sl_driver#(.DW(`DW), .AW(`AW), .IDW(`MIDW))       m_extmem_drv;

  virtual timestamp_logger_event_if                     event_vif;
  axe_uvm_distribution                                  m_random_read_rate;
  bit [1:0]                                             random_read_enable = 2'b0;

  `uvm_component_utils(timestamp_logger_cfg_drv)

  function new (string name, uvm_component parent);
    super.new (name, parent);
    ap = new("ap", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    assert(uvm_config_db #(virtual timestamp_logger_event_if)::get(this, "", "event_vif",  event_vif));
    assert(uvm_config_db #(virtual axi_intf#(.DW(`DW),.AW(`AW),.IDW(`SIDW)))::get(this, "", "cfg_vif",  cfg_vif));
    assert(uvm_config_db#(timestamp_logger_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));

    cfg_drv = new("cfg_drv", cfg_vif);

    // CSRs
    cfg_drv.set_csr_base(m_env_cfg.csr_base, .dev(0));
    cfg_drv.set_id(m_env_cfg.cfg_id, .dev(0));

    // Mem
    cfg_drv.set_csr_base(m_env_cfg.mem_base, .dev(1));
    cfg_drv.set_id(m_env_cfg.cfg_id, .dev(1));

    // Rate limiter
    if (m_env_cfg.random_cfg_read_rate > 0) begin
      m_random_read_rate = axe_uvm_distribution::type_id::create("m_random_read_rate", this);
      m_random_read_rate.add_rate(1, m_env_cfg.random_cfg_read_rate);
    end
  endfunction : build_phase

  virtual task reset_phase (uvm_phase phase);
    reset();
  endtask : reset_phase

  virtual task reset();
    begin
    end
  endtask : reset

  task access(bit rnw, int unsigned idx, logic [63:0] data, int unsigned delay=0, int dev=0);
    // Delay
    repeat(delay) @(posedge cfg_vif.clk);

    if (rnw == 1'b0) begin
      cfg_drv.csr_wr(.reg_idx(idx), .data(data), .dev(dev));
    end
    else begin
      logic [63:0] rd_data;
      cfg_drv.csr_rd(.reg_idx(idx), .data(rd_data), .dev(dev));

      if (rd_data !== data) begin
        `uvm_fatal(get_full_name(), $psprintf("Internal Read Error: idx=0x%x Expected 0x%x Observed 0x%x", idx, data, rd_data));
      end
      else begin
        `uvm_info(get_full_name(), $psprintf("Internal Read Success : idx=0x%x Expected 0x%x Observed 0x%x", idx, data, rd_data), UVM_DEBUG);
      end
    end
  endtask : access

  task csr_access(logic rnw, int unsigned idx, logic [63:0] data, int unsigned delay=0);
    access( .rnw(rnw),
            .idx(idx),
            .data(data),
            .delay(delay),
            .dev(0));
  endtask : csr_access

  task mem_access(logic rnw, int unsigned idx, logic [63:0] data, int unsigned delay=0);
    access( .rnw(rnw),
            .idx(idx),
            .data(data),
            .delay(delay),
            .dev(1));
  endtask : mem_access

  task extmem_access(logic rnw, logic[63:0] addr, logic [63:0] data, int unsigned delay=0);
    if (rnw) begin
      logic [63:0] rd_data;
      rd_data = m_extmem_drv.mem[addr];
      if (rd_data !== data) begin
        `uvm_fatal(get_full_name(), $psprintf("External Read Error: idx=0x%x Expected 0x%x Observed 0x%x", addr, data, rd_data));
      end
      else begin
        `uvm_info(get_full_name(), $psprintf("External Read Success : idx=0x%x Expected 0x%x Observed 0x%x", addr, data, rd_data), UVM_DEBUG);
      end
    end
    else begin
      m_extmem_drv.mem[addr] = data;
    end
  endtask : extmem_access

  task program_cfg(timestamp_logger_cfg_item item);

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ST_ADDR,         item.st_addr);

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_COUNTER_CTRL,    ('0 | item.sync_ctrl   << 0
                                                                                             | item.stop        << 1
                                                                                             | item.reset       << 2));

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_LOG_SIZE,        item.log_size);

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_BURST_SIZE,      item.burst_size);

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_EN_0_63,   item.group_en[63:0]);

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_EN_64_127, item.group_en[127:64]);

    csr_access(1'b0, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL,            ('0  | item.capture_enable << 0
                                                                                              | item.trace_mode     << 1
                                                                                              | item.external_mode  << 2
                                                                                              | item.cntr_division  << 4));


    ap.write(item);
  endtask : program_cfg

  task random_cfg_read(timestamp_logger_cfg_item item);
    int delay;

    delay = m_random_read_rate.next();
    // TODO - HACKY while there's a race condition
    while (event_vif.capture_enable == 1'b0) @(posedge event_vif.clk);

    while(random_read_enable == 2'b01) begin

      randcase

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ST_ADDR,         item.st_addr);

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_COUNTER_CTRL,    ('0 | item.sync_ctrl   << 0
                                                                                                     | item.stop        << 1
                                                                                                     | item.reset       << 2));

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_LOG_SIZE,        item.log_size);

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_BURST_SIZE,      item.burst_size);

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_EN_0_63,   item.group_en[63:0]);

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_EN_64_127, item.group_en[127:64]);

        1 : csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL,            ('0  | item.capture_enable << 0
                                                                                                      | item.trace_mode     << 1
                                                                                                      | item.external_mode  << 2
                                                                                                      | item.cntr_division  << 4));

      endcase
      // Next delay - done after so the status is checked close to access
      delay = m_random_read_rate.next();
      repeat(delay) @(posedge cfg_vif.clk);
      if (!cfg_vif.rst_n)
        return;
    end
    random_read_enable = 2'b00;

  endtask : random_cfg_read


  task check_cfg(timestamp_logger_cfg_item item);
    logic [63:0] rd_data;

    // Wait for anything to drain as a result of disable - has to be big could be moving 1K as a flush
    repeat(5000) begin
      @(posedge cfg_vif.clk);
      if (!cfg_vif.rst_n)
        return;
    end

    if (m_env_cfg.rate_limit == 1'b1) begin
        // Should have no group overflows
        csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_TRIGGER_OVERFLOW_0, 0);
        csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_TRIGGER_OVERFLOW_1, 0);
        csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_STAMP_OVERFLOW,           0);
    end
    else begin
        // Check overflows - if overflow data is un-reliable
        logic [63:0] rd_data_0, rd_data_1, rd_data_2;
        cfg_drv.csr_rd(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_TRIGGER_OVERFLOW_0), .data(rd_data_0), .dev(0));
        cfg_drv.csr_rd(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_TRIGGER_OVERFLOW_1), .data(rd_data_1), .dev(0));
        cfg_drv.csr_rd(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_STAMP_OVERFLOW),           .data(rd_data_2), .dev(0));

        if (rd_data_0 | rd_data_1 | rd_data_2) begin
            `uvm_info(get_full_name(), "Group FIFO overflow - skipping log checks", UVM_DEBUG);
            return;
        end
    end


    // Check the entry count
    if (item.external_mode == 1'b0) begin
      csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ENTRY_COUNT, m_model.get_entry_count());
    end
    else begin
      csr_access(1'b1, timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ENTRY_COUNT, 0);
    end

    // Check memory
    for (int i = 0; i < m_model.get_log_size() ; i++) begin
        rd_data = m_model.get_entry(i);

        if (item.external_mode)
          extmem_access(1'b1, (item.st_addr + (8*i)), rd_data); // Based on Index
        else
          mem_access(1'b1, int'((item.st_addr/8)+i), rd_data); // Based on absolute address
    end

  endtask : check_cfg

  virtual task run_phase(uvm_phase phase);

    // Start the Designer AXI Component
    // This is easier than the Synopsys VIP and as we only use for config
    // doesn't require the level of randomisation
    fork
      cfg_drv.run();
    join_none

    reset();

    @(posedge cfg_vif.clk iff cfg_vif.rst_n);
    forever begin
      seq_item_port.get_next_item(req);

      // Random Reads
      if (req.capture_enable) begin
        if (m_env_cfg.random_cfg_read_rate > 0) begin
            random_read_enable = 1'b1;
            fork
                random_cfg_read(req);
            join_none
        end
      end
      else begin
        if (m_env_cfg.random_cfg_read_rate > 0) begin
          random_read_enable = 2'b10;
          while (random_read_enable != 2'b00)
              @(posedge cfg_vif.clk);
        end
      end

      program_cfg(req);

      if (!req.capture_enable) begin
        // Check results
        check_cfg(req);
      end

      seq_item_port.item_done();
    end

  endtask : run_phase
endclass : timestamp_logger_cfg_drv

`endif // GUARD_TIMESTAMP_LOGGER_CFG_DRV_SVH
