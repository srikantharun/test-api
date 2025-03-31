// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_EVENT_DRV_SVH
`define GUARD_TIMESTAMP_LOGGER_EVENT_DRV_SVH

class timestamp_logger_event_drv extends uvm_driver#(timestamp_logger_event_item);

  timestamp_logger_env_cfg          m_env_cfg;
  virtual timestamp_logger_event_if event_vif;
  logic [31:0]                      rate_limiter[`NUM_GROUPS];

  `uvm_component_utils_begin(timestamp_logger_event_drv)
    `uvm_field_sarray_int( rate_limiter, UVM_DEFAULT)
  `uvm_component_utils_end

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    assert(uvm_config_db #(virtual timestamp_logger_event_if)::get(this, "", "event_vif",  event_vif));
    assert(uvm_config_db#(timestamp_logger_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));
  endfunction : build_phase

  virtual task reset_phase (uvm_phase phase);
    reset();
  endtask : reset_phase

  virtual task reset();
    event_vif.sync_start     <= '0;
    event_vif.group_triggers <= '0;
    event_vif.group_msgs     <= '0;
  endtask : reset

  virtual task rate_limit_monitor();
    for (int i = 0; i < `NUM_GROUPS; i++) begin
        rate_limiter[i] = '0;
    end

    if (!m_env_cfg.rate_limit) return;

    forever begin
        @(posedge event_vif.clk);
        for (int i = 0; i < `NUM_GROUPS; i++) begin
            rate_limiter[i] =  {rate_limiter[i][30:0], event_vif.group_triggers[i]};
        end
    end
  endtask : rate_limit_monitor

  virtual task run_phase(uvm_phase phase);
    reset();

    fork begin
        rate_limit_monitor();
    end
    join_none

    @(posedge event_vif.clk iff event_vif.rst_n);
    forever begin
      seq_item_port.get_next_item(req);

      repeat(req.delay) begin
        @(posedge event_vif.clk)
        if (!event_vif.rst_n) begin
          reset();
          continue;
        end
      end

      event_vif.sync_start <= req.sync_start;

      for (int i = 0; i < m_env_cfg.n_groups; i++) begin
        event_vif.group_triggers[i] <= ($countones(rate_limiter[i]) >= `GROUP_FIFO_DEPTH[i]) ? 1'b0 : req.triggers[i];
        event_vif.group_msgs[i]     <= req.msgs[i];
      end

      @(posedge event_vif.clk);
      reset();
      seq_item_port.item_done();
    end

  endtask : run_phase
endclass : timestamp_logger_event_drv

`endif // GUARD_TIMESTAMP_LOGGER_EVENTDRV_SVH
