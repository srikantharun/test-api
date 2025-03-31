// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_MON_SVH
`define GUARD_TIMESTAMP_LOGGER_MON_SVH

class timestamp_logger_event_mon extends uvm_monitor;

  virtual timestamp_logger_event_if event_vif;
  timestamp_logger_event_item       cov_item[$];
  int unsigned                      cycle_count = 0;
  int unsigned                      prev_cycle_count = 0;

  covergroup cg;
        option.per_instance = 1'b1;
        option.name         = "cg";

        cp_n_triggers0:  coverpoint $countones(cov_item[0].triggers) {
          bins n[] = {[1:`NUM_GROUPS]};
        }
        cp_n_triggers1:  coverpoint $countones(cov_item[1].triggers) iff (cov_item.size() >= 2) {
          bins n[] = {[1:`NUM_GROUPS]};
        }
        cp_delay0:       coverpoint cov_item[0].delay                iff (cov_item.size() >= 2) {
          bins s[] = {[0:2]};
          bins m   = {[3:8]};
          bins l   = {[9:$]};
        }
         cp_delay1:       coverpoint cov_item[1].delay               iff (cov_item.size() >= 3) {
          bins s[] = {[0:2]};
          bins m   = {[3:8]};
          bins l   = {[9:$]};
        }
        cp_n_b2b:         coverpoint $countones(cov_item[0].triggers & cov_item[1].triggers) iff ((cov_item.size() >= 2) && (cov_item[0].delay == 0)) {
          bins s[] = {[0:2]};
         }

        cc_n_X_delay: cross cp_n_triggers0, cp_delay0      iff (cov_item.size() >= 2);
        cc_n_X_n:     cross cp_n_triggers0, cp_n_triggers1 iff (cov_item.size() >= 2);
        cc_delay:     cross cp_delay0, cp_delay1           iff (cov_item.size() >= 3);

    endgroup : cg

  uvm_analysis_port#(timestamp_logger_event_item) ap;

  `uvm_component_utils(timestamp_logger_event_mon)

  function new (string name, uvm_component parent);
    super.new (name, parent);
    cg = new();
  endfunction : new

  function void build_phase(uvm_phase phase);
    assert(uvm_config_db #(virtual timestamp_logger_event_if)::get(this, "", "event_vif",  event_vif));
    ap = new("ap", this);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    cycle_count = 0;

    forever begin
      @(posedge event_vif.clk iff event_vif.rst_n);

      if (event_vif.group_triggers != '0) begin
        timestamp_logger_event_item item = new("from_monitor");
        item.triggers  = event_vif.group_triggers;
        item.msgs      = event_vif.group_msgs;
        item.timestamp = event_vif.timestamp;
        item.delay     = cycle_count - prev_cycle_count -1;

        prev_cycle_count = cycle_count;

        ap.write(item);

        cov_item.push_front(item);
        if (cov_item.size() > 3) void'(cov_item.pop_back());
        cg.sample();
      end
      cycle_count += 1;
    end
  endtask : run_phase
endclass : timestamp_logger_event_mon

`endif // GUARD_TIMESTAMP_LOGGER_MON_SVH
