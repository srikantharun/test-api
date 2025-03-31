`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_MON_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_MON_SVH

class ai_core_dp_cmd_gen_cmdb_mon extends uvm_monitor;

  virtual dp_cmd_gen_cmdb_if        cmdb_vif;
  ai_core_dp_cmd_gen_cmdb           cmdbQ[$];

  `uvm_component_utils(ai_core_dp_cmd_gen_cmdb_mon)

  uvm_analysis_port#(ai_core_dp_cmd_gen_cmdb) ap;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db #(virtual dp_cmd_gen_cmdb_if)::get(this, "", "cmdb_vif", cmdb_vif)); 
    ap = new("ap", this);
  endfunction : build_phase

  virtual task monitor_reset(uvm_phase phase);
    @(negedge cmdb_vif.rst_n);
    `uvm_info(get_full_name(), $sformatf("Reset was seen on the cmdb interface and monitor will be reset"), UVM_LOW)

    phase.drop_objection(this, .count(cmdbQ.size())); 
    cmdbQ.delete();

    @(posedge cmdb_vif.rst_n);
    `uvm_info(get_full_name(), $sformatf("Reset done!"), UVM_LOW)
  endtask : monitor_reset

  virtual task monitor_cmdb(uvm_phase phase);
    forever begin
      @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);

      if (cmdb_vif.cmdb_valid) begin
        ai_core_dp_cmd_gen_cmdb cmdb = new("from_monitor");
        phase.raise_objection(this);
        cmdb.valid             = cmdb_vif.cmdb_valid;
        cmdb.format            = cmdb_vif.cmdb_format;
        cmdb.nested_1_map_main = cmdb_vif.cmdb_command.view_struct.nested_1_map_main;
        cmdb.nested_1          = cmdb_vif.cmdb_command.view_struct.nested_1;
        cmdb.nested_0_map_main = cmdb_vif.cmdb_command.view_struct.nested_0_map_main;
        cmdb.nested_0          = cmdb_vif.cmdb_command.view_struct.nested_0;
        cmdb.main_2            = cmdb_vif.cmdb_command.view_struct.main_2;
        cmdb.reserved_0        = cmdb_vif.cmdb_command.view_struct.reserved_0;
        cmdb.reserved_1        = cmdb_vif.cmdb_command.view_struct.reserved_1;
        cmdb.main_1            = cmdb_vif.cmdb_command.view_struct.main_1;
        cmdb.extra             = cmdb_vif.cmdb_command.view_struct.extra;
        cmdb.main_0            = cmdb_vif.cmdb_command.view_struct.main_0;
        cmdb.valid_cycle       = cmdb_vif.cycle_count;

        while (!cmdb_vif.cmdb_ready) begin
          @(posedge cmdb_vif.clk);
          if (!cmdb_vif.rst_n) break;
        end

        cmdb.ready_cycle       = cmdb_vif.cycle_count;
        cmdb.timestamp         = $realtime;
        cmdbQ.push_back(cmdb);
      end
    end
  endtask : monitor_cmdb

  virtual task monitor_done(uvm_phase phase);
      forever begin
        @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
        if (cmdb_vif.cmdb_done) begin
          ai_core_dp_cmd_gen_cmdb cmdb = cmdbQ.pop_front();
          cmdb.done_cycle = cmdb_vif.cycle_count;
          cmdb.errors     = cmdb_vif.cmdb_errors;
          ap.write(cmdb);
          phase.drop_objection(this);
        end
      end
  endtask: monitor_done

  virtual task run_phase(uvm_phase phase);
    fork
      monitor_reset(phase);
      monitor_cmdb(phase);
      monitor_done(phase);
    join_none

    wait fork;
  endtask : run_phase
endclass : ai_core_dp_cmd_gen_cmdb_mon

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_MON_SVH
