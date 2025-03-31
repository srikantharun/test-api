`ifndef GUARD_AI_CORE_DP_CMD_GEN_COMMAND_MON_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_COMMAND_MON_SVH

class ai_core_dp_cmd_gen_command_mon#(type dp_command_t) extends uvm_monitor;

  virtual dp_cmd_gen_command_if#(dp_command_t)  command_vif;

  `uvm_component_param_utils(ai_core_dp_cmd_gen_command_mon#(dp_command_t))

  uvm_analysis_port#(ai_core_dp_cmd_gen_command#(dp_command_t)) ap;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db #(virtual dp_cmd_gen_command_if#(dp_command_t))::get(this, "", "command_vif", command_vif)); 
    ap = new("ap", this);
  endfunction : build_phase

  virtual task monitor_reset();
    @(negedge command_vif.rst_n);
    `uvm_info(get_full_name(), $sformatf("Reset was seen on the command interface and monitor will be reset"), UVM_LOW)

    @(posedge command_vif.rst_n);
    `uvm_info(get_full_name(), $sformatf("Reset done!"), UVM_LOW)
  endtask : monitor_reset

  virtual task monitor_command();
    forever begin
      @(posedge command_vif.clk iff command_vif.rst_n);

      if (command_vif.command_valid && command_vif.command_ready) begin
        ai_core_dp_cmd_gen_command#(dp_command_t) command = new("from_monitor");

        command.data              = command_vif.command_data; 
        command.format            = command_vif.command_metadata.format;
        command.extra             = command_vif.command_metadata.extra;
        command.last              = command_vif.command_last;
        command.overall_last      = command_vif.command_iterations.overall_last;
        command.nested_1          = command_vif.command_iterations.nested_1;
        command.nested_0          = command_vif.command_iterations.nested_0;
        command.main              = command_vif.command_iterations.main;
        command.main_index        = command_vif.command_iterations.main_index;
        command.timestamp         = $realtime;
        ap.write(command);
      end
    end
  endtask : monitor_command

  virtual task run_phase(uvm_phase phase);
    fork
      monitor_reset();
      monitor_command();
    join_none

    wait fork;
  endtask : run_phase
endclass : ai_core_dp_cmd_gen_command_mon

`endif // GUARD_AI_CORE_DP_CMD_GEN_COMMAND_MON_SVH
