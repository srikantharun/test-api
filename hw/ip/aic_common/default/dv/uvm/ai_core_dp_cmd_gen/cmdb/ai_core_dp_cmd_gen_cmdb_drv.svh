`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_DRV
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_DRV

class ai_core_dp_cmd_gen_cmdb_drv extends uvm_driver#(ai_core_dp_cmd_gen_cmdb);

  virtual dp_cmd_gen_cmdb_if                  cmdb_vif;

  ai_core_dp_cmd_gen_cmdb                     cmdb;

  ai_core_dp_cmd_gen_env_cfg                  m_env_cfg;

  axe_uvm_numeric_pkg::axe_uvm_distribution   m_distribution = new();

  uvm_analysis_port#(ai_core_dp_cmd_gen_cmdb) ap;

  `uvm_component_utils(ai_core_dp_cmd_gen_cmdb_drv)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db #(virtual dp_cmd_gen_cmdb_if)::get(this, "", "cmdb_vif", cmdb_vif));
    assert(uvm_config_db#(ai_core_dp_cmd_gen_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));

    ap = new("ap", this);
  endfunction

  virtual task reset_phase (uvm_phase phase);
    reset();
  endtask : reset_phase

  virtual task reset();
    cmdb_vif.cmdb_valid                                 <= 1'b0;
    cmdb_vif.cmdb_format                                <= aic_dp_cmd_gen_pkg::cmd_format_e'('0);
    cmdb_vif.cmdb_command.view_struct.main_0            <= aic_dp_cmd_gen_pkg::loop_description_t'(0);
    cmdb_vif.cmdb_command.view_struct.main_1            <= aic_dp_cmd_gen_pkg::loop_description_t'(0);
    cmdb_vif.cmdb_command.view_struct.main_2            <= aic_dp_cmd_gen_pkg::loop_description_t'(0);
    cmdb_vif.cmdb_command.view_struct.nested_0_map_main <= aic_dp_cmd_gen_pkg::loop_index_t'(0);
    cmdb_vif.cmdb_command.view_struct.nested_0          <= aic_dp_cmd_gen_pkg::loop_description_t'(0); 
    cmdb_vif.cmdb_command.view_struct.nested_1_map_main <= aic_dp_cmd_gen_pkg::loop_index_t'(0);;
    cmdb_vif.cmdb_command.view_struct.nested_1          <= aic_dp_cmd_gen_pkg::loop_description_t'(0);
    cmdb_vif.cmdb_command.view_struct.extra             <= aic_dp_cmd_gen_pkg::command_extra_t'(0);
    cmdb_vif.cmdb_command.view_struct.reserved_0        <= aic_dp_cmd_gen_pkg::command_reserved_t'(0);
    cmdb_vif.cmdb_command.view_struct.reserved_1        <= aic_dp_cmd_gen_pkg::command_reserved_t'(0);
  endtask : reset

  virtual task flush_cmdb(int delay);
    for (int i = 0; i < delay; i++)
      @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
    
    cmdb_vif.cmdb_flush <= 1'b1;
    @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
    cmdb_vif.cmdb_flush <= 1'b0;

  endtask : flush_cmdb

  virtual task run_phase(uvm_phase phase);
    m_distribution.add_rate(1, m_env_cfg.cmdb_rate);
    this.m_env_cfg.print();
    reset();

    @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);

    fork
      forever begin
        int unsigned _delay = m_distribution.next();

        repeat(_delay) begin
          @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
        end

        seq_item_port.get_next_item(req);

        // Send to ap as base class (required for comparision)
        cmdb = new("from_driver");
        cmdb.copy(req);
        ap.write(cmdb);

        cmdb_vif.cmdb_valid                                 <= req.valid;
        cmdb_vif.cmdb_format                                <= req.format;
        cmdb_vif.cmdb_command.view_struct.main_0            <= req.main_0;
        cmdb_vif.cmdb_command.view_struct.main_1            <= req.main_1;
        cmdb_vif.cmdb_command.view_struct.main_2            <= req.main_2;
        cmdb_vif.cmdb_command.view_struct.nested_0_map_main <= req.nested_0_map_main;
        cmdb_vif.cmdb_command.view_struct.nested_0          <= req.nested_0;
        cmdb_vif.cmdb_command.view_struct.nested_1_map_main <= req.nested_1_map_main;
        cmdb_vif.cmdb_command.view_struct.nested_1          <= req.nested_1;
        cmdb_vif.cmdb_command.view_struct.extra             <= req.extra;
        cmdb_vif.cmdb_command.view_struct.reserved_0        <= req.reserved_0;
        cmdb_vif.cmdb_command.view_struct.reserved_1        <= req.reserved_1;

        if (cmdb.flush_delay >= 0) begin
          fork : flush_fork
          begin
            flush_cmdb(cmdb.flush_delay);
          end
          join_none;
        end

        fork : wait_fork
        begin
          while (1) begin
            @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
            if (cmdb_vif.cmdb_flush)
              break;
          end
        end
        begin
          while(1) begin
            @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
            if (cmdb_vif.cmdb_valid && cmdb_vif.cmdb_ready) begin
              `uvm_info(get_name(), $psprintf("\n%s", cmdb.sprint()), UVM_LOW);
              break;
            end
          end

          reset();

          if (m_env_cfg.cmdb_wait_on_done) begin
            while (1) begin
              @(posedge cmdb_vif.clk iff cmdb_vif.rst_n);
              if (cmdb_vif.cmdb_done)
                break;
            end
          end
        end
        join_any;
        disable wait_fork;

        seq_item_port.item_done();
      end
    join
  endtask
endclass

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_DRV

