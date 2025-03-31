`ifndef DMC_ADDR_GEN_MONITOR_SV
`define DMC_ADDR_GEN_MONITOR_SV

class dmc_addr_gen_monitor extends uvm_monitor;
  `uvm_component_utils(dmc_addr_gen_monitor)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual dmc_addr_gen_if vif;

  uvm_analysis_port#(dmc_addr_gen_seq_item) ag_ap;
  uvm_analysis_port#(dmc_addr_gen_seq_item) dpc_ap;

  dmc_addr_gen_seq_item cmd_items[$]; // command programmed in cmdblk
  uvm_event m_addr_gen_evt_h;
  mem_baseaddr_t l1_base_addr;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ag_ap  = new("ag_ap", this);
    dpc_ap = new("dpc_ap", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    dmc_addr_gen_seq_item ag_item, dpc_item, evt_item, compare_item;
    uvm_object obj;
    super.run_phase(phase);
    forever begin
      @(posedge vif.reset_an_i);
      `uvm_info(get_name(), "Reset negated!", UVM_LOW)
      fork
        forever begin
          m_addr_gen_evt_h.wait_trigger_data(obj);
          if (!$cast(evt_item, obj)) begin
            `uvm_fatal(get_type_name(), "Cast failed!")
          end else begin
            if (cmd_items.size() < CMDB_FIFO_DEPTH+2) begin // tolerance of 2 in corner case of simultaneous push/pop of commands in FIFO and waiting for tokens
              cmd_items.push_back(evt_item);
            end else begin
              `uvm_info(get_name(), $sformatf("Not pushing item because of FIFO FULL! Total commands: %0d", cmd_items.size()), UVM_LOW)
            end
          end
        end
        forever begin
          @(vif.mon);
          if (vif.mon.ag_vld===1 && vif.mon.ag_rdy===1 &&
              uvm_root::get().find("uvm_test_top").get_type_name() != "aic_ls_icdf_stimuli_test") begin
            ag_item = dmc_addr_gen_seq_item::type_id::create("ag_item");
            ag_item.m_has_cmd = 1;
            ag_item.m_cmd = vif.mon.ag_cmd;
            ag_item.set_cmd_to_fields();
            if (cmd_items.size() == 0) begin
              `uvm_error(get_name(), $sformatf("Unexpected Addr Gen Item! %s", ag_item.convert2string()))
            end else begin
              compare_item = cmd_items.pop_front();
              compare_item.m_has_cmd = 1;
              compare_item.m_l1_base_addr = l1_base_addr;
              compare_item.compare_cmd(ag_item, get_full_name()); // compare cmd input vs addr gen output
            end
            ag_ap.write(compare_item);
            `uvm_info(get_full_name(), $sformatf("Has AG item!, %0d compare_item's left", cmd_items.size()), UVM_LOW)
          end
        end
        forever begin
          @(vif.mon);
          if (vif.mon.dpc_vld===1 && vif.mon.dpc_rdy===1) begin
            dpc_item = dmc_addr_gen_seq_item::type_id::create("dpc_item");
            dpc_item.m_has_dpc_cmd = 1;
            dpc_item.m_dpc_cmd = {vif.mon.dpc_addr, vif.mon.dpc_msk, vif.mon.dpc_format, vif.mon.dpc_config, vif.mon.dpc_pad, vif.mon.dpc_last, vif.mon.dpc_pad_val, vif.mon.dpc_intra_pad_val, vif.mon.err_addr_out_of_range};
            if (dpc_item.m_dpc_cmd.dpc_pad) begin
              dpc_item.m_dpc_cmd.dpc_addr = 0; // match w/ python model
            end
            dpc_ap.write(dpc_item);
            `uvm_info(get_full_name(), "Has DPC item!", UVM_FULL)
          end
        end
        @(negedge vif.reset_an_i);
      join_any
      disable fork;
      cmd_items.delete();
      `uvm_info(get_name(), "Reset detected!", UVM_LOW)
    end
  endtask
endclass

`endif


