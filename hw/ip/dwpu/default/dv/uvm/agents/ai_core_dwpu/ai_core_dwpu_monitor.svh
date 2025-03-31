`ifndef AI_CORE_DWPU_MONITOR_SV
`define AI_CORE_DWPU_MONITOR_SV

class ai_core_dwpu_monitor extends uvm_monitor;
  `uvm_component_utils(ai_core_dwpu_monitor)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual ai_core_dwpu_if vif;

  uvm_analysis_port#(ai_core_dwpu_seq_item) ap;

  ai_core_dwpu_seq_item item_mon;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    item_mon = new();
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    forever begin
      @(posedge vif.reset_an_i);
      fork
        begin: ai_core_dwpu_mon
          forever @(vif.mon) begin
            item_mon.reset_an_i   = vif.mon.reset_an_i;
            item_mon.irq_o        = vif.mon.irq_o;
            item_mon.obs_o        = vif.mon.obs_o;
            item_mon.cid_i        = vif.mon.cid_i;
            item_mon.trace_vld_o  = vif.mon.trace_vld_o;

            ap.write(item_mon.do_clone());
          end
        end
        @(negedge vif.reset_an_i) disable ai_core_dwpu_mon;
      join
    end
  endtask
endclass

`endif


