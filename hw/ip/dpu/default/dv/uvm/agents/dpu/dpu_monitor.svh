`ifndef DPU_MONITOR_SV
`define DPU_MONITOR_SV

class dpu_monitor extends uvm_monitor;
  `uvm_component_utils(dpu_monitor)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual dpu_if vif;

  uvm_analysis_port#(dpu_seq_item) ap;

  dpu_seq_item item_mon;

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

        begin: dpu_mon
          forever @(vif.mon) begin
            item_mon.reset_an_i = vif.mon.reset_an_i;
            item_mon.irq_o      = vif.mon.irq_o;
            ap.write(item_mon.do_clone());
	        end
        end

        @(negedge vif.reset_an_i) disable dpu_mon;

      join
    end
  endtask
endclass

`endif


