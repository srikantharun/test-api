`ifndef IAU_MONITOR_SV
`define IAU_MONITOR_SV

class iau_monitor extends uvm_monitor;
  `uvm_component_utils(iau_monitor)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual iau_if vif;

  uvm_analysis_port#(iau_seq_item) ap;

  iau_seq_item item_mon;

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
        begin: iau_mon
          forever @(vif.mon) begin
            item_mon.reset_an_i = vif.mon.reset_an_i;
            item_mon.irq_o      = vif.mon.irq_o;
            item_mon.obs_o      = vif.mon.obs_o;
            item_mon.cid_i      = vif.mon.cid_i;
            item_mon.block_id_i = vif.mon.block_id_i;

            ap.write(item_mon.do_clone());
          end
        end
        @(negedge vif.reset_an_i) disable iau_mon;
      join
    end
  endtask
endclass

`endif


