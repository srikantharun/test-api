`ifndef AI_CORE_CD_MONITOR_SV
`define AI_CORE_CD_MONITOR_SV

class ai_core_cd_monitor extends uvm_monitor;
  `uvm_component_utils(ai_core_cd_monitor)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual ai_core_cd_if vif;

  uvm_analysis_port#(ai_core_cd_seq_item) ap;

  ai_core_cd_seq_item item_mon;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    item_mon = new();
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    forever begin
      @(posedge vif.reset_n_i);
      fork begin
	fork
          begin: ai_core_cd_mon
            forever @(vif.mon) begin
              item_mon.reset_n_i   = vif.mon.reset_n_i;
              item_mon.irq_o        = vif.mon.irq_o;

              ap.write(item_mon.do_clone());
            end
          end
          //-//@(negedge vif.reset_n_i) disable ai_core_cd_mon;
          @(negedge vif.reset_n_i);
       join_any
       disable fork;
     end join // fork
    end
  endtask

endclass

`endif


