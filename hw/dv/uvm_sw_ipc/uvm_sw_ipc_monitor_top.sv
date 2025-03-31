`ifndef UVM_SW_IPC_MONITOR_TOP_SV
`define UVM_SW_IPC_MONITOR_TOP_SV

class uvm_sw_ipc_monitor extends uvm_monitor;

  `uvm_component_utils(uvm_sw_ipc_monitor)

  virtual uvm_sw_ipc_if              vif;
  uvm_sw_ipc_config                  m_config;
  uvm_analysis_port #(uvm_sw_ipc_tx) analysis_port;

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern task do_mon();

endclass : uvm_sw_ipc_monitor


function uvm_sw_ipc_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
  analysis_port = new("analysis_port", this);
endfunction : new


task uvm_sw_ipc_monitor::run_phase(uvm_phase phase);
  `uvm_info(get_type_name(), "run_phase", UVM_HIGH)

  do_mon();
endtask : run_phase


task uvm_sw_ipc_monitor::do_mon();
  uvm_sw_ipc_tx tx;
  bit read_data_next_cycle = 0;

  wait (vif.cb.reset == 0);

  forever begin
    @(vif.cb);

    if (read_data_next_cycle) begin
      tx.data = vif.cb.rdata;
      analysis_port.write(tx);
    end
    read_data_next_cycle = 0;

    while (vif.cb.cen !== 1) begin
      @(vif.cb);
    end
    tx = uvm_sw_ipc_tx::type_id::create("tx");
    tx.addr = vif.cb.address;
    tx.rwb  = vif.cb.wen === 0;

    if (vif.cb.wen === 1) begin
      // write data
      for (int i = 0; i < 8; i++) begin
        tx.data[i*8+:8] = vif.cb.byteen[i] ? vif.cb.wdata[i*8+:8] : 8'b0;
      end
      analysis_port.write(tx);
    end else begin
      // read data next cycle
      read_data_next_cycle = 1;
    end
  end

endtask : do_mon

`endif  // UVM_SW_IPC_MONITOR_TOP_SV
