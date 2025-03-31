`ifndef SOC_IO_TIMER_TEST_SV
`define SOC_IO_TIMER_TEST_SV

`define SOC_PERIPH_TIMER_NB 2

class timer_test extends spike_top_test;

  `uvm_component_utils(timer_test)

  extern function new(string name, uvm_component parent);

  extern task run_phase(uvm_phase phase);
endclass : timer_test


function timer_test::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


task timer_test::run_phase(uvm_phase phase);
  fork
    begin
      super.run_phase(phase);
    end
  join_none

  repeat (`SOC_PERIPH_TIMER_NB) begin
    int t0;
    uvm_sw_ipc_wait_event(0);
    `uvm_info(get_type_name(), "Waiting for interrupt", UVM_LOW)
    t0 = $time;
    @(posedge m_config.timer_vif.mon_cb.timer_int);
    `uvm_info(get_type_name(), "Interrupt triggered!", UVM_LOW)
    uvm_sw_ipc_push_data(0, $time - t0);
    uvm_sw_ipc_gen_event(0);
  end
endtask : run_phase

`endif  // SOC_IO_TIMER_TEST_SV
