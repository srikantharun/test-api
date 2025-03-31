`ifndef FW_BASE_TEST_SV
`define FW_BASE_TEST_SV

`ifdef ENABLE_DECODER_SCOREBOARD
  import decoder_uvm_pkg::*;
  `include "allegro_tb_demoter.svh"
`endif

class fw_base_test extends uvm_test;
  `uvm_component_utils(fw_base_test)
  
  `ifdef ENABLE_DECODER_SCOREBOARD
    decoder_env m_decoder_env;
    allegro_tb_demoter m_demoter;
  `endif

  uvm_sw_ipc m_uvm_sw_ipc[CORE_NUMBER];

  function void uvm_sw_ipc_gen_event(int hart_id, int event_idx);
    m_uvm_sw_ipc[hart_id].uvm_sw_ipc_gen_event(event_idx);
  endfunction


  task uvm_sw_ipc_wait_event(int hart_id, int event_idx);
    m_uvm_sw_ipc[hart_id].uvm_sw_ipc_wait_event(event_idx);
  endtask


  function void uvm_sw_ipc_push_data(input int hart_id, input int fifo_idx, input bit [63:0] data);
    m_uvm_sw_ipc[hart_id].uvm_sw_ipc_push_data(fifo_idx, data);
  endfunction


  function bit uvm_sw_ipc_pull_data(input int hart_id, input int fifo_idx, output bit [63:0] data);
    return m_uvm_sw_ipc[hart_id].uvm_sw_ipc_pull_data(fifo_idx, data);
  endfunction


  function new(string name = "fw_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    foreach (m_uvm_sw_ipc[i]) begin
      m_uvm_sw_ipc[i] = uvm_sw_ipc::type_id::create($sformatf("m_uvm_sw_ipc[%0d]", i), this);
    end

    `ifdef ENABLE_DECODER_SCOREBOARD
      m_decoder_env = decoder_env::type_id::create("m_decoder_env", this);
      m_demoter = allegro_tb_demoter::type_id::create("m_demoter", this);
      uvm_report_cb::add(null, m_demoter);
    `endif

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase


  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction : end_of_elaboration_phase
endclass

`endif  // FW_BASE_TEST_SV
