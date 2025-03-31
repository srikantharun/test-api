`ifndef SECURE_SPIKE_TOP_TEST_SV
`define SECURE_SPIKE_TOP_TEST_SV

import "DPI-C" context task spike_main(input string elf);

class spike_top_test extends uvm_test;

  `uvm_component_utils(spike_top_test)

  spike_top_env m_env;
  spike_top_config m_config;
  uvm_sw_ipc m_uvm_sw_ipc;
  extern function new(string name, uvm_component parent);

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern task wait_for_spm_preload();
  extern function void uvm_sw_ipc_gen_event(int event_idx);
  extern task uvm_sw_ipc_wait_event(int event_idx);
  extern function void uvm_sw_ipc_push_data(input int fifo_idx, input bit [63:0] data);
  extern function bit uvm_sw_ipc_pull_data(input int fifo_idx, output bit [63:0] data);
endclass : spike_top_test


function spike_top_test::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


function void spike_top_test::build_phase(uvm_phase phase);
  m_env = spike_top_env::type_id::create("m_env", this);
  m_uvm_sw_ipc = uvm_sw_ipc::type_id::create("m_uvm_sw_ipc", this);
endfunction : build_phase

function void spike_top_test::connect_phase(uvm_phase phase);
  m_config = m_env.m_config;
endfunction

task spike_top_test::run_phase(uvm_phase phase);
  wait_for_spm_preload();
  // Exit code and end-of-test are handled by uvm_sw_ipc
  spike_main(m_config.m_elf);
endtask : run_phase

task spike_top_test::wait_for_spm_preload();
  wait (m_config.axi_vif.master_if[0].aresetn === 1);
  @(posedge m_config.axi_vif.common_aclk);
endtask : wait_for_spm_preload

function void spike_top_test::uvm_sw_ipc_gen_event(int event_idx);
  m_uvm_sw_ipc.uvm_sw_ipc_gen_event(event_idx);
endfunction


task spike_top_test::uvm_sw_ipc_wait_event(int event_idx);
  m_uvm_sw_ipc.uvm_sw_ipc_wait_event(event_idx);
endtask


function void spike_top_test::uvm_sw_ipc_push_data(input int fifo_idx, input bit [63:0] data);
  m_uvm_sw_ipc.uvm_sw_ipc_push_data(fifo_idx, data);
endfunction


function bit spike_top_test::uvm_sw_ipc_pull_data(input int fifo_idx, output bit [63:0] data);
  return m_uvm_sw_ipc.uvm_sw_ipc_pull_data(fifo_idx, data);
endfunction

`endif  // SECURE_SPIKE_TOP_TEST_SV
