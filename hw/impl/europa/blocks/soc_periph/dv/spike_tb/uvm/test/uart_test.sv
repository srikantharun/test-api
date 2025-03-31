`ifndef SOC_PERIPH_UART_TEST_SV
`define SOC_PERIPH_UART_TEST_SV

virtual class uart_xactor_wrapper_abstract extends uvm_object;
  `uvm_object_utils(uart_xactor_wrapper_abstract)

  function new(string name = "");
    super.new(name);
  endfunction

  pure virtual task send_char(input bit [7:0] char);

  pure virtual task receive_char(output bit [7:0] char);
endclass


class uart_test extends spike_top_test;

  int unsigned m_txrx_max_pkt;
  uart_xactor_wrapper_abstract m_uart_xactor;

  `uvm_component_utils(uart_test)

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern task send_random_char();
  extern task receive_char();
endclass : uart_test


function uart_test::new(string name, uvm_component parent);
  super.new(name, parent);
  m_uart_xactor = uart_xactor_wrapper_abstract::type_id::create("m_uart_xactor");
endfunction : new

task uart_test::run_phase(uvm_phase phase);
  fork
    begin
      super.run_phase(phase);
    end
  join_none
  uvm_sw_ipc_wait_event(0);
  if (!uvm_sw_ipc_pull_data(0, m_txrx_max_pkt)) `uvm_fatal(get_type_name(), "No data to pull!")
  `uvm_info(get_type_name(), $sformatf("Exchanging %0d characters", m_txrx_max_pkt), UVM_LOW)
  fork
    begin
      repeat (m_txrx_max_pkt) send_random_char();
    end
    begin
      repeat (m_txrx_max_pkt) receive_char();
    end
  join
  uvm_sw_ipc_gen_event(0);  // Notify C that we have finished
endtask : run_phase

task uart_test::send_random_char();
  bit [7:0] char = $urandom_range(0, 255);
  m_uart_xactor.send_char(char);
  `uvm_info(get_type_name(), $sformatf("Sent: 0x%0x", char), UVM_HIGH)
  uvm_sw_ipc_push_data(0, char);
endtask

task uart_test::receive_char();
  bit [7:0] char;
  m_uart_xactor.receive_char(char);
  `uvm_info(get_type_name(), $sformatf("Received: 0x%0x", char), UVM_HIGH)
  uvm_sw_ipc_push_data(1, char);
endtask

`endif  // SOC_PERIPH_UART_TEST_SV
