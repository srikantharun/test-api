`ifndef UVM_SW_IPC_CONFIG_SV
`define UVM_SW_IPC_CONFIG_SV

class uvm_sw_ipc_config extends uvm_object;

  // Do not register config class with the factory

  virtual uvm_sw_ipc_if    vif;

  // 0: uvm_sw_ipc's instance won't block the test completion
  // 1: uvm_sw_ipc's instance will  block the test completion until uvm_sw_ipc_quit() or sys_exit() is called
  bit handle_end_of_test;

  // low-level API
  bit [63:0] cmd_address;
  bit [63:0] fifo_data_to_uvm_address[UVM_SW_IPC_FIFO_NB];
  bit [63:0] fifo_data_to_sw_address[UVM_SW_IPC_FIFO_NB];
  bit [63:0] fifo_data_to_sw_empty_address;

  bit [63:0] start_address;
  bit [63:0] end_address;

  function new(string name = "", bit [63:0] base_address, bit handle_end_of_test = 1);
    super.new(name);
    this.handle_end_of_test       = handle_end_of_test;

    // populate all addresses
    start_address                 = base_address + 0 * UVM_SW_IPC_FIFO_OFFSET;
    cmd_address                   = base_address + 0 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_uvm_address[0]   = base_address + 1 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_uvm_address[1]   = base_address + 2 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_uvm_address[2]   = base_address + 3 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_sw_address[0]    = base_address + 4 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_sw_address[1]    = base_address + 5 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_sw_address[2]    = base_address + 6 * UVM_SW_IPC_FIFO_OFFSET;
    fifo_data_to_sw_empty_address = base_address + 7 * UVM_SW_IPC_FIFO_OFFSET;
    end_address                   = base_address + 8 * UVM_SW_IPC_FIFO_OFFSET;

  endfunction : new

  function void do_print(uvm_printer printer);
    printer.print_int("start_address", start_address, $bits(start_address));
    printer.print_int("cmd_address", cmd_address, $bits(cmd_address));
    foreach (fifo_data_to_uvm_address[i]) begin
      printer.print_int($sformatf("fifo_data_to_uvm_address[%0d]", i), fifo_data_to_uvm_address[i],
                        $bits(fifo_data_to_uvm_address[i]));
    end

    foreach (fifo_data_to_sw_address[i]) begin
      printer.print_int($sformatf("fifo_data_to_sw_address[%0d]", i), fifo_data_to_sw_address[i],
                        $bits(fifo_data_to_sw_address[i]));
    end
    printer.print_int("data_to_sw_empty_address", fifo_data_to_sw_empty_address, $bits(
                      fifo_data_to_sw_empty_address));
    printer.print_int("end_address", end_address, $bits(end_address));
  endfunction

endclass : uvm_sw_ipc_config


`endif  // UVM_SW_IPC_CONFIG_SV
