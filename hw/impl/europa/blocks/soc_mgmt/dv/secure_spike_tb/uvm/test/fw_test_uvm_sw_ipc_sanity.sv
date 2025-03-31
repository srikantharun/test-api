`ifndef GUARD_FW_TEST_UVM_SW_IPC_SANITY_SV
`define GUARD_FW_TEST_UVM_SW_IPC_SANITY_SV

class fw_test_uvm_sw_ipc_sanity extends spike_top_test;

  `uvm_component_utils(fw_test_uvm_sw_ipc_sanity)


  function new(string name = "fw_test_uvm_sw_ipc_sanity", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new


  task basic_test();
    bit [31:0] n;
    bit [63:0] data_to_uvm;
    bit [63:0] ref_data_arr[2];
    int i;

    `uvm_info(get_type_name(), "start SPIKE", UVM_LOW);
    n = 0;
    ref_data_arr[0] = {n, 32'hdeadbeef};
    ref_data_arr[1] = {n, 32'hcafedeca};

    uvm_sw_ipc_wait_event(16);
    `uvm_info(get_type_name(), "running sequence", UVM_LOW);
    #1000ns;
    `uvm_info(get_type_name(), "sequence done", UVM_LOW);
    uvm_sw_ipc_push_data(0, ref_data_arr[0]);
    uvm_sw_ipc_push_data(0, ref_data_arr[1]);
    `uvm_info(get_type_name(), "data pushed", UVM_LOW);
    uvm_sw_ipc_gen_event(1);

    uvm_sw_ipc_wait_event(0);
    `uvm_info(get_type_name(), "received event 0", UVM_LOW);
    i = 0;
    while (i < 2 && uvm_sw_ipc_pull_data(
        0, data_to_uvm
    )) begin
      `uvm_info(get_type_name(), $sformatf("data_to_uvm = 0x%0x", data_to_uvm), UVM_LOW);
      if (data_to_uvm != ref_data_arr[i]) begin
        `uvm_error(get_type_name(), $sformatf("was expecting 0x%x", ref_data_arr[i]))
      end
      i++;
    end
  endtask


  virtual task run_phase(uvm_phase phase);
    // Launch spike_main in background
    fork
      super.run_phase(phase);
    join_none
    basic_test();
  endtask


endclass

`endif  // GUARD_FW_TEST_UVM_SW_IPC_SANITY_SV
