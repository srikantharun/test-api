// emmc_test:
//
// This UVM test doesn't do anything: it is just here for compatibility with its soc_periph
// counterpart
`ifndef EMMC_TEST_SV
`define EMMC_TEST_SV

class emmc_test extends fw_base_test;

  `uvm_component_utils(emmc_test)

  extern function new(string name, uvm_component parent);

  extern task run_phase(uvm_phase phase);
endclass : emmc_test


function emmc_test::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


task emmc_test::run_phase(uvm_phase phase);
  super.run_phase(phase);
endtask : run_phase

`endif  // EMMC_TEST_SV
