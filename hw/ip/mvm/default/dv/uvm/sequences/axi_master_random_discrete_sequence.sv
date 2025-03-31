
/**
 * Abstract:
 * class axi_master_random_discrete_sequence defines a sequence that generates a
 * random discrete master transaction.  This sequence is used by the
 * axi_master_random_discrete_virtual_sequence which is set up as the default
 * sequence for this environment.
 *
 * Execution phase: main_phase
 * Sequencer: Virtual sequencer in AXI System ENV
 */

`ifndef GUARD_AXI_MASTER_RANDOM_DISCRETE_SEQUENCE_SV
`define GUARD_AXI_MASTER_RANDOM_DISCRETE_SEQUENCE_SV

//------------------------------------------------------------------------------
//
// CLASS: axi_master_random_discrete_sequence 
//
//------------------------------------------------------------------------------

class axi_master_random_discrete_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 10;

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_random_discrete_sequence)

  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}

  // Declare start and end address variables
  rand bit [31:0] start_addr;
  rand bit [31:0] end_addr;
  rand bit [31:0] addr;
  

  /** Class Constructor */
  function new(string name = "axi_master_random_discrete_sequence");
    super.new(name);
  endfunction : new

  // Method to set the address range
  function void set_address_range(bit [31:0] start_addr, bit [31:0] end_addr);
    this.start_addr = start_addr;
    this.end_addr = end_addr;
  endfunction

  // Constraints to restrict address range
  constraint addr_range_c {
    addr >= start_addr;
    addr <= end_addr;
  }
  

  /*
  virtual task body();
    bit status;

    `uvm_info("body", "Entered ...", UVM_HIGH)

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
    `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_HIGH);

    for(int i = 0; i < sequence_length; i++) begin
      `uvm_info("body", $sformatf("Calling `uvm_do, iteration=%0d", i), UVM_HIGH)
      `uvm_do(req)
    end

    `uvm_info("body", "Exiting...", UVM_HIGH)
  endtask: body
*/
  // Body task
  virtual task body();
    svt_axi_master_transaction master_transaction;
    svt_configuration get_cfg;
    bit status;
    `uvm_info("body", "Entered ...", UVM_HIGH)

    super.body();

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length",
                                               sequence_length);
    `uvm_info("body", $sformatf(
              "sequence_length is %0d as a result of %0s.",
              sequence_length,
              status ? "config DB" : "randomization"
              ), UVM_HIGH);

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    for (int i = 0; i < sequence_length; i++) begin
      `uvm_info("body", $sformatf("Calling `uvm_do, iteration=%0d", i), UVM_HIGH)
      
      if (!this.randomize(addr)) begin
        `uvm_fatal("RANDOMIZATION FAILED", "Randomization of address failed")
      end

      // Create and execute a transaction with the randomized address
      master_transaction = svt_axi_master_transaction::type_id::create("master_transaction");
      master_transaction.addr = addr;
      // Set other transaction parameters as needed
      `uvm_do(master_transaction);
    end        `uvm_info("body", "Exiting...", UVM_HIGH)
  endtask : body
endclass : axi_master_random_discrete_sequence

`endif  // GUARD_AXI_MASTER_RANDOM_DISCRETE_SEQUENCE_SV
