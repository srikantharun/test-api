
// Test to write/read, to/from one register for every CSR block of LS
class ai_core_mvm_ral_single_wrrd_test extends ai_core_mvm_ral_base_test;

  `uvm_component_utils (ai_core_mvm_ral_single_wrrd_test);
  // Reset sequence
  axi_simple_reset_sequence axi_reset_seq;

  // Single write/read sequence
  ral_access_single_write_read_seq wrrd_seq;

  function new (string name="ai_core_mvm_ral_single_wrrd_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_HIGH)
    super.build_phase(phase);

    // Create simple reset sequence
    axi_reset_seq = axi_simple_reset_sequence::type_id::create("axi_reset_seq");

    // Create the sequence class
    wrrd_seq = ral_access_single_write_read_seq::type_id::create("ral_access_single_write_read_seq",,get_full_name());

    `uvm_info("ai_core_mvm_ral_single_wrrd_test", "Exiting...", UVM_HIGH)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);

    phase.raise_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_HIGH)

    // Start reset sequence on the sequencer
    axi_reset_seq.start(env.sequencer);

    wrrd_seq.start(env.sequencer);

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_HIGH)
  endtask : run_phase

  virtual function void report_phase(uvm_phase phase);
    `uvm_info("report_phase", "Entering... printing AXI VIP slave memory", UVM_HIGH);
    `uvm_info("report_phase", "Exiting...", UVM_HIGH);
  endfunction : report_phase

endclass:ai_core_mvm_ral_single_wrrd_test
