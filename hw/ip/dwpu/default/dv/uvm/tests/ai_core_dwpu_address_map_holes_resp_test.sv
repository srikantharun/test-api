// AI Core DWPU test to verify the holes in register map
class ai_core_dwpu_address_map_holes_resp_test extends ai_core_dwpu_base_test;

  // Registration with the factory
  `uvm_component_utils (ai_core_dwpu_address_map_holes_resp_test)
  // Reset sequence
  axi_simple_reset_sequence axi_reset_seq;
  ai_core_dwpu_not_addressable_csr_sequence   not_addressable_csr_seq;
  ai_core_dwpu_not_addressable_prog_sequence  not_addressable_prog_seq;
  ai_core_dwpu_csr_config_sequence            csr_cfg_seq;
  // Register list
  uvm_reg reg_list[$];

  // Class Constructor
  function new (string name="ai_core_dwpu_address_map_holes_resp_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    // Create simple reset sequence
    axi_reset_seq = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    not_addressable_csr_seq= ai_core_dwpu_not_addressable_csr_sequence::type_id::create("not_addressable_csr_seq");
    not_addressable_prog_seq= ai_core_dwpu_not_addressable_prog_sequence::type_id::create("not_addressable_prog_seq");
    csr_cfg_seq= ai_core_dwpu_csr_config_sequence::type_id::create("csr_cfg_seq");
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    // Variables declaration
    uvm_status_e status;
    uvm_status_e expected_status;
    uvm_reg_addr_t avail_address_list[$];
    uvm_reg_addr_t not_avail_address_list[$];
    uvm_reg_addr_t init_burst_address;
    int success;

    phase.raise_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)

    // Print RAL model registers information
    regmodel.print();

    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)
    // Start reset sequence on the sequencer
    if(!axi_reset_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
    axi_reset_seq.start(env.sequencer);

    //start not addressable csr sequence
    not_addressable_csr_seq.start(env.sequencer);
    //start not addressable program sequence
    not_addressable_prog_seq.start(env.sequencer);
    //start a sequence that will receive an OKAY response. This is necessary for coverage purpose of transition from ERROR to OKAY
    csr_cfg_seq.start(env.sequencer);

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)
  endtask
endclass
