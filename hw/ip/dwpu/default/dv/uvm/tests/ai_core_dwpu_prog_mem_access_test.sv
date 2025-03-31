// AI Core DWPU AXI random test-case class
class ai_core_dwpu_prog_mem_access_test extends ai_core_dwpu_base_test;

  // Registration with the factory
  `uvm_component_utils(ai_core_dwpu_prog_mem_access_test)

  ai_core_dwpu_initialize_prog_sequence   init_prog_seq;
  axi_prog_random_sequence                prog_rnd_seq;
  ai_core_dwpu_csr_config_sequence        csr_cfg_seq;
  ai_core_dwpu_small_random_prog_sequence small_rnd_prg;
  // Class Constructor
  function new(string name = "ai_core_dwpu_prog_mem_access_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    init_prog_seq= ai_core_dwpu_initialize_prog_sequence::type_id::create("init_prog_seq");
    prog_rnd_seq= axi_prog_random_sequence::type_id::create("prog_rnd_seq");
    csr_cfg_seq = ai_core_dwpu_csr_config_sequence::type_id::create("csr_cfg_seq", this);
    small_rnd_prg = ai_core_dwpu_small_random_prog_sequence::type_id::create("small_rnd_prg", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase
  // Run phase
  virtual task run_phase(uvm_phase phase);

    phase.raise_objection(this);
    //start csr configuration
    if(!csr_cfg_seq.randomize()) `uvm_error(get_name, "csr_cfg_seq randomization error!");
    csr_cfg_seq.start(env.sequencer);

    //start initialization program memory sequence
    init_prog_seq.start(env.sequencer);
    //start axi random program access sequence
    if(!prog_rnd_seq.randomize() with {
      sequence_length== 1000;
    }) `uvm_error(get_name, "prog_rnd_seq randomization error!");
    prog_rnd_seq.start(env.m_axi_system_env.master[0].sequencer);
    
    //start small random program access sequence
    if(!small_rnd_prg.randomize() with {
      sequence_length== 100;
    }) `uvm_error(get_name, "small_rnd_prgrandomization error!");
    small_rnd_prg.start(env.sequencer);

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)
  endtask
  
  function void change_axi_cfg();
    cfg.master_cfg[0].default_bready = 0;
    `uvm_info(get_type_name(), $sformatf("default_bready was changed to 0"), UVM_LOW)
  endfunction : change_axi_cfg

endclass : ai_core_dwpu_prog_mem_access_test
