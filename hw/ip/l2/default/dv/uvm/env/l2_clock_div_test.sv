/** Test case to stimuli the clock divider clear and enable.
*/
class l2_clock_div_test extends l2_all_bank_all_ram_addr_check_test;

  // Registration with the factory
  `uvm_component_utils (l2_clock_div_test)

  cc_clk_div_agent_base_sequence incr_clk_div_seq;
  cc_clk_div_agent_base_sequence enable_disable_clk_div_seq;
  cc_clk_div_agent_clear_sequence clear_clk_div_seq;

  // Class Constructor
  function new (string name="l2_clock_div_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  virtual task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info(get_type_name(), $sformatf("Main phase started, raising objection"), UVM_LOW)
    incr_clk_div_seq = cc_clk_div_agent_base_sequence::type_id::create($sformatf("incr_clk_div_seq"));
    enable_disable_clk_div_seq= cc_clk_div_agent_base_sequence::type_id::create($sformatf("enable_disable_clk_div_seq"));
    clear_clk_div_seq = cc_clk_div_agent_clear_sequence::type_id::create($sformatf("clear_clk_div_seq"));

    #200ns;
    
    //Disable the clock divider
    `uvm_info(get_type_name(), $sformatf("Disabling clock divider"), UVM_LOW)
    if(!enable_disable_clk_div_seq.randomize() with {
      m_enable == 0;
    }) `uvm_error(get_name, "enable_disable_clk_div_seq randomization error!");
    enable_disable_clk_div_seq.start(env.m_clk_div_agt.m_seqr);

    //give some time to start changing the increment values and the clear
    #100ns;

    for(int i= 0; i<60; i++) begin
      //change the clock divider increment and by default the base sequence has the m_enable variable equal to 1
      if(!incr_clk_div_seq.randomize() with {
        m_incr inside {[0 : $]};
      }) `uvm_error(get_name, "incr_clk_div_seq randomization error!");
      incr_clk_div_seq.start(env.m_clk_div_agt.m_seqr);
      //clear the clock divider
      if(!clear_clk_div_seq.randomize() with {
        m_incr == incr_clk_div_seq.m_incr;
      }) `uvm_error(get_name, "clear_clk_div_seq randomization error!");
      clear_clk_div_seq.start(env.m_clk_div_agt.m_seqr);
      //give some time in between changes to make sure they took place. The changes on the inputs have a propagation time to the clock divided
      #100ns;
    end
    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Main phase finished, dropping objection"), UVM_LOW)
  endtask

endclass
