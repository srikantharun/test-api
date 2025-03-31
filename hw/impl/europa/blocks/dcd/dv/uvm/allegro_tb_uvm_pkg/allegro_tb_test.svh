

class allegro_tb_test extends uvm_test;
  `uvm_component_utils(allegro_tb_test)

  decoder_env m_decoder_env;
  allegro_tb_demoter m_demoter;

  function new(string name="allegro_tb_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction: new

  function void build_phase(uvm_phase phase);
    if (!$test$plusargs("disable_decoder_scoreboard")) begin
      m_decoder_env = decoder_env::type_id::create("m_decoder_env", this);
      m_demoter = allegro_tb_demoter::type_id::create("m_demoter", this);
      uvm_report_cb::add(null, m_demoter);
    end
  endfunction: build_phase

  task run_phase(uvm_phase phase);
    uvm_event finish_ev;
    phase.raise_objection(this);
    phase.phase_done.set_drain_time(this, 5);
    finish_ev = uvm_event_pool::get_global("finish_ev");
    finish_ev.wait_trigger;
    `uvm_info("TEST", "Finish event received", UVM_NONE);
    phase.drop_objection(this);
  endtask : run_phase

endclass: allegro_tb_test
