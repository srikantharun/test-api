/** Token sequence that make sure that delay of token interface is huge enough
* to create the scenario of having tvalid = 1 and tready = 0 on dwpu command fifo.
*/
class token_agent_huge_delay_seq_item extends token_agent_seq_item;

  constraint c_huge_delay {
    m_bv_delay inside {[100:1000]};
  }
  constraint c_huge_delay_dist {
    m_bv_delay dist {
      [100:700] :/ 10,
      [700:1000] :/ 90
    };
  }

  `uvm_object_utils(token_agent_huge_delay_seq_item)

  function new(string name = "token_agent_huge_delay_seq_item");
    super.new(name);
    `uvm_info ("run_phase", $sformatf("New from token_agent_huge_delay_seq_item"), UVM_HIGH)

  endfunction

endclass : token_agent_huge_delay_seq_item


/**
* Generate multiple commands to fill cmdblk`s cmd FIFO
*/
class iau_cmdblk_backpressure_test extends iau_standard_test;
  /** UVM Component Utility macro */
  `uvm_component_utils (iau_cmdblk_backpressure_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)

    /** Factory override of the master transaction object */
    set_type_override_by_type (token_agent_seq_item::get_type(), token_agent_huge_delay_seq_item::get_type());

    super.build_phase(phase);
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout
    max_iter = 1;
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_HIGH)
      common_prog_cfg(.p_smax(100));
      prg_seq.start(env.axi_system_env.master[0].sequencer);
      this.cmd = prg_seq.get_cmd();

      //if (iter == max_iter-1)
      common_run(.reset_en(0), .loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                 .loop_iter(this.cmd.loop_iter), .multiple_cmds_cnt(28));
      //else
      //  common_run(.loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start), .loop_iter(this.cmd.loop_iter), .tokens_en(1));
    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : iau_cmdblk_backpressure_test

