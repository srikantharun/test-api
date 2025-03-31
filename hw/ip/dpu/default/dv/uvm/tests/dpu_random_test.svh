`ifndef DPU_RANDOM_TEST_SVH 
`define DPU_RANDOM_TEST_SVH

class dpu_random_test extends dpu_base_test;
  `uvm_component_utils(dpu_random_test)

  function new(string name = "dpu_random_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);

    axi_reset_seq.start(env.sequencer);

    init_regs();
    //TODO: increase iteration when test is passing
    repeat (1) begin
      dpu_csr_config_seq.irq_en_reg = 0;
      dpu_csr_config_seq.randomize();
      dpu_csr_config_seq.start(env.sequencer);

      cfg_cmd_desc(.ll_max(5), .i_max(5), .li_max(1), .loop_only(0));

      cfg_program_and_start();

      cfg_streams();

      wait_cycles($urandom_range(10,20));
      if ($urandom_range(0,4) == 2) 
        axi_reset_seq.start(env.sequencer);
    end
    phase.drop_objection(this);

  endtask

endclass

`endif

