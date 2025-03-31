/**
* Same steps and interation as iau_standard_test
* but send a command to bypass the input data instead of executing the program
*/
class iau_stream_bypass_test extends iau_standard_test;

  rand bit rand_cmd_bypass_cfg;
  /** UVM Component Utility macro */
  `uvm_component_utils(iau_stream_bypass_test)

  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout
    max_iter = 8;
    for (int iter = 1; iter <= max_iter; iter++) begin
      if(!this.randomize(rand_cmd_bypass_cfg) with {
        rand_cmd_bypass_cfg dist {
          1 := 5,
          0 := 2
        };
      }) `uvm_fatal(get_name, "Randomization Failed!")

      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_HIGH)
      //generate input data streams with random lenghs
      common_prog_cfg(.p_smin(10), .p_smax(20), .bypass_cmd(rand_cmd_bypass_cfg));
      //IAU should ignore commands and only bypass input stream data to output
      prg_seq.start(env.axi_system_env.master[0].sequencer);

      this.cmd = prg_seq.get_cmd();

      if (iter == max_iter - 1)
        common_run(.reset_en(0), .stream_bypass(rand_cmd_bypass_cfg), .loop_len(this.cmd.loop_len),
                   .loop_start(this.cmd.loop_start), .loop_iter(this.cmd.loop_iter));
      else
        common_run(.stream_bypass(rand_cmd_bypass_cfg), .loop_len(this.cmd.loop_len),
                   .loop_start(this.cmd.loop_start), .loop_iter(this.cmd.loop_iter));

    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

