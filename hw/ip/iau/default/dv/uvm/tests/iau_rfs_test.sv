/**
* Same steps and interation as iau_standard_test
* but set rfs = 1 in instructions randomly during program generation
*/
class iau_rfs_test extends iau_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_rfs_test)

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
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_HIGH)
      // Only 1 instr with rfs=1 per command for ICDF compatibility
      common_prog_cfg(.p_smin(2), .p_smax(2), .set_rfs(1));
      prg_seq.start(env.axi_system_env.master[0].sequencer);

      this.cmd = prg_seq.get_cmd();

      if (iter == max_iter - 1)
        common_run(.reset_en(0), .stream_rfs(1), .loop_len(this.cmd.loop_len),
                   .loop_start(this.cmd.loop_start), .loop_iter(this.cmd.loop_iter));
      else
        common_run(.stream_rfs(1), .loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                   .loop_iter(this.cmd.loop_iter));
    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

