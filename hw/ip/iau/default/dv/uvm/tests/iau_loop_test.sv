/**
* Same steps and interation as iau_standard_test
* but set a random value for loop_interation
*/
class iau_loop_test extends iau_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_loop_test)

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
      //random iteration between [30:200] with len = 1
      if (iter == max_iter && $urandom_range(0,2) == 1) begin
        common_prog_cfg(.p_smin(1), .p_smax(1), .p_iter_en(1), .p_imin(30), .p_imax(200),.single_stream(1));
      end
      else
        common_prog_cfg(.p_smin(8), .p_smax(120), .p_iter_en(1), .p_imin(30), .p_imax(200),.single_stream(1));
      prg_seq.start(env.axi_system_env.master[0].sequencer);

      this.cmd = prg_seq.get_cmd();

      if (iter == max_iter - 1)
        common_run(.reset_en(0), .loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                   .loop_iter(this.cmd.loop_iter));
      else
        common_run(.loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                   .loop_iter(this.cmd.loop_iter));
    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

