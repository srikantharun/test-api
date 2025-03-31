/**
* Same steps and interation as ai_core_dwpu_standard_test
* but set all_loop_en equal to 1 to make sure all loops are created
*/
class ai_core_dwpu_loop_test extends ai_core_dwpu_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_loop_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_HIGH)
      common_rand_cmd_prg_csr(.curr_iter(iter), .instr_min(10), .instr_max(20), .iter_en(1), .iter_min(2), .iter_max(10), .all_loops_en(1));
      
      if (iter == max_iter-1)
        common_run(.reset_en(0));
      else
        common_run();
    end
    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

