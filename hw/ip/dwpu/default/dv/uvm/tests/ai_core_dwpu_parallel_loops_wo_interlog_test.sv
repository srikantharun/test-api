class ai_core_dwpu_parallel_loops_wo_interlog_sequence extends ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb;

  constraint c_wo_interlog {
    nested_1.start == nested_0.start + nested_0.length;
  }

  `uvm_object_utils(ai_core_dwpu_parallel_loops_wo_interlog_sequence)

  function new(string name = "ai_core_dwpu_parallel_loops_wo_interlog_sequence");
    super.new(name);
  endfunction

endclass : ai_core_dwpu_parallel_loops_wo_interlog_sequence
/**
* Same steps and interation as ai_core_dwpu_standard_test
* but set a random value for loop_interation
*/
class ai_core_dwpu_parallel_loops_wo_interlog_test extends ai_core_dwpu_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_parallel_loops_wo_interlog_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    /** Factory override of the master transaction object */
    set_type_override_by_type (ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::get_type(), ai_core_dwpu_parallel_loops_wo_interlog_sequence::get_type());
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_HIGH)
      common_rand_cmd_prg_csr(.curr_iter(iter), .instr_min(10), .instr_max(20), .iter_en(1), .iter_min(2), .iter_max(3), .innerloop_type(2), .all_loops_en(1)); //call this function with parallel loop option

      if (iter == max_iter-1)
        common_run(.reset_en(0));
      else
        common_run();
    end
    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_parallel_loops_wo_interlog_test

