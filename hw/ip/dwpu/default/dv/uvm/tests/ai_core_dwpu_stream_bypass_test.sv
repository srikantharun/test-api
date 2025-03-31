/**
* Same steps and interation as ai_core_dwpu_standard_test
* but send a command to bypass the input data instead of executing the program
*/
class ai_core_dwpu_stream_bypass_test extends ai_core_dwpu_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_stream_bypass_test)

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
      //generate input data streams with random lenghs
      //DWPU should ignore commands and only bypass input stream data to output
      common_rand_cmd_prg_csr(.curr_iter(iter), .instr_min(10), .instr_max(20), .bypass_data_en(1), .bypass_data(1));

      if (iter == max_iter-1)
        common_run(.reset_en(0));
      else
        common_run();

    end
    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass

