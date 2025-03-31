`ifndef DPU_MEM_ACCESS_TEST_SVH
`define DPU_MEM_ACCESS_TEST_SVH

class dpu_memory_access_out_of_range_test extends dpu_base_test;
  // Registration with the factory
  `uvm_component_utils(dpu_memory_access_out_of_range_test)
  
  ai_core_dpu_axi_simple_reset_sequence 		axi_reset_seq;
  dpu_memory_access_out_of_range_sequence		dpu_memory_access_out_of_range_seq;
  
  // Class Constructor
  function new(string name="dpu_memory_access_out_of_range_test", uvm_component parent=null);
    super.new (name, parent);
    axi_reset_seq 		= ai_core_dpu_axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    dpu_memory_access_out_of_range_seq 	= dpu_memory_access_out_of_range_sequence::type_id::create("dpu_memory_access_out_of_range_seq");
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    int num_of_iter;
    phase.raise_objection(this);
    num_of_iter = $urandom_range(500,1000);
    axi_reset_seq.start(env.sequencer);
    `uvm_info(get_type_name(), $sformatf("Run phase started, num of iter %d, raising objection", num_of_iter), UVM_LOW)
    repeat(num_of_iter) begin
      dpu_memory_access_out_of_range_seq.randomize();
      dpu_memory_access_out_of_range_seq.start(env.sequencer);
    end

    phase.drop_objection(this);

  endtask

endclass

`endif
