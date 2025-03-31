`ifndef AXI_ADDRESS_RANGE_STRESS_SEQ_SV
`define AXI_ADDRESS_RANGE_STRESS_SEQ_SV

class axi_address_range_stress_seq extends uvm_sequence;

  axe_uvm_memory_allocator m_memory_allocator;
  int unsigned m_transaction_count = 1;
  int unsigned m_memory_chunks = 1;

  `uvm_object_utils_begin(axi_address_range_stress_seq)
    `uvm_field_object(m_memory_allocator, UVM_ALL_ON)
    `uvm_field_int(m_transaction_count, UVM_ALL_ON)
    `uvm_field_int(m_memory_chunks, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction

  task body();
    `uvm_info(get_type_name(), "Starting axi_address_range_stress_seq", UVM_LOW)
    for (int chunk_idx = 0; chunk_idx < m_memory_chunks; chunk_idx++) begin
      automatic
      axi_address_chunk_stress_seq
      seq = new(
          $sformatf("%s.seq_chunk[%0d]", this.get_name(), chunk_idx)
      );
      seq.m_range = m_memory_allocator.allocate();
      seq.m_transaction_count = m_transaction_count;
      fork
        begin
          seq.set_item_context(this, m_sequencer);
          seq.set_starting_phase(get_starting_phase());
          seq.start(m_sequencer, this);
        end
      join_none
    end
    wait fork;
    `uvm_info(get_type_name(), "Ending axi_address_range_stress_seq", UVM_LOW)
  endtask
endclass

`endif  // AXI_ADDRESS_RANGE_STRESS_SEQ_SV
