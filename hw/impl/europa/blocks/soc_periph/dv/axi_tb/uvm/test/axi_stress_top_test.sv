`ifndef SOC_PERIPH_AXI_STRESS_TOP_TEST_SV
`define SOC_PERIPH_AXI_STRESS_TOP_TEST_SV

class axi_stress_top_test extends uvm_test;

  `uvm_component_utils(axi_stress_top_test)

  axi_stress_top_env m_env;
  axi_stress_top_config m_config;

  axe_uvm_memory_allocator m_periph_allocators[`NB_PERIPHS];

  extern function new(string name, uvm_component parent);

  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);

endclass : axi_stress_top_test


function axi_stress_top_test::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


function void axi_stress_top_test::build_phase(uvm_phase phase);
  if (!uvm_config_db#(axi_stress_top_config)::get(this, "", "config", m_config))
    `uvm_fatal(get_type_name(), "Unable to get axi_stress_top_config")

  for (int i = 0; i < `NB_PERIPHS; i++) begin
    bit [63:0] start, _end, size;
    start = SOC_PERIPH_ADDRESSES[i][0];
    size  = SOC_PERIPH_ADDRESSES[i][1];
    _end = start + size;
    `uvm_info(get_type_name(), $sformatf("0x%0h, 0x%0h, 0x%0h", size, start, _end), UVM_LOW)
    m_periph_allocators[i] =
        axe_uvm_memory_allocator::type_id::create($sformatf("m_periph_allocators[%0d]", i), this);
    m_periph_allocators[i].base = start;
    m_periph_allocators[i].top = _end;
    m_periph_allocators[i].partition_size = (size / m_config.m_nb_threads_per_periph);

    // We expect to be able to do all kinds of bursts on each partition
    assert (m_periph_allocators[i].partition_size > 16)
    else
      `uvm_fatal(get_type_name(), $sformatf(
                 "[%s] Partition size is too small: %0h bytes",
                 m_periph_allocators[i].get_name(),
                 m_periph_allocators[i].partition_size
                 ))
  end
  m_env = axi_stress_top_env::type_id::create("m_env", this);
endfunction : build_phase

task axi_stress_top_test::run_phase(uvm_phase phase);
  svt_axi_master_sequencer master_sequencer = m_env.m_axi_system_env.master[0].sequencer;
  super.run_phase(phase);
  phase.raise_objection(this);
  wait (m_config.axi_vif.master_if[0].aresetn === 1'b1);
  // Wait for pctl to correctly propagate the reset to the soc_periph
  repeat (50) begin
    @(posedge m_config.axi_vif.common_aclk);
  end
  for (int periph_idx = 0; periph_idx < `NB_PERIPHS; periph_idx++) begin
    automatic
    axi_address_range_stress_seq
    vseq = axi_address_range_stress_seq::type_id::create(
        $sformatf("vseq_%0d", periph_idx)
    );
    vseq.set_item_context(null, master_sequencer);
    vseq.m_transaction_count = m_config.m_transaction_count;
    vseq.m_memory_chunks = m_config.m_nb_threads_per_periph;
    vseq.m_memory_allocator = m_periph_allocators[periph_idx];
    fork
      begin
        vseq.set_starting_phase(phase);
        vseq.start(master_sequencer, null);
      end
    join_none
  end
  wait fork;
  `uvm_info(get_type_name(), "All done!", UVM_LOW)
  phase.drop_objection(this);
endtask

`endif  // SOC_PERIPH_AXI_STRESS_TOP_TEST_SV
