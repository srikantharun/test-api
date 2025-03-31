`ifndef RVV_SEQUENCER_SV
`define RVV_SEQUENCER_SV

class rvv_sequencer#(int DATA_WIDTH = 128, int ADDR_WIDTH = 22) extends uvm_sequencer#(rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH));
  `uvm_component_param_utils(rvv_sequencer#(DATA_WIDTH, ADDR_WIDTH))

  rvv_config                                m_rvv_cfg;
  // Virtual interface array
  virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH)  m_mmio_vif[];

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if ( ! uvm_config_db#( rvv_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_rvv_cfg" ), .value( m_rvv_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
    m_mmio_vif = new[m_rvv_cfg.connections_num];
  endfunction

endclass : rvv_sequencer

`endif // RVV_SEQUENCER_SV

