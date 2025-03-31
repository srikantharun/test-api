`ifndef SOC_IO_SPIKE_TOP_SCOREBOARD_SV
`define SOC_IO_SPIKE_TOP_SCOREBOARD_SV


`uvm_analysis_imp_decl(_spi_rx)

class spike_top_scoreboard extends uvm_scoreboard;

  uvm_analysis_imp_spi_rx #(svt_spi_transaction, spike_top_scoreboard) analysis_imp_spi_rx;

  `uvm_component_utils(spike_top_scoreboard)

  extern function new(string name, uvm_component parent);

  extern function write_spi_rx(svt_spi_transaction rx);

endclass : spike_top_scoreboard


function spike_top_scoreboard::new(string name, uvm_component parent);
  super.new(name, parent);

  analysis_imp_spi_rx = new("analysis_imp_spi_rx", this);
endfunction : new

function spike_top_scoreboard::write_spi_rx(svt_spi_transaction rx);
  `uvm_info(get_type_name(), $sformatf("Got transaction: %s", rx.sprint()), UVM_LOW)
endfunction

`endif  // SOC_IO_SPIKE_TOP_SCOREBOARD_SV
