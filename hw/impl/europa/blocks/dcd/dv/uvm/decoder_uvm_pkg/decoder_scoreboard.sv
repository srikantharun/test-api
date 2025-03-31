

function decoder_scoreboard::new(string name="decoder_scoreboard", uvm_component parent=null);
  super.new(name, parent);
endfunction: new

function void decoder_scoreboard::build_phase (uvm_phase phase);
  super.build_phase(phase);

  decoder_mcu_axi_export      = new("decoder_mcu_axi_export", this);
  decoder_core0_axi_export    = new("decoder_core0_axi_export", this);
  decoder_core1_axi_export    = new("decoder_core1_axi_export", this);
  decoder_postproc_axi_export = new("decoder_postproc_axi_export", this);
  decoder_apb_export          = new("decoder_apb_export", this);
endfunction: build_phase

function void decoder_scoreboard::print_axi_transaction(string id, svt_axi_transaction trans);
  string data_str;
  data_str=$sformatf("%h", trans.data[0][CODEC_AXI_DATA_WIDTH-1:0]);
  if (trans.data.size() > 1) begin
    for (int i = 1; i < trans.data.size(); i++) begin
      data_str=$sformatf("%h_%s", trans.data[i][CODEC_AXI_DATA_WIDTH-1:0], data_str);
    end
  end
  `uvm_info(id, $sformatf("AXI %0s started at %t (length=%0d, type=%0s, size=%0s): @0x%h(%0s) -> 0x%s(%0s) ",
    trans.xact_type.name(),
    trans.addr_valid_assertion_time,
    trans.burst_length,
    trans.burst_type.name(),
    trans.burst_size.name(),
    trans.addr,
    trans.addr_status.name(),
    data_str,
    trans.data_status.name()
    ), UVM_MEDIUM)
endfunction: print_axi_transaction

function void decoder_scoreboard::write_decoder_mcu_axi(svt_axi_transaction trans);
  print_axi_transaction("DECODER_AXI_MCU", trans);
endfunction: write_decoder_mcu_axi

function void decoder_scoreboard::write_decoder_core0_axi(svt_axi_transaction trans);
  print_axi_transaction("DECODER_AXI_CORE0", trans);
endfunction: write_decoder_core0_axi

function void decoder_scoreboard::write_decoder_core1_axi(svt_axi_transaction trans);
  print_axi_transaction("DECODER_AXI_CORE1", trans);
endfunction: write_decoder_core1_axi

function void decoder_scoreboard::write_decoder_postproc_axi(svt_axi_transaction trans);
  print_axi_transaction("DECODER_AXI_POSTPROC", trans);
endfunction: write_decoder_postproc_axi

function void decoder_scoreboard::write_decoder_apb(svt_apb_transaction trans);
  `uvm_info("DECODER_APB", $sformatf("APB %0s: @0x%h -> 0x%h (pstrb=0x%h)", trans.xact_type.name(), trans.address, trans.data, trans.pstrb), UVM_MEDIUM)
endfunction: write_decoder_apb
