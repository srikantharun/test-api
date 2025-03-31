
`uvm_analysis_imp_decl(_decoder_mcu_axi)
`uvm_analysis_imp_decl(_decoder_core0_axi)
`uvm_analysis_imp_decl(_decoder_core1_axi)
`uvm_analysis_imp_decl(_decoder_postproc_axi)
`uvm_analysis_imp_decl(_decoder_apb)

class decoder_scoreboard extends uvm_scoreboard;
   
  `uvm_component_utils(decoder_scoreboard)

  uvm_analysis_imp_decoder_mcu_axi#(svt_axi_transaction, decoder_scoreboard)      decoder_mcu_axi_export;
  uvm_analysis_imp_decoder_core0_axi#(svt_axi_transaction, decoder_scoreboard)    decoder_core0_axi_export;
  uvm_analysis_imp_decoder_core1_axi#(svt_axi_transaction, decoder_scoreboard)    decoder_core1_axi_export;
  uvm_analysis_imp_decoder_postproc_axi#(svt_axi_transaction, decoder_scoreboard) decoder_postproc_axi_export;
  uvm_analysis_imp_decoder_apb#(svt_apb_transaction, decoder_scoreboard)          decoder_apb_export;

  extern function new(string name="decoder_scoreboard", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern function void print_axi_transaction(string id, svt_axi_transaction trans);
  extern virtual function void write_decoder_mcu_axi(svt_axi_transaction trans);
  extern virtual function void write_decoder_core0_axi(svt_axi_transaction trans);
  extern virtual function void write_decoder_core1_axi(svt_axi_transaction trans);
  extern virtual function void write_decoder_postproc_axi(svt_axi_transaction trans);
  extern virtual function void write_decoder_apb(svt_apb_transaction trans);

endclass: decoder_scoreboard
