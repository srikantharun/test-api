`ifndef SOC_MGMT_SCOREBOARD_SV
`define SOC_MGMT_SCOREBOARD_SV
`uvm_analysis_imp_decl(_actual_data)
`uvm_analysis_imp_decl(_expected_data)

class soc_mgmt_scoreboard extends uvm_scoreboard;

  /** Analysis port connected to the AXI IAU SLAVE Agent */
  uvm_analysis_imp_actual_data#(svt_axi_transaction, soc_mgmt_scoreboard) actual_data_export;

  /** Analysis port conneted to the ref model */
  uvm_analysis_imp_expected_data#(svt_axi_transaction, soc_mgmt_scoreboard) expected_data_export;
  
  /** UVM Component Utility macro */
  `uvm_component_utils(soc_mgmt_scoreboard)
  
  // soc_mgmt user Inteface Handle
  virtual soc_mgmt_if soc_mgmt_if;
  
  function new(string name = "soc_mgmt_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    /** Construct the analysis ports */
    actual_data_export = new("actual_data_export", this);
    expected_data_export  = new("expected_data_export", this);

  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build();
    // Recieve soc_mgmt user interface handle
    uvm_config_db#(virtual soc_mgmt_if)::get(uvm_root::get(), "uvm_test_top", "soc_mgmt_if", soc_mgmt_if);
  endfunction

  virtual function void write_actual_data(input svt_axi_transaction xact);
  endfunction : write_actual_data

  virtual function void write_expected_data(input svt_axi_transaction xact);
  endfunction : write_expected_data



  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask : run_phase
  

  function void check_phase(uvm_phase phase);
  endfunction
endclass  
`endif

