//The uvm_analysis_imp_decl allows for a scoreboard (or other analysis component) to
// support input from many places
/** Macro that define two analysis ports with unique suffixes */
`uvm_analysis_imp_decl(_initiated)
`uvm_analysis_imp_decl(_response)

class axi_uvm_scoreboard extends uvm_scoreboard;

  /** Analysis port connected to the AXI Master Agent */
  uvm_analysis_imp_initiated#(svt_axi_transaction, axi_uvm_scoreboard) item_observed_initiated_export;

  /** Analysis port conneted to the AXI Slave Agent */
  uvm_analysis_imp_response#(svt_axi_transaction, axi_uvm_scoreboard) item_observed_response_export;

  /** UVM Component Utility macro */
  `uvm_component_utils(axi_uvm_scoreboard)
  
  function new (string name = "axi_uvm_scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build();
    /** Construct the analysis ports */
    item_observed_initiated_export = new("item_observed_initiated_export", this);
    item_observed_response_export  = new("item_observed_response_export", this);
  endfunction

  /** This method is called by item_observed_initiated_export */
  virtual function void write_initiated(input svt_axi_transaction xact);
    svt_axi_transaction init_xact;
    if (!$cast(init_xact, xact.clone())) begin
      `uvm_fatal("Write_initiated", "Unable to $cast the received transaction to svt_axi_transaction");
    end
      `uvm_info("Write_initiated", $sformatf("xact:\n%s", init_xact.sprint()), UVM_HIGH)
  endfunction:write_initiated

  /** This method is called by item_observed_response_export */
  virtual function void write_response(input svt_axi_transaction xact);

  svt_axi_transaction resp_xact;
  if (!$cast(resp_xact, xact.clone())) begin
    `uvm_fatal("Write_response", "Unable to $cast the received transaction to svt_axi_transaction");
  end
  begin
    `uvm_info("Write_response", $sformatf("xact:\n%s", resp_xact.sprint()), UVM_HIGH)
    `uvm_info("L2SCOREBOARD", $sformatf("AXI_ADDR = %h", resp_xact.addr), UVM_HIGH)
    for (int ii = 0; ii < 15; ii++)
      `uvm_info("L2SCOREBOARD", $sformatf("AXI_DATA[%d] = %h", ii, resp_xact.data[ii]), UVM_HIGH)
  end
  endfunction:write_response

  task run_phase(uvm_phase phase);
   
    super.run_phase(phase);
    // Get L2 operating parameters
      endtask:run_phase

endclass // axi_uvm_scoreboard


