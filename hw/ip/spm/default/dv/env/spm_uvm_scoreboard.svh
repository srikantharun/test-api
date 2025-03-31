`ifndef SPM_UVM_SCOREBOARD_SV
`define SPM_UVM_SCOREBOARD_SV

//The uvm_analysis_imp_decl allows for a scoreboard (or other analysis component) to
// support input from many places
/** Macro that define two analysis ports with unique suffixes */
class spm_uvm_scoreboard extends uvm_scoreboard;

  uvm_object obj; 
 
    /** Analysis port connected to the AHB Master Agent */
    uvm_analysis_imp#(svt_axi_transaction, spm_uvm_scoreboard) trans_data_import;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_uvm_scoreboard)

    svt_axi_transaction exp_xact[$];



    function new (string name = "spm_uvm_scoreboard", uvm_component parent=null);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build();
        /** Construct the analysis ports */
        trans_data_import = new("trans_data_import", this);

    endfunction

    /** This method is called by item_observed_initiated_export */
    virtual function void write(input svt_axi_transaction received_item);

        svt_axi_transaction item;
        if (!$cast(item, received_item.clone())) begin
        `uvm_fatal(get_full_name(), "Unable to $cast the received transaction to svt_axi_transaction");
        end


    endfunction:write


endclass // spm_uvm_scoreboard

`endif

