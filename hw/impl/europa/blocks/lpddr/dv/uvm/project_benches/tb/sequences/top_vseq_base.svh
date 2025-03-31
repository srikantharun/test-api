//
// File: top_vseq_base.svh
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
class top_vseq_base extends uvm_sequence;
    `uvm_object_utils(top_vseq_base)
    // Handles for each of the target (QVIP) sequencers
    
    mvc_sequencer apb_master_0_sqr;
    mvc_sequencer apb_master_1_sqr;
    mvc_sequencer axi4_master_0_sqr;
    virtual subsystem_signal_intf top_signals_intf;

    function new
    (
        string name = "top_vseq_base"
    );
        super.new(name);
        if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"apb_master_0", apb_master_0_sqr) )
        begin
            `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'apb_master_0'" )
        end
	if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"apb_master_1", apb_master_1_sqr) )
        begin
            `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'apb_master_1'" )
        end
        if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"axi4_master_0", axi4_master_0_sqr) )
        begin
            `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'axi4_master_0'" )
        end
	if ( !uvm_config_db#(virtual subsystem_signal_intf)::get(null,"","subsystem_signals",top_signals_intf))begin
            `uvm_error("Config Error" , "uvm_config_db #( subsystem_signal_intf )::get cannot find resource 'subsystem_signals'" )
	end

    endfunction
    
    extern task body;
    
endclass: top_vseq_base

task top_vseq_base::body;
endtask: body

