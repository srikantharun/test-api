// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Env, it contains the agents for all the token managers
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
`ifndef GUARD_TKN_MNG_ENV_SV
`define GUARD_TKN_MNG_ENV_SV

class tkn_mng_env extends uvm_env;
    `uvm_component_utils(tkn_mng_env)

    tkn_mng_aic_agent_pkg::tkn_mng_aic_agent aic_agent;


    /** Class Constructor */
    function new (string name="tkn_mng_env", uvm_component parent=null);
        super.new (name, parent);
    endfunction

    /** Build the APB System ENV */
    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        // the if is passed by the hdt top, this might be fixed becase of reusing
        aic_agent = tkn_mng_aic_agent_pkg::tkn_mng_aic_agent::type_id::create("aic_agent", this);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)

    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info("connect_phase", "Entered...",UVM_LOW)
    endfunction:connect_phase

    virtual task configure_phase(uvm_phase phase);
        `uvm_info("configure_phase", "Entered...",UVM_LOW)

        super.configure_phase(phase);

        `uvm_info("configure_phase", "Exiting...",UVM_LOW)
    endtask

    task reset_phase(uvm_phase phase);
        phase.raise_objection(this,"Restting regmodel");
        phase.drop_objection(this);
    endtask

endclass

`endif  // GUARD_TKN_MNG_ENV_SV
