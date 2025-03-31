/**
 * Abstract:
 * class 'sys_spm_env' is extended from uvm_env base class.  It implements
 * the build phase to construct the structural elements of this environment.
 *
 * sys_spm_env is the testbench environment, which constructs two APB System
 * ENVs in the build_phase method using the UVM factory service.  The APB System
 * ENV  is the top level component provided by the APB VIP. The APB System ENV
 * in turn, instantiates constructs the APB Master and Slave agents.
 *
 * spm_basic env also constructs the virtual sequencer. This virtual sequencer
 * in the testbench environment obtains a handle to the reset interface using
 * the config db.  This allows reset sequences to be written for this virtual
 * sequencer.
 *
 * The simulation ends after all the objections are dropped.  This is done by
 * using objections provided by phase arguments.
 */
`ifndef GUARD_SYS_SPM_ENV_SV
`define GUARD_SYS_SPM_ENV_SV

class sys_spm_env extends uvm_env;
    `uvm_component_utils(sys_spm_env)

    spm_uvm_pkg::spm_env                        spm_ip_env;

    svt_apb_system_env                          sys_spm_apb_env;

    cust_sys_spm_svt_apb_system_configuration   apb_cfg;
    
    apb_virtual_sequencer apb_sequencer;

    function new (string name="sys_spm_env", uvm_component parent=null);
        super.new (name, parent);
    endfunction


    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);


        spm_ip_env = spm_uvm_pkg::spm_env::type_id::create("spm_ip_env", this);

        /** Construct the virtual sequencer */
        apb_sequencer = apb_virtual_sequencer::type_id::create("apb_sequencer", this);

        if (uvm_config_db#(cust_sys_spm_svt_apb_system_configuration)::get(this, "", "apb_cfg", apb_cfg)) begin
            /** Apply the configuration to the System ENV */
            uvm_config_db#(svt_apb_system_configuration)::set(this, "sys_spm_apb_env", "apb_cfg", apb_cfg);
        end
        // No configuration passed from test
        else begin
            apb_cfg = cust_sys_spm_svt_apb_system_configuration::type_id::create("apb_cfg");
            uvm_config_db#(svt_apb_system_configuration)::set(this, "sys_spm_apb_env", "apb_cfg", apb_cfg);
        end

        `uvm_info("build_phase", "Exiting...", UVM_LOW)

    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info("connect_phase", "Entered...",UVM_LOW)


    endfunction:connect_phase

    task reset_phase(uvm_phase phase);
        phase.raise_objection(this,"Restting regmodel");
        phase.drop_objection(this);
    endtask

endclass

`endif  // GUARD_SYS_SPM_ENV_SV
