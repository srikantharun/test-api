/**
 * Abstract:
 * class 'spm_env' is extended from uvm_env base class.  It implements
 * the build phase to construct the structural elements of this environment.
 *
 * spm_env is the testbench environment, which constructs two APB System
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
`ifndef GUARD_SPM_ENV_SV
`define GUARD_SPM_ENV_SV

class spm_env extends uvm_env;
    `uvm_component_utils(spm_env)

    /** AXI System ENV */
    svt_axi_system_env m_axi_system_env;

    /** Virtual Sequencer */
    axi_virtual_sequencer axi_sequencer;

    /** AXI System Configuration */
    cust_svt_axi_system_configuration cfg;

    // ecc and irq monitor
    spm_uvm_monitor spm_monitor;


    /** Class Constructor */
    function new (string name="spm_env", uvm_component parent=null);
        super.new (name, parent);
    endfunction

    /** Build the APB System ENV */
    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        /**
        * Check if the configuration is passed to the environment.
        * If not then create the configuration and pass it to the VIP ENV.
        */
        if (!uvm_config_db#(cust_svt_axi_system_configuration)::get(this, "", "cfg", cfg)) begin
            cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
        end

        // Apply the configuration to the System ENV
        uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cfg);

        m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);

        axi_sequencer = axi_virtual_sequencer::type_id::create("axi_sequencer", this);

        // the if is passed by the hdt top, this might be fixed becase of reusing
        spm_monitor = spm_uvm_monitor::type_id::create("spm_monitor", this);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)

    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info("connect_phase", "Entered...",UVM_LOW)

        //turn off vip messages
        m_axi_system_env.set_report_verbosity_level(UVM_NONE);
        m_axi_system_env.master[0].set_report_verbosity_level(UVM_NONE);
        m_axi_system_env.slave[0].set_report_verbosity_level(UVM_NONE);
        m_axi_system_env.system_monitor.set_report_verbosity_level(UVM_NONE);
    endfunction:connect_phase

    virtual task configure_phase(uvm_phase phase);
        `uvm_info("configure_phase", "Entered...",UVM_LOW)

        super.configure_phase(phase);
        m_axi_system_env.slave[0].axi_slave_mem.set_meminit(svt_mem::ZEROES); //initialize slv memory with zeroes

        `uvm_info("configure_phase", "Exiting...",UVM_LOW)
    endtask

    task reset_phase(uvm_phase phase);
        phase.raise_objection(this,"Restting regmodel");
        phase.drop_objection(this);
    endtask

endclass

`endif  // GUARD_SPM_ENV_SV
