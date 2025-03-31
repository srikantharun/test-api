
/**
 * Abstract:
 * This file creates a base test, which serves as the base class for the rest
 * of the tests in this environment.  This test sets up the default behavior
 * for the rest of the tests in this environment.
 *
 * In the build_phase phase of the test we will set the necessary test related
 * information:
 *  - Use type wide factory override to set cust_svt_axi_master_transaction
 *    as the default master transaction type
 *  - Create a default configuration and set it to the axi_basic_env instance
 *    using the configuration DB
 *  - Create the axi_basic_env instance (named env)
 *  - Configure the axi_master_random_discrete_virtual_sequence as the default
 *    sequence for the main phase of the virtual sequence of the axi System ENV
 *    virtual sequencer.  This sequence can be disabled by extended tests by
 *    setting the axi_null_virtual_sequence.
 *  - Configure the sequence length to 50
 *  - Configure the built-in svt_axi_slave_memory_sequence as the default sequence for
 *    all Slave Sequencers
 *  - Configure the axi_simple_reset_sequence as the default sequence for the reset
 *    phase of the TB ENV virtual sequencer
 */
`ifndef GUARD_SPM_BASE_TEST_SV
`define GUARD_SPM_BASE_TEST_SV

class spm_illegal_axi_txn_demoter extends uvm_report_catcher;
    `uvm_object_utils(spm_illegal_axi_txn_demoter)

    function new(string name="spm_illegal_axi_txn_demoter");
        super.new(name);
    endfunction

    function bit string_search(string message, string pattern);
        int match_count;
        int len         = message.len();
        int pattern_len = pattern.len();
        for(int i =0; i < len;i++) begin
            if(message.substr(i,i+pattern_len-1) ==pattern) begin
            match_count +=1;
            end
        end
        return (match_count>0);
    endfunction

    function action_e catch();
        bit err;
        // vioalte AXI protocol so the Slave Issues SLVERR
        err = string_search(get_message(), "Master Transaction is_valid check failed");
        if (err) begin
        set_severity(UVM_INFO);
        end
        return THROW;
    endfunction
endclass

class spm_base_test extends uvm_test;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_base_test)

    /** Instance of the environment */
    spm_env env;

    /** Customized configuration */
    cust_svt_axi_system_configuration cfg;

    virtual spm_if spm_if;

    spm_config_t                                    spm_config;

    axe_uvm_memory_allocator spm_memory_allocator;


    /** Class Constructor */
    function new(string name = "spm_base_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction: new

    /** Allow a test to tweak the configuration */
    virtual function void test_cfg(cust_svt_axi_system_configuration cfg);
    endfunction

    /**
    * Build Phase
    * - Create and apply the customized configuration transaction factory
    * - Create the TB ENV
    * - Set the default sequences
    */
    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);



        /** Factory override of the master transaction object */
        set_type_override_by_type (svt_axi_master_transaction::get_type(),
                                cust_svt_axi_master_transaction::get_type());


        if (cfg == null)  begin
            cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
        end

        /** Set configuration in environment */
        uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

        /** Create the environment */
        env = spm_env::type_id::create("env", this);


        /** Apply the default sequence to the System ENV virtual sequencer
        * A virtual sequence is applied by default which generates unconstrained random
        * master transactions on all masters.  Extended tests can disable this behavior in
        * one of two ways:
        *   1) If using UVM 1.0 then this virtual sequence can be overriden with the
        *      axi_null_virtual_sequence.
        *   2) If using UVM 1.1 then his virtual sequence can be overriden by configuring
        *      the default sequence of the main phase as 'null'.
        *
        * Note that this sequence is configured using the uvm_object_wrapper with the
        * uvm_config_db. So extended tests must also configure the default_sequence using
        * the uvm_object_wrapper rather than using a sequence instance.
        */

        /** Apply the Slave default response sequence to every Slave sequencer
        * Slaves will use the memory response sequence by default.  To override this behavior
        * extended tests can apply a different sequence to the Slave Sequencers.
        *
        * This sequence is configured for the run phase since the slave should always
        * respond to recognized requests.
        */

        uvm_config_db#(virtual spm_if)::get(uvm_root::get(), "", "spm_intf", spm_if);

        /** Apply the default reset sequence */
        uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());

        uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave[0].sequencer.main_phase", "default_sequence", svt_axi_slave_memory_sequence::type_id::get());


        if(!uvm_config_db #(spm_config_t)::get(uvm_root::get(), "", "spm_config", spm_config))
            `uvm_fatal(get_full_name(), "no spm config found");

        spm_memory_allocator = axe_uvm_memory_allocator::type_id::create("spm_memory_allocator", this);
        spm_memory_allocator.base           = 0;
        spm_memory_allocator.top            = spm_config.spm_mem_size_kb*1024 - 1;
        spm_memory_allocator.partition_size = spm_config.spm_mem_macro_depth_k*spm_config.spm_axi_data_width*1024/8;

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction: build_phase



    /**
    * Calculate the pass or fail status for the test in the final phase method of the
    * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
    * test will fail.
    */
    function void final_phase(uvm_phase phase);
        uvm_report_server svr;
        `uvm_info("final_phase", "Entered...",UVM_LOW)

        super.final_phase(phase);

        svr = uvm_report_server::get_server();

        if (svr.get_severity_count(UVM_FATAL) +
            svr.get_severity_count(UVM_ERROR) +
            svr.get_severity_count(UVM_WARNING) > 50000)
        `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
        else
        `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

        `uvm_info("final_phase", "Exiting...", UVM_LOW)
    endfunction: final_phase

endclass

`endif // GUARD_SPM_BASE_TEST_SV
