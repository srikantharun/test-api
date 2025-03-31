//
// File: lpddr_subsystem_base_test.svh
// pcie_subsystem_base_test
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
class lpddr_subsystem_base_test extends uvmf_test_base #(.CONFIG_T(lpddr_subsystem_env_configuration),.ENV_T(lpddr_subsystem_environment),.TOP_LEVEL_SEQ_T(lpddr_subsystem_base_virtual_seq));
    `uvm_component_utils(lpddr_subsystem_base_test)

    function new ( string name = "lpddr_subsystem_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

  task shutdown_phase ( uvm_phase phase);
    super.shutdown_phase(phase);
    phase.raise_objection(this);

    // Delay to ensure all stimulus is reacted to.
    #20us;

    phase.drop_objection(this);
  endtask: shutdown_phase

  function void build_phase ( uvm_phase phase);
    string interface_names[] = { "apb_master_0", "axi4_master_0","apb_master_1"};
    super.build_phase( phase );
    configuration.initialize( BLOCK, "uvm_test_top.top", interface_names );
    uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.reset_phase","default_sequence",lpddr_subsystem_init_seq::type_id::get());
  endfunction: build_phase

endclass: lpddr_subsystem_base_test


