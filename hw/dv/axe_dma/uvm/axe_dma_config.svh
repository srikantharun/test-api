// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CONFIG_SVH
`define AXE_DMA_CONFIG_SVH

// Class: axe_dma_config
class axe_dma_config extends uvm_component;

    // is_active - enables sequencer
    uvm_active_passive_enum  is_active = UVM_ACTIVE;

    // coverage_enable - enables coverage
    bit                      coverage_enable;

    // checks_enable - enables model and scoreboard
    bit                      checks_enable;

    // n_channels - number of dma channels
    int                      n_channels;

    `uvm_component_utils_begin(axe_dma_config)
        `uvm_field_enum(uvm_active_passive_enum, is_active,       UVM_DEFAULT)
        `uvm_field_int(                          coverage_enable, UVM_DEFAULT)
        `uvm_field_int(                          checks_enable,   UVM_DEFAULT)
        `uvm_field_int(                          n_channels,      UVM_DEFAULT)
    `uvm_component_utils_end

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the config class
          parent - Parent class
          
       Returns:

          Instance of axe_dma_config
    */
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

endclass : axe_dma_config

`endif // AXE_DMA_CONFIG_SVH
