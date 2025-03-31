// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_CONFIG_SVH
`define AXE_DMA_CHANNEL_CONFIG_SVH

// Class: axe_dma_channel_config
class axe_dma_channel_config extends uvm_component;

    // is_active - enables sequencer
    uvm_active_passive_enum  is_active = UVM_ACTIVE;

    // coverage_enable - enables coverage
    bit                      coverage_enable;

    // checks_enable - enables model and scoreboard
    bit                      checks_enable;

    // Linked List Master Select
    rand axe_dma_ms_t        ll_ms;

     // Destination Master Select
    rand axe_dma_ms_t        dst_ms;   
 
    // Source Master Select
    rand axe_dma_ms_t        src_ms;

    // Destination Outstanding Request Limit
    rand axe_dma_ost_lmt_t   dst_ost_lmt;

    // Source Outstanding Request Limit
    rand axe_dma_ost_lmt_t   src_ost_lmt;

    `uvm_component_utils_begin(axe_dma_channel_config)
        `uvm_field_enum(uvm_active_passive_enum, is_active,       UVM_DEFAULT)
        `uvm_field_int(                          coverage_enable, UVM_DEFAULT)
        `uvm_field_int(                          checks_enable,   UVM_DEFAULT)
        `uvm_field_enum(axe_dma_ms_t           , ll_ms,           UVM_DEFAULT) 
        `uvm_field_enum(axe_dma_ms_t           , dst_ms,          UVM_DEFAULT)
        `uvm_field_enum(axe_dma_ms_t           , src_ms,          UVM_DEFAULT) 
        `uvm_field_int(                          dst_ost_lmt,     UVM_DEFAULT)
        `uvm_field_int(                          src_ost_lmt,     UVM_DEFAULT) 
    `uvm_component_utils_end

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the config class
          parent - Parent class
       Returns:

          Instance of axe_dma_channel_config
    */
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

endclass : axe_dma_channel_config

`endif // AXE_DMA_CHANNEL_CONFIG_SVH
