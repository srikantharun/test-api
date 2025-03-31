// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CMD_SVH
`define AXE_DMA_CMD_SVH

// Class: axe_dma_cmd
class axe_dma_cmd extends uvm_sequence_item;

    // TODO -add fields
    // Command Format
    rand axe_dma_cmd_fmt_t fmt;

    `uvm_object_utils_begin(axe_dma_cmd)
        `uvm_field_enum(axe_dma_cmd_fmt_t, fmt, UVM_DEFAULT)
    `uvm_object_utils_end


    /* Function: new 

       Constructor

       Parameters:

          name - Name of the tx class

       Returns:

          Instance of axe_dma_cmd
    */
    function new(string name = "");
        super.new(name);
    endfunction : new

endclass : axe_dma_cmd

`endif // AXE_DMA_CMD_SVH
