// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_MODEL_SVH
`define AXE_DMA_CHANNEL_MODEL_SVH

// Class: axe_dma_channel_model
class axe_dma_channel_model extends uvm_subscriber #(axe_dma_cmd);

    // Analysis port - output items for checking on scoreboard
    // TODO - update type
    uvm_analysis_port #(uvm_object) analysis_port;

    `uvm_component_utils(axe_dma_channel_model)

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the MODEL class
          parent - Parent class
          
       Returns:

          Instance of axe_dma_channel_agent
    */
    function new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_port = new("analysis_port", this);
    endfunction : new

    /* Function: write

       Write function. Sample transation item for MODEL
      
       Parameters:

          t - Transaction item to cover
    */
    function void write(input axe_dma_cmd t);
        begin
            // TODO - process command and generate reference objects
        end 
    endfunction : write

endclass : axe_dma_channel_model

`endif // AXE_DMA_CHANNEL_MODEL_SVH
