// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_COVERAGE_SVH
`define AXE_DMA_CHANNEL_COVERAGE_SVH

// Class: axe_dma_channel_coverage
class axe_dma_channel_coverage extends uvm_subscriber #(axe_dma_cmd);

    `uvm_component_utils(axe_dma_channel_coverage)

    // TODO - insert coverage groups

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the coverage class
          parent - Parent class
          
       Returns:

          Instance of axe_dma_channel_agent
    */
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    /* Function: write

       Write function. Sample transation item for coverage
      
       Parameters:

          t - Transaction item to cover
    */
    function void write(input axe_dma_cmd t);
        begin
            // TODO
        end 
    endfunction : write

    /* Function: report_phase 

       UVM report phase
       Report coverage score for coverage group

       Parameters:

          phase - uvm_phase
    */
    function void report_phase(uvm_phase phase);
        begin
            // TODO
        end
    endfunction : report_phase

endclass : axe_dma_channel_coverage

`endif // AXE_DMA_CHANNEL_COVERAGE_SVH
