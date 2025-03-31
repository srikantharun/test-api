// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// DMA Channel sequence prologue
// - Any initialisation needed before the DMA transfer is initiated
// - Memory initialisation
// - Static configuration
// - etc. etc.
// Owner: abond

`ifndef AXE_DMA_CHANNEL_SEQ_PROLOGUE_SVH
`define AXE_DMA_CHANNEL_SEQ_PROLOGUE_SVH

// Class: axe_dma_channel_default_seq
class axe_dma_channel_seq_prologue extends uvm_sequence #(uvm_sequence_item);

    `uvm_object_utils(axe_dma_channel_seq_prologue)


    /* Function: new 

       Constructor

       Parameters:

          name - Name of the sequence class
          
       Returns:

          Instance of axe_dma_channel_agent
    */
    function new(string name = "");
      super.new(name);
    endfunction : new

    /* Function: body

       Sequence body

    */
    task body();
        // TODO
        `uvm_info(get_type_name(), "Prologue", UVM_NONE)
    endtask : body

endclass : axe_dma_channel_seq_prologue

`endif // AXE_DMA_CHANNEL_SEQ_PROLOGUE_SVH
