// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// DMA Channel sequence epilogue 
// - Any checks / cleanup needed after the DMA transfer is complete
// - Memory checks 
// - Status / Intetrrupt checks / tear down
// - etc. etc.
// Owner: abond

`ifndef AXE_DMA_CHANNEL_SEQ_EPILOGUE_SVH
`define AXE_DMA_CHANNEL_SEQ_EPILOGUE_SVH

// Class: axe_dma_channel_default_seq
class axe_dma_channel_seq_epilogue extends uvm_sequence #(uvm_sequence_item);

    `uvm_object_utils(axe_dma_channel_seq_epilogue)


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
        `uvm_info(get_type_name(), "Epilogue", UVM_NONE)
    endtask : body

endclass : axe_dma_channel_seq_epilogue

`endif // AXE_DMA_CHANNEL_SEQ_EPILOGUE_SVH
