// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_SEQ_BASE_SVH
`define AXE_DMA_CHANNEL_SEQ_BASE_SVH

// Class: axe_dma_channel_default_seq
class axe_dma_channel_seq_base extends uvm_sequence #(uvm_sequence_item);

      axe_dma_channel_config       m_config;
      axe_dma_channel_seq_epilogue prologue;
      axe_dma_channel_seq_epilogue epilogue;

      `uvm_object_utils(axe_dma_channel_seq_base)


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

      /* Function: pre_start

         UVM Built-In

      */
      task pre_start();
          `uvm_do(prologue)
      endtask : pre_start

      /* Function: post_start

         UVM Built-In

      */
      task post_start();
          `uvm_do(epilogue)
      endtask : post_start  

      /* Function: body

         Sequence body

      */
      task body();
            // TODO
            `uvm_info(get_type_name(), "Body", UVM_NONE)
            #100ns;
      endtask : body

endclass : axe_dma_channel_seq_base

`endif // AXE_DMA_CHANNEL_SEQ_BASE_SVH
