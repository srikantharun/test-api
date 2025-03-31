// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_DRIVER_SVH
`define AXE_DMA_CHANNEL_DRIVER_SVH

// Class: axe_dma_channel_class 
class axe_dma_channel_driver extends uvm_driver #(uvm_sequence_item);

    `uvm_component_utils(axe_dma_channel_driver)

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the driver class
          parent - Parent class
          
       Returns:

          Instance of axe_dma_channel_driver
    */
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    /* Function: report_phase 

       UVM run phase

       Parameters:

          phase - uvm_phase
    */
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "run_phase", UVM_HIGH)

        forever
        begin
            seq_item_port.get_next_item(req);
            `uvm_info(get_type_name(), {"req item\n",req.sprint}, UVM_DEBUG)
            do_drive();
            seq_item_port.item_done();
        end
    endtask : run_phase


    task do_drive();
        `uvm_fatal(get_type_name(), "TODO: fill do_drive()");
    endtask : do_drive

endclass : axe_dma_channel_driver

`endif // AXE_DMA_CHANNEL_DRIVER_SVH
