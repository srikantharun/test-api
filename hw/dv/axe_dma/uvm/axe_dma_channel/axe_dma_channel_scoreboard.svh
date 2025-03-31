// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_SCOREBOARD_SVH
`define AXE_DMA_CHANNEL_SCOREBOARD_SVH

// Class: axe_dma_channel_scoreboard
class axe_dma_channel_scoreboard extends axe_uvm_indexed_scoreboard;

    `uvm_component_utils(axe_dma_channel_scoreboard)

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the scoreboard class
          parent - Parent class 
       Returns:

          Instance of axe_dma_channel_scoreboard
    */
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

   /* Function: indices

        Returns array of all possible indices
    
        Returns:

            Array of indices
    */
    virtual function indices_t indices();
        // TODO
        return '{0};
    endfunction : indices

    /* Function: index

        Returns the index for a transation
    
        Parameters:

            t - item

        Returns:

            Index
    */
    virtual function IDX_T index(EXP_T t);
        // TODO
        return 0;
    endfunction : index

   /* Function: convert 

       Convert observed object into data type of expected object

       Parameters:

          t - Observed object

       Returns:

          Instance of expected object class
    */
    virtual function EXP_T convert (OBS_T t);
        // TODO
        return t;
    endfunction : convert
endclass : axe_dma_channel_scoreboard

`endif // AXE_DMA_CHANNEL_scoreboard_SVH
