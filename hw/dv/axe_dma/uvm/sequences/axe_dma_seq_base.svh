// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_SEQ_BASE_SVH
`define AXE_DMA_SEQ_BASE_SVH

// Class: axe_dma_channel_default_seq
class axe_dma_seq_base extends uvm_sequence #(uvm_sequence_item);

    `uvm_object_utils(axe_dma_seq_base)

    axe_dma_channel_agent channel_agent[int];

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
        uvm_phase phase = get_starting_phase();
        if (phase != null)
            phase.raise_objection(this);
    endtask : pre_start

    /* Function: post_start

        UVM Built-In

    */
    task post_start();
        uvm_phase phase = get_starting_phase();
        if (phase != null)
            phase.drop_objection(this);
    endtask : post_start

    /* Task: body

         Sequence body

    */
    task body();
        // TODO
        `uvm_info(get_type_name(), "Body", UVM_NONE)

        for (int i = 0; i < channel_agent.size(); i++)
        begin
            fork
                automatic int channel = i;
                start_channel(channel);
            join_none
        end
        wait fork;
    endtask : body

    /* Task: start_channel

        Start Channels sequences

        Parameters:
            channel - Index of channel
        
    */
    task automatic start_channel(int channel);
        if (channel_agent[channel].m_config.is_active == UVM_ACTIVE)
        begin
            axe_dma_channel_seq_base seq;
            seq = axe_dma_channel_seq_base::type_id::create("seq");
            seq.set_item_context(this, channel_agent[channel].m_sequencer);
            assert(seq.randomize());
            seq.m_config = channel_agent[channel].m_config;
            seq.set_starting_phase(get_starting_phase());
            seq.start(channel_agent[channel].m_sequencer, this);
        end
    endtask : start_channel
endclass : axe_dma_seq_base

`endif // AXE_DMA_SEQ_BASE_SVH
