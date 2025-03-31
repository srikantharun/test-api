// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_CHANNEL_AGENT_SVH
`define AXE_DMA_CHANNEL_AGENT_SVH

// Class: axe_dma_channel_agent 
class axe_dma_channel_agent extends uvm_agent;

    `uvm_component_utils(axe_dma_channel_agent)

    axe_dma_channel_config       m_config;
    axe_dma_channel_sequencer    m_sequencer;
    axe_dma_channel_driver       m_driver;
    axe_dma_channel_model        m_model;
    axe_dma_channel_scoreboard   m_scoreboard;
    axe_dma_channel_coverage     m_coverage;

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the agent class
          parent - Parent class
          
       Returns:

          Instance of axe_dma_channel_agent
    */
    function  new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    /* Function: build_phase 

       UVM build phase

       Parameters:

          phase - uvm_phase
    */
    function void build_phase(uvm_phase phase);

        m_config = axe_dma_channel_config::type_id::create("m_config", this);
        m_config.build();

        if (m_config.is_active == UVM_ACTIVE)
        begin
            m_sequencer = axe_dma_channel_sequencer::type_id::create("m_sequencer", this);
            m_driver    = axe_dma_channel_driver::type_id::create("m_driver", this);
        end

        if (m_config.checks_enable)
        begin
            m_model      = axe_dma_channel_model::type_id::create("m_model", this);
            m_scoreboard = axe_dma_channel_scoreboard::type_id::create("m_scoreboard", this);
        end

        if (m_config.coverage_enable)
        begin
            m_coverage = axe_dma_channel_coverage::type_id::create("m_coverage", this);
        end

    endfunction : build_phase

    /* Function: connect_phase 

       UVM connect phase

       Parameters:

          phase - uvm_phase
    */
    function void connect_phase(uvm_phase phase);

        if (m_config.is_active == UVM_ACTIVE)
        begin
            // TODO - Connect to AXI Sequencers
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end

    endfunction : connect_phase

   /* Task: run_phase 

       UVM run phase

       Parameters:

          phase - uvm_phase
    */
    task run_phase(uvm_phase phase);

        if (m_config.is_active == UVM_ACTIVE)
        begin
            m_sequencer.start_phase_sequence(phase);
        end

    endtask : run_phase

endclass : axe_dma_channel_agent

`endif // AXE_DMA_CHANNEL_AGENT_SVH
