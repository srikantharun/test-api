// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef AXE_DMA_AGENT_SVH
`define AXE_DMA_AGENT_SVH

// Class: axe_dma_agent 
class axe_dma_agent extends uvm_agent;

    // TODO - Add AXI agents

    `uvm_component_utils(axe_dma_agent)

    axe_dma_config           m_config;
    axe_dma_channel_agent    m_channel_agents[int];

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the agent class
          parent - Parent class
          
       Returns:

          Instance of axe_dma_agent
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

        m_config = axe_dma_config::type_id::create("m_config", this);
        m_config.build();

        for (int i = 0; i < m_config.n_channels; i++)
        begin
            m_channel_agents[i] = axe_dma_channel_agent::type_id::create($sformatf("m_channel_agent[%0d]", i), this);
        end
    endfunction : build_phase

    /* Function: connect_phase 

       UVM connect phase

       Parameters:

          phase - uvm_phase
    */
    function void connect_phase(uvm_phase phase);
      begin
          // TODO - Connect
      end
    endfunction : connect_phase

endclass : axe_dma_agent

`endif // AXE_DMA_AGENT_SVH
