// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef DMA_ENV_SVH
`define DMA_ENV_SVH

// Class: axe_dma_agent 
class dma_env extends uvm_env;

    // TODO - Add AXI agents

    `uvm_component_utils(dma_env)

    axe_dma_agent           m_dma_agent;

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

        uvm_config_db#(int)::set(this, "m_dma_agent.m_config", "n_channels", `DMA_NCHANNELS);
        m_dma_agent = axe_dma_agent::type_id::create("m_dma_agent", this);

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

    /* Function: run_phase 

       UVM run phase

       Parameters:

          phase - uvm_phase
    */
    task run_phase(uvm_phase phase);
        axe_dma_seq_base vseq;
        vseq = axe_dma_seq_base::type_id::create("vseq");
        vseq.set_item_context(null, null);
        assert(vseq.randomize());

        for (int i = 0; i < m_dma_agent.m_config.n_channels; i++)
        begin
            vseq.channel_agent[i] = m_dma_agent.m_channel_agents[i];
        end

        vseq.set_starting_phase(phase);
        vseq.start(null);
    endtask : run_phase

endclass : dma_env

`endif // DMA_ENV_SVH
