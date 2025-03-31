// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : IRQ (UVM) Agent
// Owner       : Sultan Khan

`ifndef __IRQ_AGENT_SV__
`define __IRQ_AGENT_SV__

class irq_agent extends uvm_agent;
    uvm_analysis_port#(irq_seq_item)  ap;
    `uvm_component_utils(irq_agent)

    irq_monitor       monitor;
    virtual irq_if    vif;

    //==========================================================================
    function new(string name = "irq_agent", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap",this);
    endfunction
    //==========================================================================

    //==========================================================================
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual irq_if)::get(this,"","dma_irq_vif",vif))
        begin
            `uvm_fatal(get_type_name(),"No IRQ VIF is pushed to config_db!")
        end
        monitor     = irq_monitor::type_id::create("monitor", this);
        monitor.vif = vif;
    endfunction
    //==========================================================================

    //==========================================================================
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        monitor.ap.connect(ap);
    endfunction
    //==========================================================================

endclass

`endif  // __IRQ_AGENT_SV__
