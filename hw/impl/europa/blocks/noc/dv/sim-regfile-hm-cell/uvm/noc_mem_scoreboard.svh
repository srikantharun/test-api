// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_SCOREBOARD_SVH
`define GUARD_NOC_MEM_SCOREBOARD_SVH

class noc_mem_scoreboard extends axe_uvm_scoreboard #(noc_mem_item, noc_mem_item);

    `uvm_component_utils(noc_mem_scoreboard)

    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

endclass : noc_mem_scoreboard
`endif // GUARD_NOC_MEM_SCOREBOARD_SVH
