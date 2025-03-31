// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : IRQ Sequence Item
// Owner       : Sultan Khan

`ifndef __IRQ_SEQ_ITEM_SV__
`define __IRQ_SEQ_ITEM_SV__

class irq_seq_item extends uvm_sequence_item;
    `uvm_object_utils(irq_seq_item)

    t_irq_change       change;

    bit [NUM_IRQ_LINES-1:0]  irq_line_state;

    //==========================================================================
    function new(string name = "irq_seq_item");
        super.new(name);
    endfunction
    //==========================================================================

    //==========================================================================
    virtual function string convert2string();
        string s;
        s = $sformatf("IRQ event = %s", change.name());
        return s;
    endfunction
    //==========================================================================

endclass
`endif  //__IRQ_SEQ_ITEM_SV__
