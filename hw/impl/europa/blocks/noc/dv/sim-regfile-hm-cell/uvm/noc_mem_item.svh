// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_ITEM_SVH
`define GUARD_NOC_MEM_ITEM_SVH

class noc_mem_item extends uvm_sequence_item;
    rand bit                rd_en   = '0;
    rand int unsigned       rd_addr = '0;
    rand logic [`DATAW-1:0] rd_data = '0;

    rand bit                wr_en   = '0;
    rand int unsigned       wr_addr = '0;
    rand logic [`DATAW-1:0] wr_data = '0;
    rand logic [`DATAW-1:0] wr_ben  = '0;

    constraint c_wr_bit_en {    (wr_en == 1'b1) -> (wr_ben == '1 || wr_ben == '0);
                                (wr_en == 1'b0) -> (wr_ben == '0);
    }

    `uvm_object_utils_begin(noc_mem_item)
        `uvm_field_int(rd_en,     UVM_DEFAULT)
        `uvm_field_int(rd_addr,   UVM_DEFAULT)
        `uvm_field_int(rd_data,   UVM_DEFAULT | UVM_NOCOMPARE)
        `uvm_field_int(wr_en,     UVM_DEFAULT)
        `uvm_field_int(wr_addr,   UVM_DEFAULT)
        `uvm_field_int(wr_data,   UVM_DEFAULT)
        `uvm_field_int(wr_ben,    UVM_DEFAULT)
    `uvm_object_utils_end

    function new(string name = "");
        super.new(name);
    endfunction : new

    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit retVal;
        noc_mem_item _rhs;
        assert($cast(_rhs, rhs));

        retVal  = super.do_compare(_rhs, comparer);
        if (rd_en)
            retVal &= _rhs.rd_data === this.rd_data;

        return retVal;
    endfunction : do_compare

endclass : noc_mem_item

`endif // GUARD_NOC_MEM_ITEM_SVH
