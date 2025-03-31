// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_CFG_ITEM_SVH
`define GUARD_TIMESTAMP_LOGGER_CFG_ITEM_SVH

class timestamp_logger_cfg_item extends uvm_sequence_item;

    rand logic         capture_enable;
    rand logic         trace_mode;
    rand logic         external_mode;
    rand logic [2:0]   cntr_division;

    rand logic         sync_ctrl;
    rand logic         stop;
    rand logic         reset;

    rand logic [39:0]  st_addr;

    rand logic [39:0]  log_size;

    rand logic [2:0]   burst_size;

    rand logic [127:0] group_en;

    rand int unsigned  n_transactions;


    constraint c_sync_ctrl      {   soft    sync_ctrl      == 1'b0;    }
    constraint c_stop           {   soft    stop           == 1'b0;    }
    constraint c_reset          {   soft    reset          == 1'b0;    }

    constraint c_st_addr        {                                       st_addr      >= 40'h0000000000;
                                            external_mode == 1'b0 ->    st_addr      <= `MEM_DEPTH-40'h8;
                                            external_mode == 1'b1 ->    st_addr      <= 40'hffffffffff;
                                                                        st_addr[2:0] == 3'b000;
                                            external_mode == 1'b1 ->    st_addr[9:0] == 10'b0000000000; // 1K aligned
                                }

    constraint c_log_size       {                                       log_size        > 0;
                                                                        log_size       <= 40'hffffffffff;
                                            external_mode == 1'b0 ->    log_size       <= `MEM_DEPTH;
                                                                        log_size[2:0]  == 3'b000;
                                            external_mode == 1'b1 ->    log_size[9:0] == 10'b0000000000; // 1K aligned
                                }

    constraint c_add_size       {           external_mode == 1'b0 -> st_addr + log_size <= `MEM_DEPTH; }

    constraint c_n_transactions {   soft    n_transactions == 1; }

    `uvm_object_utils_begin(timestamp_logger_cfg_item)
        `uvm_field_int(capture_enable,     UVM_DEFAULT)
        `uvm_field_int(trace_mode,         UVM_DEFAULT)
        `uvm_field_int(external_mode,      UVM_DEFAULT)
        `uvm_field_int(cntr_division,      UVM_DEFAULT)
        `uvm_field_int(sync_ctrl,          UVM_DEFAULT)
        `uvm_field_int(stop,               UVM_DEFAULT)
        `uvm_field_int(reset,              UVM_DEFAULT)
        `uvm_field_int(st_addr,            UVM_DEFAULT)
        `uvm_field_int(log_size,           UVM_DEFAULT)
        `uvm_field_int(burst_size,         UVM_DEFAULT)
        `uvm_field_int(group_en,           UVM_DEFAULT)
        `uvm_field_int(n_transactions,     UVM_DEFAULT)
    `uvm_object_utils_end

    function new(string name = "");
        super.new(name);
    endfunction : new

    function int n_group_en();
       return $countones(group_en);
    endfunction : n_group_en

endclass : timestamp_logger_cfg_item

`endif // GUARD_TIMESTAMP_LOGGER_CFG_ITEM_SVH
