// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_EVENT_ITEM_SVH
`define GUARD_TIMESTAMP_LOGGER_EVENT_ITEM_SVH

class timestamp_logger_event_item extends uvm_sequence_item;
    rand int unsigned                                                                                    n_triggers;
    rand logic                                                                                           sync_start = '0;
    rand logic [timestamp_logger_pkg::TimeLogMaxNrGroups-1:0] [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] msgs       = '0;
    rand int unsigned                                                                                    delay      = '0;     // Only used for stimulus
        logic [timestamp_logger_pkg::TimeLogMaxNrGroups-1:0]                                             triggers   = '0;     // Not randomized - in post randomize
        logic [timestamp_logger_pkg::TimeLogEntryTimestampW-1:0]                                         timestamp  = '0;     // Only used for monitor

    // Previous item useful for complex sequences
    static timestamp_logger_event_item previous_item = null;

    constraint c_sync        { soft  sync_start  == 1'b0;       }
    constraint c_soft_delay  {       delay   inside {[0:100]};  }
    constraint c_n_triggers  {       n_triggers <= `NUM_GROUPS; }

    `uvm_object_utils_begin(timestamp_logger_event_item)
        `uvm_field_int       ( n_triggers,   UVM_DEFAULT)
        `uvm_field_int       ( sync_start,   UVM_DEFAULT)
        `uvm_field_sarray_int( msgs,         UVM_DEFAULT)
        `uvm_field_int       ( delay,        UVM_DEFAULT)
        `uvm_field_int       ( triggers,     UVM_DEFAULT)
        `uvm_field_int       ( timestamp,    UVM_DEFAULT)
    `uvm_object_utils_end

    function new(string name = "");
        super.new(name);
    endfunction : new

    function void post_randomize();
        int unsigned trigger_bit;

        triggers = 0;
        while ($countones(triggers) != n_triggers) begin
            assert(std::randomize(trigger_bit) with {trigger_bit <= `NUM_GROUPS;});
            triggers |= (1 << trigger_bit);
            assert($countones(triggers) <= n_triggers);
        end
    endfunction  : post_randomize

endclass : timestamp_logger_event_item

`endif // GUARD_TIMESTAMP_LOGGER_EVENT_ITEM_SVH
