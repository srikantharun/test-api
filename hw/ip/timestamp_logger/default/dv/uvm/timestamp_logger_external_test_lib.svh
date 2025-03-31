// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_EXTERNAL_TEST_LIB_SVH
`define GUARD_TIMESTAMP_LOGGER_EXTERNAL_TEST_LIB_SVH

class timestamp_logger_external_cfg_item extends timestamp_logger_cfg_item;

  `uvm_object_utils(timestamp_logger_external_cfg_item)

  constraint c_capture_enable { capture_enable == 1'b1;    }
  constraint c_external_mode  { external_mode  == 1'b1;    }
  constraint c_group_en       { group_en       == (1 << `NUM_GROUPS)-1;}
  constraint c_burst_size     { burst_size     inside {[0:7]}; }

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_cfg_item

// ---------------------------------------------------------------------
// Sanity Test
// ---------------------------------------------------------------------
class timestamp_logger_external_sanity_cfg_item extends timestamp_logger_external_cfg_item;

  `uvm_object_utils(timestamp_logger_external_sanity_cfg_item)

  constraint c_group_en       { group_en       == 1;          }
  constraint c_st_addr        { st_addr        == 40'h0;      }
  constraint c_log_size       { log_size       == 8*8;        }
  constraint c_n_transactions { n_transactions == 1;          }
  constraint c_burst_size     { burst_size     == 1;          }

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_sanity_cfg_item

class timestamp_logger_external_sanity_event_item extends timestamp_logger_event_item;

    `uvm_object_utils(timestamp_logger_external_sanity_event_item)

    function new(string name = "");
        super.new(name);
    endfunction : new

    function void post_randomize();
        triggers = 1;
    endfunction  : post_randomize

endclass : timestamp_logger_external_sanity_event_item

class timestamp_logger_external_sanity_test extends timestamp_logger_test;

  constraint c_n_programs        { n_programs       == 1; }

  `uvm_component_utils(timestamp_logger_external_sanity_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_sanity_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_sanity_event_item::get_type(), 1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_sanity_test

// ---------------------------------------------------------------------
// Single Trigger Tests
// ---------------------------------------------------------------------
class timestamp_logger_external_single_trigger_cfg_item extends timestamp_logger_external_cfg_item;

  constraint c_log_size2      { log_size inside {[512*8:1024*8]};     } // Moderate number of entries

  `uvm_object_utils(timestamp_logger_external_cfg_item)

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_single_trigger_cfg_item

class timestamp_logger_external_single_trigger_event_item extends timestamp_logger_event_item;

    constraint c_n_triggers { n_triggers == 1; }

    `uvm_object_utils(timestamp_logger_external_single_trigger_event_item)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : timestamp_logger_external_single_trigger_event_item

// ---------------------------------------------------------------------
// Single Trigger No Flush (number of transactions is multiple of burst size)
// ---------------------------------------------------------------------
class timestamp_logger_external_single_trigger_no_flush_cfg_item extends timestamp_logger_external_single_trigger_cfg_item;

  constraint c_n_transactions   {                           n_transactions    <= log_size/4;
                                    (burst_size == 1) ->    n_transactions[  0] == 1'b0;
                                    (burst_size == 2) ->    n_transactions[1:0] == 1'b0;
                                    (burst_size == 3) ->    n_transactions[2:0] == 2'b0;
                                    (burst_size == 4) ->    n_transactions[3:0] == 3'b0;
                                    (burst_size == 5) ->    n_transactions[4:0] == 4'b0;
                                    (burst_size == 6) ->    n_transactions[5:0] == 5'b0;
                                    (burst_size == 7) ->    n_transactions[6:0] == 6'b0;
                                }

  `uvm_object_utils(timestamp_logger_external_single_trigger_no_flush_cfg_item)

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_single_trigger_no_flush_cfg_item

class timestamp_logger_external_single_trigger_no_flush_test extends timestamp_logger_test;

  constraint c_n_programs { n_programs inside {[50:100]}; }

  `uvm_component_utils(timestamp_logger_external_single_trigger_no_flush_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_single_trigger_no_flush_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_single_trigger_event_item::get_type(),         1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_single_trigger_no_flush_test


// ---------------------------------------------------------------------
// Single Trigger Flush (number of transactions is not multiple of burst size)
// ---------------------------------------------------------------------
class timestamp_logger_external_single_trigger_flush_cfg_item extends timestamp_logger_external_single_trigger_cfg_item;

  constraint c_n_transactions   {                           n_transactions    <= log_size/4;
                                    (burst_size == 1) ->    n_transactions[  0] != 1'b0;
                                    (burst_size == 2) ->    n_transactions[1:0] != 1'b0;
                                    (burst_size == 3) ->    n_transactions[2:0] != 2'b0;
                                    (burst_size == 4) ->    n_transactions[3:0] != 3'b0;
                                    (burst_size == 5) ->    n_transactions[4:0] != 4'b0;
                                    (burst_size == 6) ->    n_transactions[5:0] != 5'b0;
                                    (burst_size == 7) ->    n_transactions[6:0] != 6'b0;
                                }

  `uvm_object_utils(timestamp_logger_external_single_trigger_flush_cfg_item)

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_single_trigger_flush_cfg_item

class timestamp_logger_external_single_trigger_flush_test extends timestamp_logger_test;

  constraint c_n_programs { n_programs inside {[50:100]}; }

  `uvm_component_utils(timestamp_logger_external_single_trigger_flush_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_single_trigger_flush_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_single_trigger_event_item::get_type(),         1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_single_trigger_flush_test
// ---------------------------------------------------------------------
// Single Trigger Random
// ---------------------------------------------------------------------
class timestamp_logger_external_single_trigger_random_cfg_item extends timestamp_logger_external_single_trigger_cfg_item;

  constraint c_n_transactions { n_transactions inside {[1:1000]}; }

  constraint c_sync_ctrl      { sync_ctrl   dist  { 1'b1 := 1, 1'b0 := 4 }; }
  constraint c_trace_mode     { trace_mode  dist  { 1'b1 := 1, 1'b0 := 4 }; }
  constraint c_log_size2      { log_size inside   {[512*8:(1024*16)*8]};    }

  `uvm_object_utils(timestamp_logger_external_single_trigger_random_cfg_item)

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_single_trigger_random_cfg_item

class timestamp_logger_external_single_trigger_random_test extends timestamp_logger_test;

  constraint c_n_programs           { n_programs               == 200;     }
  constraint c_random_cfg_read_rate { random_cfg_read_rate inside {[1:3]}; }

  `uvm_component_utils(timestamp_logger_external_single_trigger_random_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_single_trigger_random_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_single_trigger_event_item::get_type(),            1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_single_trigger_random_test

// ---------------------------------------------------------------------
// Single Trigger Corner Cases
// ---------------------------------------------------------------------
class timestamp_logger_external_single_trigger_log_smaller_than_burst_cfg_item extends timestamp_logger_external_single_trigger_cfg_item;

  constraint c_n_transactions { n_transactions > log_size; n_transactions < 2*log_size; }

  constraint c_sync_ctrl      { sync_ctrl   dist   { 1'b1 := 1, 1'b0 := 4 }; }
  constraint c_trace_mode     { trace_mode  dist   { 1'b1 := 1, 1'b0 := 4 }; }
  constraint c_burst_size     { burst_size  inside {6, 7};                   }
  constraint c_log_size2      { burst_size == 6 -> log_size     == 1024;
                                burst_size == 7 -> log_size inside {1024, 2048};
                              }

  `uvm_object_utils(timestamp_logger_external_single_trigger_log_smaller_than_burst_cfg_item)

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_single_trigger_log_smaller_than_burst_cfg_item

class timestamp_logger_external_single_trigger_log_smaller_than_burst_test extends timestamp_logger_test;

  constraint c_n_programs           { n_programs               == 1 ;      }
  constraint c_random_cfg_read_rate { random_cfg_read_rate inside {[1:3]}; }

  `uvm_component_utils(timestamp_logger_external_single_trigger_log_smaller_than_burst_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_single_trigger_log_smaller_than_burst_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_single_trigger_event_item::get_type(),                        1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_single_trigger_log_smaller_than_burst_test
// ---------------------------------------------------------------------
// Multi Trigger Tests
// ---------------------------------------------------------------------
class timestamp_logger_external_multi_trigger_cfg_item extends timestamp_logger_external_cfg_item;

  constraint c_log_size2      { log_size    inside { [2048*8:8182*8]};       } // Moderate number of entries
  constraint c_sync_ctrl      { sync_ctrl   dist   { 1'b1 := 1, 1'b0 := 4 }; }
  constraint c_trace_mode     { trace_mode  dist   { 1'b0 := 1, 1'b0 := 4 }; }

  constraint c_n_transactions { n_transactions dist { [1:8]     :/ 1,
                                                      [9:128]   :/ 3,
                                                      [129:256] :/ 1
                                                    };
                              }
  constraint c_group_en       { group_en       != '0 ; }

  `uvm_object_utils(timestamp_logger_external_multi_trigger_cfg_item)

  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : timestamp_logger_external_multi_trigger_cfg_item

class timestamp_logger_external_multi_trigger_event_item extends timestamp_logger_event_item;

    constraint c_n_triggers { n_triggers dist { 0                := 1,
                                                [1:3]            := 5,
                                                [4:`NUM_GROUPS]  :/ 5
                                              };
                            }
    constraint c_delay      { delay dist { 0 := 3, 1 := 1, 2 := 1, [3:100] :/ 1 } ; }

    `uvm_object_utils(timestamp_logger_external_multi_trigger_event_item)

    function new(string name = "");
        super.new(name);
    endfunction : new

endclass : timestamp_logger_external_multi_trigger_event_item

class timestamp_logger_external_multi_trigger_test extends timestamp_logger_test;

  constraint c_n_programs           { n_programs           inside {[50:100]}; }
  constraint c_random_cfg_read_rate { random_cfg_read_rate inside {[1:3]};    }
  constraint c_rate_limit           { rate_limit               == 1'b1;       }

  `uvm_component_utils(timestamp_logger_external_multi_trigger_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_multi_trigger_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_multi_trigger_event_item::get_type(), 1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_multi_trigger_test

class timestamp_logger_external_multi_trigger_ovfl_test extends timestamp_logger_test;

  constraint c_n_programs           { n_programs           inside {[50:100]}; }
  constraint c_random_cfg_read_rate { random_cfg_read_rate inside {[1:3]};    }
  constraint c_rate_limit           { rate_limit               == 1'b0;       }

  `uvm_component_utils(timestamp_logger_external_multi_trigger_ovfl_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    set_type_override_by_type(timestamp_logger_cfg_item::get_type(),   timestamp_logger_external_multi_trigger_cfg_item::get_type(),   1'b1);
    set_type_override_by_type(timestamp_logger_event_item::get_type(), timestamp_logger_external_multi_trigger_event_item::get_type(), 1'b1);
  endfunction : build_phase

endclass : timestamp_logger_external_multi_trigger_ovfl_test

`endif // GUARD_TIMESTAMP_LOGGER_EXTERNAL_TEST_LIB_SVH
