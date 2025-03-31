// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Package containing reusable functions that can be reused in multiple modules.
///
package cc_lib_pkg;

  /// Default index type
  typedef logic [3:0]  index_4_t;

  /// Default address type
  typedef logic [39:0] addr_40_t;

  /// Default type definition for the module cc_decode_addr
  typedef struct packed {
    index_4_t index;
    addr_40_t addr_start;
    addr_40_t addr_end;
  } default_addr_rule_t;
endpackage
