// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : Package Containing ENUMs and IRQ Agent Makeup
// Owner       : Sultan Khan

package irq_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  localparam  NUM_IRQ_LINES = 4;   // Same defined in irq_if (interface cant be placed inside a pkg)

  typedef enum bit [1:0]
  {
      IRQ_JUST_RAISED,
      IRQ_JUST_CLEARED,
      IRQ_REMAINS_HIGH
  } t_irq_change;

  `include "irq_seq_item.svh"
  `include "irq_monitor.svh"
  `include "irq_agent.svh"

endpackage : irq_pkg
