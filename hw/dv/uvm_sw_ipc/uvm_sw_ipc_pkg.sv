package uvm_sw_ipc_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;

  localparam UVM_SW_IPC_EVENT_NB = 1024;

  // UVM_SW_IPC_DATA_FIFO_NB data fifo + 1 cmd args fifo
  localparam UVM_SW_IPC_DATA_FIFO_NB = 2;
  localparam UVM_SW_IPC_FIFO_NB = UVM_SW_IPC_DATA_FIFO_NB + 1;
  // last FIFO used for cmd args
  localparam UVM_SW_IPC_CMD_ARGS_FIFO_IDX = UVM_SW_IPC_FIFO_NB - 1;

  localparam UVM_SW_IPC_FIFO_OFFSET = 8; // 8 bytes = 64 bits = 1 memory word
  // cmd + fifo_to_uvm (UVM_SW_IPC_FIFO_NB times) + fifo_to_sw (UVM_SW_IPC_FIFO_NB times) + empty
  localparam UVM_SW_IPC_MEM_SIZE = (2 + 2 * UVM_SW_IPC_FIFO_NB) * UVM_SW_IPC_FIFO_OFFSET;

  `include "uvm_sw_ipc_tx.sv"
  `include "uvm_sw_ipc_config.sv"
  `include "spm_utils.sv"
  `include "l1_utils.sv"
`ifdef UVM_SW_IPC_FLAVOR_TOP
  `include "uvm_sw_ipc_monitor_top.sv"
`elsif UVM_SW_IPC_FLAVOR_SOC_PERIPH
  `include "uvm_sw_ipc_monitor_top.sv"
`elsif UVM_SW_IPC_FLAVOR_AICORE0
  `include "uvm_sw_ipc_monitor_top.sv"
`endif

  `include "uvm_sw_ipc.sv"

endpackage : uvm_sw_ipc_pkg
