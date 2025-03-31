
/**
 * Abstract:
 * Defines an interface that provides access to a reset signal.  This
 * interface can be used to write sequences to drive the reset logic.
 */

`ifndef GUARD_AXI_RESET_IF_SVI
`define GUARD_AXI_RESET_IF_SVI

interface axi_reset_if();

  logic reset;
  logic clk;

  modport axi_reset_modport (input clk, output reset);

endinterface

`endif // GUARD_AXI_RESET_IF_SVI
