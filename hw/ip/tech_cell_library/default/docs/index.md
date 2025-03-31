---
title: Tech Cell Library
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

This library contains a variety of technology_cells wrappers, intended for heavy reuse in other IP. To ensure smooth
changes between technology nodes all primitives have to be implemented in the respective node. The wrappers are
implemented in common source files grouped by general category of technology cell.

!!! note "File naming convention"
    The naming of the source files is standardized and follows the convention of:
    **`rtl/<tech_node>/axe_tcl_<category>.sv`**

TODO(@wolfgang.roennigner): Update for flow related changes
To use in your IP add the `dependency: axe_tcl_lib` to the `Bender.yml` manifest.

Implemented technology nodes are:

- `rtl` : Behavioral model of a technology cell. Do not use for synthesis, however this set of module needs to be
implemented. for a specific technology node. Refer to the (./rtl.md)[RTL] chapter for functional description for each
module.

!!! note "Module naming convention"
    The naming of a specific wrapper is standardized and follows the convention of: **`axe_tcl_<category>_<function>`**


## `axe_tcl_clk` : Balanced gates and clock gating

These cells are for the usage in clock and reset networks. In general they should be implemented with balanced or
glitch-free gates.

| Name             | Module                     | Description                                | Number Inputs  | Status |
|:---------------- |:-------------------------- |:------------------------------------------ |:-------------  |:------ |
| `Clock BUF`      | `axe_tcl_clk_buffer`       | Clock repeater (buffer)                    | 1              | active |
| `Clock INV`      | `axe_tcl_clk_inverter`     | Clock inversion gate (not)                 | 1              | active |
| `Clock AND`      | `axe_tcl_clk_and2`         | Balanced AND                               | 2              | active |
| `Clock OR`       | `axe_tcl_clk_or2`          | Balanced OR                                | 2              | active |
| `Clock XOR`      | `axe_tcl_clk_xor2`         | Balanced XOR                               | 2              | active |
| `Clock MUX`      | `axe_tcl_clk_mux2`         | Balanced multiplexer                       | 2              | active |
| `Clock Gate`     | `axe_tcl_clk_gating`       | Integrated clock gating cell               | 1              | active |
|                  |                            |                                            |                |        |


## `axe_tcl_pad` : Chip pad models

These are generic I/O-pad models. Pads with output functionality have pull-up/down functionality modeled. Additional
Functionality like driving strength and Schmitt-triggers are expected to be implemented on a per case basis via the
`impl_*_t` types.

| Name                | Module                  | Description                                                      | Status |
|:------------------- |:----------------------- |:---------------------------------------------------------------- |:------ |
| `Bidirectional Pad` | `axe_tcl_pad_inout`     | Bidirectional chip pad with pull-up/down                         | active |
| `Output Pad`        | `axe_tcl_pad_output`    | Output chip pad with pull-up/down                                | active |
| `Input Pad`         | `axe_tcl_pad_input`     | Input chip pad                                                   | active |
| `Pad Retention`     | `axe_tcl_pad_retention` | Pad Retention enable                                             | active |
|                     |                         |                                                                  |        |


## `*.tc_pwr` : Power gating and level shifter

TODO(@wolfgang.roenninger): This is a placeholder for eventual power specific cells like level shifters and power gates.

| Name             | Module                     | Description                                                 | Status |
|:---------------- |:-------------------------- |:----------------------------------------------------------- |:------ |
|                  |                            |                                                             |        |


## `axe_tcl_seq` : Sequential cells and synchronizer

Sequential cells for the edge cases that a specific type of single technology specific cell is needed.
In most cases only the module `axe_tcl_seq_sync` should be used directly in generic RTL code to specify single bit
clock crossings. Ideally these cells should be left to the synthesizer via `always_ff` and `always_latch` blocks.

| Name                      | Module                     | Description                                        | Status |
|:------------------------- |:-------------------------- |:-------------------------------------------------- |:------ |
| `Synchronizer`            | `axe_tcl_seq_sync`         | Cell to synchronize a single bit to another clock  | active |
|                           |                            |                                                    |        |


## `axe_tcl_sram` : Generic SRAM model

A generic SRAM model which provides a convenient entry point everything memory related.

| Name                          | Module    | Description                                                     | Status |
|:----------------------------- |:----------|:--------------------------------------------------------------- |:------ |
| `Static random-access memory` | `tc_sram` | Generic wrapper description for memory                          | active |
|                               |           |                                                                 |        |


## `axe_tcl_std` : Combinatiorial logic cells

Generic combinatorial logic blocks. These in most cases should be handled by normal RTL code and are provided as a
convenience.

| Name   | Module                   | Description                                                    | Number Inputs | Status |
|:------ |:------------------------ |:-------------------------------------------------------------- |:------------- |:------ |
| `BUF`  | `axe_tcl_std_buffer`     | Combinatorial Buffer                                           | 1             | active |
| `INV`  | `axe_tcl_std_inverter`   | Combinatorial Inverter (NOT)                                   | 1             | active |
| `AND`  | `axe_tcl_std_and[2\|3]`  | Combinatorial AND Gate                                         | parameter     | active |
| `NAND` | `axe_tcl_std_nand[2\|3]` | Combinatorial NAND Gate                                        | parameter     | active |
| `OR`   | `axe_tcl_std_or[2\|3]`   | Combinatorial OR Gate                                          | parameter     | active |
| `NOR`  | `axe_tcl_std_nor[2\|3]`  | Combinatorial NOR Gate                                         | parameter     | active |
| `XOR`  | `axe_tcl_std_xor[2\|3]`  | Combinatorial XOR Gate                                         | parameter     | active |
| `XNOR` | `axe_tcl_std_xnor[2\|3]` | Combinatorial XNOR Gate                                        | parameter     | active |
| `MUX`  | `axe_tcl_std_mux[2]`     | Combinatorial Multiplexer                                      | 2             | active |
|        |                          |                                                                |               |        |
