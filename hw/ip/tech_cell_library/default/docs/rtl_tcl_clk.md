---
title: "RTL : Balanced Gates and Clock Gating"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
rtl:
  sv:
    tech_cell_library:
      bender:
        hw/ip/tech_cell_library/default/rtl/Bender.yml
---


## BUF: `axe_tcl_clk_buffer`

Buffer designed for clock or reset networks.

![Functional Schematic: Clock Buffer](./figures/axe_tcl_clk_buffer.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_buffer") }}


## INV: `axe_tcl_clk_inverter`

Inverter designed for clock or reset networks.

![Functional Schematic: Clock Inverter](./figures/axe_tcl_clk_inverter.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_inverter") }}


## AND: `axe_tcl_clk_and2`

Balanced `AND` gate designed for clock or reset networks.

![Functional Schematic: Clock AND](./figures/axe_tcl_clk_and.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_and2") }}


## OR: `axe_tcl_clk_or2`

Balanced `OR` gate designed for clock or reset networks.

![Functional Schematic: Clock OR](./figures/axe_tcl_clk_or.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_or2") }}


## XOR: `axe_tcl_clk_xor2`

Balanced `XOR` gate designed for clock or reset networks.

![Functional Schematic: Clock XOR](./figures/axe_tcl_clk_xor.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_xor2") }}


## MUX: `axe_tcl_clk_mux2`

Glitch free multiplexer, designed for clock or reset networks.

![Functional Schematic: Clock MUX](./figures/axe_tcl_clk_mux.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_mux2") }}


## GATE: `axe_tcl_clk_gating`

Integrated clock gating cell with bypass for testing purposes. The cell follows the standard way of clock gating by
utilizing a active-low latch, glitch free-AND and a glitch free mux for bypassing for testing purposes.

![Functional Schematic: Clock Gate](./figures/axe_tcl_clk_gating.drawio.svg)

### IO Description

{{ io_table("axe_tcl_clk_gating") }}
