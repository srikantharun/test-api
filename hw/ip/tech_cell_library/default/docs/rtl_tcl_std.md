---
title: "RTL : Standard Combinatorial Cells"
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


## BUF: `axe_tcl_std_buffer`

Standard buffer, repeating the signal.

![Functional Schematic: Combinatorial Buffer](./figures/axe_tcl_std_buffer.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_buffer") }}


## INV: `axe_tcl_std_inverter`

Standard Inverter, negating the signal.

![Functional Schematic: Combinatorial Inverter](./figures/axe_tcl_std_inverter.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_inverter") }}


## AND: `axe_tcl_std_and[2|3]`

Combinatorial `AND` gate with different flavours for the amount of input ports.

![Functional Schematic: Combinatorial AND](./figures/axe_tcl_std_and.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_and2") }}


## AND: `axe_tcl_std_nand[2|3]`

Combinatorial `NAND` gate with different flavours for the amount of input ports.

![Functional Schematic: Combinatorial NAND](./figures/axe_tcl_std_nand.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_nand2") }}


## OR: `axe_tcl_std_or[2|3]`

Combinatorial `OR` gate with different flavours for the amount of input ports.

![Functional Schematic: Combinatorial OR](./figures/axe_tcl_std_or.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_or2") }}


## OR: `axe_tcl_std_nor[2|3]`

Combinatorial `NOR` gate with different flavours for the amount of input ports.

![Functional Schematic: Combinatorial NOR](./figures/axe_tcl_std_nor.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std__std_nor2") }}


## XOR: `axe_tcl_std_xor[2|3]`

Combinatorial `XOR` gate with different flavours for the amount of input ports.

![Functional Schematic: Combinatorial XOR](./figures/axe_tcl_std_xor.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_xor2") }}


## XOR: `axe_tcl_std_xnor[2|3]`

Combinatorial `XNOR` gate with different flavours for the amount of input ports.

![Functional Schematic: Combinatorial XNOR](./figures/axe_tcl_std_xnor.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_xnor2") }}


## MUX: `axe_tcl_std_mux2`

Standard cell multiplexer, use this only to force a mux instantiation.

![Functional Schematic: Combinatorial MUX](./figures/axe_tcl_std_mux.drawio.svg)

### IO Description

{{ io_table("axe_tcl_std_mux2") }}
