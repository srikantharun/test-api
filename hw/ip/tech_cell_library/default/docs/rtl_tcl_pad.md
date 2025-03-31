---
title: "RTL : Chip Pads"
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


Here the functional description of the expected pad models is provided. A concrete tech node implementation should
choose technology cells which follow the same functionality.

## Bidirectional Pad: `axe_tcl_pad_inout`

A bidirectional pad with pull-up/down functionality. The schematic of the model is shown below:

![Functional Schematic: Bidirectional Pad](./figures/axe_tcl_pad_inout.drawio.svg)

### IO Description

{{ io_table("axe_tcl_pad_inout") }}


## Output Pad: `axe_tcl_pad_output`

A pure output pad with pull-up/down functionality. The schematic of the module is shown below:

![Functional Schematic: Output Pad](./figures/axe_tcl_pad_output.drawio.svg)

### IO Description

{{ io_table("axe_tcl_pad_output") }}


## Input Pad: `axe_tcl_pad_input`

A pure input pad. The schematic of the module is shown below:

![Functional Schematic: Input Pad](./figures/axe_tcl_pad_input.drawio.svg)

### IO Description

{{ io_table("axe_tcl_pad_input") }}


## Retention Pad Cell: `axe_tcl_pad_retention`

A retention enable pad. The schematic of the module is shown below:


![Functional Schematic: Retention Pad](./figures/axe_tcl_pad_retention.drawio.svg)

### IO Description

{{ io_table("axe_tcl_pad_retention") }}
