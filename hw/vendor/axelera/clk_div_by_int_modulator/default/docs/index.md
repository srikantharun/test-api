---
title: clk_div_by_int_modulator
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# clk_div_by_int_modulator

This module is a sub-block of the clk_div_by_int clock divider module. It corresponds to the blue box below:

![int_clk_div](img/int_clk_div.png)

This module has two views:
- A functional model implementation clk_div_by_int_modulator_functional.sv used for simulation only
- A PD implementation made of tech cells clk_div_by_int_modulator.v used for synthesis

## PD implementation

![clk_div_by_int_modulator](img/clk_div_by_int_modulator.png)
