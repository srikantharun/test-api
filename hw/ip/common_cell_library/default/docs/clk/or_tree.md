---
title: Clock Or Tree
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_clk_or_tree.sv:axe_ccl_clk_or_tree


## Mircoarchitecture

```mermaid
flowchart TD
    I0>i_clk0]
    I1>i_clk1]
    I2>i_clk2]
    I3>i_clk3]
    I4>i_clk4]
    G0((axe_tcl_clk_or2))
    G1((axe_tcl_clk_or2))
    G2((axe_tcl_clk_or2))
    G3((axe_tcl_clk_or2))
    O>o_clk]
    G0 --> O
    G1 --> G0
    G2 --> G0
    G3 --> G2
    I4 --> G1
    I2 --> G2
    I3 --> G1
    I0 --> G3
    I1 --> G3
```

Generates a binary tree comprised of `axe_tcl_clk_or2` modules. This allows for constructing arbitrary wide clock ors.
