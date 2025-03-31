---
title: Phase Accumulator
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cnt_phase_acc.sv:axe_ccl_cnt_phase_acc


## Operation Principle

A phase accumulator is a binary counter which periodically overflows and keeps the remainder.
The average overflow rate can be calculated with:

$$
F_{out} = \frac{i\_counter\_increment}{2^{Width}} * F_{i\_clk}
$$

The frequency resolution is defined by the smallest possible incremental change:

$$
F_{res} = \frac{F_{i\_clk}}{2^{Width}}
$$
