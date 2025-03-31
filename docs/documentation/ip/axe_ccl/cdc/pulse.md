---
title: "Pulse Clock Domain Crossing"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_pulse.sv:axe_ccl_cdc_pulse


## Operation Principle

![axe_ccl_cdc_pulse architecture drawing](./figures/axe_ccl_cdc_pulse.drawio.svg)

A toggle flip flop provides the means of synchronizing the source domains pulse over to the destination domain. A dual
edge detection (xor) circuit generates the pulse for the destination domain.  The toggle level of the destination domain
is synchronized back to the source domain as feedback.

The observational flags for the source domain are the following:

- `o_src_busy`:  There is an active pulse being synchronized, subsequent source domain pulses will be **dropped**.
- `o_src_error`: A pulse arrived but the module was busy and the pulse was **dropped**.
