---
title: Apb
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# APB

Documentation for generic APB components.

## axe_apb_cdc

APB clock domain crossing to connect a manager on i_src_clk domain to a subordinate on i_dst_clk domain.

The two domains can be completely asynchronous and there is no constraint on the clock frequencies being used.

![axe_apb_cdc](fig/axe_apb_cdc.drawio.svg)
