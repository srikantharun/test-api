---
title: Hysteresis Comparator
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_mon_hysteresis_comparator.sv:axe_ccl_mon_hysteresis_comparator


## Features

This module implements a comparator with hysteresis, meaning that if the input data goes outside of the upper or lower boundary,
it will toggle and retain that value until it reaches the opposite boundary.

The module checks for correctly configured boundaries. The assumption is `i_upper >= i_lower`, `o_active` remains stable otherwise.
