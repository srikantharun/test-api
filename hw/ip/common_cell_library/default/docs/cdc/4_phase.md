---
title: "4-phase Handshaked CDC"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_4_phase.sv:axe_ccl_cdc_4_phase

## Structure

The Fifo contains two seperate modules one for source, the other for the destinations. They each operate only on their
respective clocks and have all synchronzer structures included.

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_4_phase/axe_ccl_cdc_4_phase_src.sv:axe_ccl_cdc_4_phase_src

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_4_phase/axe_ccl_cdc_4_phase_dst.sv:axe_ccl_cdc_4_phase_dst
