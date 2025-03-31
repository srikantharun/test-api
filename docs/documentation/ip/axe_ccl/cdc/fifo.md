---
title: "Gray Coded Clock Domain Crossing FIFO"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_fifo.sv:axe_ccl_cdc_fifo

## Structure

The Fifo contains two seperate modules one for source, the other for the destinations. They each operate only on their
respective clocks and have all synchronzer structures included.

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_fifo/axe_ccl_cdc_fifo_src.sv:axe_ccl_cdc_fifo_src

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_fifo/axe_ccl_cdc_fifo_dst.sv:axe_ccl_cdc_fifo_dst
