---
title: "RTL : Memories"
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

TODO(@wolfgang.roenninger): Add documentation for tc_sram

## DfT signals:
DFTRAM -> Test control enable, active high
SE     -> Scan enable, active high
SI_D_L -> Scan Input for the lower half DI
SO_D_L -> Scan Output for the lower half DI
SI_D_R -> Scan Input for the upper half DI
SO_D_R -> Scan Output for the upper half DI

The input signals `DFTRAM`, `SI_D_L` and `SI_D_R` should be tied low.
They are going to be connected during MBIST and SCAN insertion.

The output signals `SO_D_L` and `SO_D_R` should remain floating.

The input signal `SE` should be driven by a primary input pin at the top level of the IP.
Then this primary input is connected to `scan_en` of the DfT interface in the wrapper file (_p).
