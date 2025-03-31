---
title: AIC_DID
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---


This document contains the high level description of the `AIC\_DID` block.
It contains and connects the following 3 IPs to form a processing chain inside the ai-Core:
    - `DWPU`: Depth-Wise-Processing-Unit
    - `IAU`: Integer Arithmetic Unit
    - `DPU`: Data Processing Unit


![Block Schematic: AIC_DID](figures/aic_did_p.drawio.svg)


The top-level consists of the `aic_did_p` wrapper:


<!-- ::: hw/impl/europa/blocks/aic_did/rtl/generated/aic_did_p.sv:aic_did_p  -->

## Clock & Reset Requirements

This block is completely synchronous with a single clock and witout explicit clock-gating inside. See the ports for
requirements.
