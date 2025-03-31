---
title: Lifecycle and accesses verification plan
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# Lifecycle and accesses verification plan

## Introduction

### Overview
The aim of this testcases is to verify that lifecycle of the chip and the accesses allowed on every phase are accordingly to the specification.
These are the phases of the product:
  1. WAFER_TEST
  2. WAFER_PERSO
  3. USER_DELIVERY
  4. USER_SECURED
  5. USER_DECOMMISSIONED
  6. RMA (Return Merchandise Authorization)
  7. EOL (End Of Life)

Test/DAP/Platform is opened during phases 1, 2 and 6. On the other phases, the debug is locked.

### Diagram
![*Top level connections for lifecycle accesses verification*](img/APU_connect_KS3.jpg)

#### Pre-requisites
 - Know the correct lifecycle and its available accesses on each stage [link documentation](TODO)
 - Build the Testbench environment to be possible to access every interface available [link gitlab issue](TODO)
 - Create a list of scenarios [link list of scenarios](TODO)

### Ownership
|  Team              | Contact         |
| ------------------ | --------------- |
| ***Architecture*** | Matt Moris |
| ***Design***       | Abhishek Maringanti |
| ***Verification*** | Jorge Carvalho |

### Reference (TODO)
| Team               | Specification |
| ------------------ | ------------- |
| ***Architecture*** |[Arch Spec](TODO)|
| ***Design***       |[Block Spec](TODO)|

### Project Planning and Tracking
|   | Link |
| - | ---- |
| ***Plan*** |[Gitlab Issues Board](https://git.axelera.ai/ai-dv-team/dv-europa-planning/SECURITY/-/issues/2)|
| ***Issues*** |[Gitlab Open Issues](https://git.axelera.ai/ai-dv-team/dv-europa-planning/SECURITY/-/issues/12)|

## Testcases

Tests to be run at top level / Veloce

| Testcase   | Description | Source | Link |
| --------   | ----------- | ------ | ---- |
| sec_lifecycle_incr | Verify that is possible to set lifecycle from WAFER_TEST until EOL | [Link to Source]()| [Last CI Run]()|
| sec_debug_access | Verify that debug is only open when in WAFER_TEST, WAFER_PERSO and RMA stages | [Link to Source]()| [Last CI Run]()|
| sec_open_debug  | Verify that is possible to open debug during infield operations using challenge interface command (**needs confirmation from Kudelski**) | [Link to Source]()| [Last CI Run]()|

## Useful links
 - [Security Verification Plan Document](index.md)
