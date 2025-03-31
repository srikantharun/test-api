---
title: l2_p
doc: 
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# L2

## Table of contents

- [L2](#l2)
  - [Table of contents](#table-of-contents)
  - [Introduction](#introduction)
    - [Overview](#overview)
      - [Block Integration](#block-integration)
    - [System Diagram](#system-diagram)
  - [Functional Description](#functional-description)
    - [Performance Requirements](#performance-requirements)
    - [CSR Details](#csr-details)
  - [Implementation Description](#implementation-description)
    - [Block Diagram](#block-diagram)
    - [Clocks and Resets](#clocks-and-resets)
    - [IO and Interfaces](#io-and-interfaces)
    - [Physical Considerations](#physical-considerations)
      - [Memory Details](#memory-details)
      - [Floorplanning considerations](#floorplanning-considerations)
      - [Special DFT Requirements](#special-dft-requirements)
    - [Timing Exceptions](#timing-exceptions)


## Introduction

### Overview

<!--
TODO: Specific block overview and link to the Arch docs once available
-->

#### Block Integration

<!--
TODO: Description how l2 is integrated in the system
-->        

### System Diagram

The L2 architecture has one AXI4 interface and one APB4 interface .

<!--
TODO: Add a system-level diagram - link to Arch docs
-->


## Functional Description

The L2 block is a 16MiB contiguous memory address space, however internally is split into 16 separate banks each 1MiB of contiguous space. Each bank can be accesses in parallel by the 512-bit wide Full duplex AXI port.

The AXI channel needs to be first converted into a MEM INTF protocol with decoupled RD and WR channels. A RR arbiter per bank will arbitrate the RD/WR MEM requests towards the bank. On a given cycle only a read or write operation can take place for each of the banks. Simultaneous accesses to the same bank are not required therefore the bank can be composed by single port RAMs.

Each of the banks will be composed by further physical sub-banks in order to form the full granule for the access for the 512-bit wide rams.

### Performance Requirements

The AXI4 features and characteristics of the INTF are described in the table below.

| **Interface characteristics** | **Interface Information**                                                                  |
| ----------------------------- | ------------------------------------------------------------------------------------------ |
| Bus Protocol                  | AXI4                                                                                       |
| Port Data Width               | 512                                                                                        |
| Address Width                 | 40 (24-bit truncated)                                                                      |
| Address Alignment             | Aligned and Unaligned support                                                              |
| Max Burst Length              | INCR: 256<br><br>WRAP:16<br><br>FIXED: 16                                                  |
| Burst Type                    | INCR, WRAP, FIXED                                                                          |
| Burst size                    | 1 to 128                                                                                   |
| Transaction Attributes        | None, Modifiable, Bufferable<br><br>Read-allocate Write-allocate                           |
| Burst Cross Boundary          | 4K                                                                                         |
| Exclusives                    | Not Supported                                                                              |
| Narrow Bursts                 | Supported                                                                                  |
| Byte Enable Usage             | Supported                                                                                  |
| Read Response Interleaving    | Not supported on the module level but it is supported if we see the complete L2 as a whole |
| Write Interleaving            | Not supported on the module level but it is supported if we see the complete L2 as a whole |
| Write Response                | Posted                                                                                     |
| Read-Write Ordering           | Not maintained                                                                             |
| Performance details           |                                                                                            |
| Max Outstanding Transactions  |                                                                                            |
| Read Bandwidth                | 77.1 GB/s peak                                                                             |
| Write Bandwidth               | 77.1 GB/s peak                                                                             |

### CSR Details

Insert a table of CSR and memory maps. 
<!--
TODO: CSRs details
-->

## Implementation Description

### Block Diagram

The L2 architecture has one AXI4 interface and one APB4 interface .

<!--
TODO: Create block diagram
-->

### Clocks and Resets
<!--
TODO: update section
-->
List clocks, resets, and draw out their networks.

### IO and Interfaces

The main interface is a full duplex AXI4 interface that is connected to the NoC. APB4 port interface will be used to communicate with the AO CSRs.


### Physical Considerations

#### Memory Details

The L2 implementation uses HS RVT 4096x128 single port SRAMs. The 16MiB capacity requires 256 macros, grouped into 16 banks of 1MiB each.\
Each bank is divided into 2 4-parallel SRAM to complete the required capacity.
- SRAM:
  - HS RVT 4096x128 single port
- Groupings:
  - Banks: 16
  - Bank capacity: 1MiB
  - SRAMs per bank: 16
    - 2 groups of 4 parallel SRAM to complete a 512-bit data width

#### Floorplanning considerations

- The large buses are the data bus to the SRAMs crossing all banks.

#### Special DFT Requirements

Are there any structures that DFT need to be aware of?
<!--
TODO: Talk with Leonidas to fill this section
-->

### Timing Exceptions

If your constraints need an exception, draw the logic, the named cells and the exception that falls out. 
<!--
TODO: fill this section
-->
