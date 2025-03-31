---
title: Block Microarchitecture Template
doc: 
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# <Block or IP Name> Microarchitecture

## Introduction

One line introduction of the block. Why is this block needed.

### Abbreviations

List all acronyms and abbreviations used in the text of this document.

### Overview

Describe what the purpose of the block / IP is.

What does it do? and what are the high level use cases? Refer to the Arch Spec where appropriate.
 
### System Diagram

Show the Block / IP within the system setting. 


## Functional Description

One small paragraph describing the salient features of the block along with a functional block diagram.

Break down design into sub-blocks. Describe the SW <> HW interface for the block at hand and in sub blocks if appropriate.

### sub-block 1

For each feature/ sub block, explain it's purpose.

Link to architectural requirements where appropriate.


### sub-block 2

For each feature/ sub block, explain it's purpose.

Link to architectural requirements where appropriate.

This section should be detailed enough for verification to determine a test plan for the block and it's features.


## Integration Specifics

Short description of integration quirks if any.

### DFT considerations

Information about special structures, isolations etc.

### IO and Interfaces

Give a list of IO and Interfaces to the design.

Details of all the standardised protocol interfaces and their supported feature set.

Example timing diagrams of non-standard (in-house) protocols.

#### Clocks and Resets

List clocks, resets, and draw out their networks.

#### Observability signals

List observable signals and their controls, programming etc

#### Interrupts

List interrupts sent or received by this block, their intended use and information about masking.

### CSR Details

Indicate this blocks place in the global memory map. 

Specify the size this IP occupies in global memory map.

Insert a table of CSR and internal memory map.

### Memory Details

- Sizes
- Groupings


## Verification hints

Microarchitecturally interesting verification corners.

### Performance Requirements

List all measurable performance requirements for verification.

<!--- As explained in prod/europa#907 --->

The list must include all of the below at the minimum.

- Start-up Latency
- Response Latency
- Serialization Throughput
- B2B Throughput
- Max Outstanding


## Physical design guidance

Describe expected difficult paths, mutually exclusive circuitry (for clock gating) etc.

### Floorplanning considerations

Large Buses connected to which sub blocks

Hard placement requirements for any macros

Proximity (or regioning) ideas

### Timing Exceptions

If your constraints need an exception, draw the logic, the named cells and the exception that falls out.



