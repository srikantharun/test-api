# Europa Architecture Template Specification

## Requirements

Choice of the requirements ID is done based on the following.

| Requirements | ID     |
| ------------ | ------ |
| Related to use cases. | BLOCK_0xx |
| Related to subsystem. | BLOCK_1xx |
| Related to toplevel integration | BLOCK_2xx |
| Related to design (FE/PD) | BLOCK_3xx |
| Related to PPA | BLOCK_4xx |

| Requirement ID | Description     | Comment    | Review Status |
| -------------- | --------------- | ---------- | ------------- |
|                |                 |            |               |


## Block Definition

### Block Description

Short Description of the Block.

### Block Diagram

Block Diagram detailing the full interface and the internal architecture.


### Block Interfaces

Details of all the standardised protocol interfaces and their supported feature set.

## Block Integration

Description and block-diagram indicating how the block is to be integrated at the top level.

## Description of use-cases

### General Description
	
Summarize the typical use cases

### Memory Usage

Describe which memories store which data in which scenarios.

### Booting

If the block contains one or multiple cores, describe how the are booted.

### Configuration

Describe how the block is configured (both local CSR's and top level sidebands).

### Runtime Interations

Describe the used clock gating mechanisms and how they are controlled.

### Power Management

Describe the used clock-gating mechanisms and how they are controlled.
