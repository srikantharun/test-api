---
title: DMA IP Functional Specification
doc: 
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---


# Introduction

A DMA is a hardware module whose purpose is to move data from a source location to a destination location without direct involvement of the CPU. 

To do this, SW must instruct the DMA controller what to move. These instructions are wrpped up into a data structure called a descriptor.

The basic components of a DMA are:

| Component      | Description                                                |
| -------------- | ---------------------------------------------------------- |
| Port           | A means to access the devices infrastructure to read and write data as part of the copy. |
| Channel        | An entity that processes a single descriptor at a time. A DMA can have more than 1 channel allowing mutiple descriptors to be processed concurrently.   |
| Buffer         | A data buffer to store response data from read transactions before being consumed in write transactions |



# DMA uArch

## Source side allocation



