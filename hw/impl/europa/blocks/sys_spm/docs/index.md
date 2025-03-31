---
title: Sys_Spm
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# SYS-SPM

## Table of Contents
- [SYS-SPM](#SYS-SPM)
- [Table of Contents](#table-of-contents)
- [Overview](#overview)
- [Parameters Configuration](#parameters-configuration)
- [SCP_ERR_STATUS Register](#scp_err_status-register)

## Overview

The SYS-SPM is an implementation of the SPM IP.
[Link](./../../../../../ip/spm/default/docs/index.md) to the SPM IP specification.

## Parameters Configuration

The SYS-SPM uses the following values for the top level parameters of SPM IP

| Parameter                     | Value |
| ---                           | --- |
| SPM_MEM_SIZE_KB               | 8192 |
| SPM_NB_BANKS                  | 4 |
| SPM_NB_SUB_BANKS              | 4 |
| SPM_NB_MINI_BANKS             | 4 |
| SPM_NB_SRAMS_PER_MINI_BANK    | 2 |
| SPM_NB_REQ_PIPELINE           | 3 |
| SPM_NB_RSP_PIPELINE           | 3 |
| ECC_PROTECTION_EN             | 1 |
| EN_ATOMIC_SUPPORT             | 0 |

### SCP_ERR_STATUS Register

The exposed error reporting outputs from SPM IP are captured in the SCP_ERR_STATUS register in SYS-SPM. The SCP_ERR_STATUS register consists of the following fields:

| **SCP_ERR_STATUS Field**          |  Bits   | **Error field description** |
| ---                               | ---     | --- |
| ECC_ERR_PRESENT                   | [0]     | An ECC error has been reported -- 0: no error present / 1: an error has been seen |
| ECC_ERR_TYPE                      | [1]     | 0: single bit error (CORRECTABLE) / 1 : Double bit error (UNRECOVERABLE) |
| ECC_ERR_SYNDROME                  | [9:2]   | The ECC error syndrome. SW ca n calculate the location of the error based on the syndrome. |
| ECC_ERR_INDEX                     | [29:10] | 64-bit aligned memory address in which the error occurred. |
