---
title: SW tests for KSE 3 verification plan
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# SW tests for KSE 3 verification plan

## Introduction

### Overview
The aim of this testcases is to verify that commands for KSE 3 are successfully done and return the expected value.
There are several commands that need to be executed using KSE 3. Here is the list:
 - AES
 - Sponge AEAD
 - SHA
 - HMAC SHA
 - Key derivation

In the image we can see that we only need the APU to have a C test (preloaded on SPM) that will communicate with KSE 3 to then check if the commands requested were correctly implemented.

#### Diagram
![*Block level connections for KSE 3 commands verification*](img/APU_connect_KS3.jpg)

#### Pre-requisites
 - KSE 3 ROM [link gitlab issue]()
 - Testbench environment structure created to allow KSE3 testing [link gitlab issue]()
 - List of commands to be tested [link list of scenarios]()

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

### Project Planning and Tracking (TODO)
|   | Link |
| - | ---- |
| ***Plan*** |[Gitlab Issues Board](https://git.axelera.ai/ai-dv-team/dv-europa-planning/SECURITY/-/issues/2)|
| ***Issues*** |[Gitlab Open Issues](https://git.axelera.ai/ai-dv-team/dv-europa-planning/SECURITY/-/issues/11)|

## Testcases

Tests to be run at top level / Veloce

| Testcase   | Description | Source | Link |
| --------   | ----------- | ------ | ---- |
| sec_kse_aes_encrypt  | Verify KSE AES encryption command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_aes_decrypt  | Verify KSE AES decryption command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_sponge_encrypt | Verify KSE Sponge AEAD encryption command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_sponge_decrypt | Verify KSE Sponge AEAD decryption command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_HMAC  | Verify KSE HMAC command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_SHA  | Verify KSE SHA command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_ECDSA | Verify KSE ECDSA command on random data | [Link to Source]()| [Last CI Run]()|
| sec_kse_GenerateMasterSecretKey  | Verify KSE is able to complete the command GenerateMasterSecretKey correctly | [Link to Source]()| [Last CI Run]()|
| sec_kse_SetGetLifecycle  | Verify KSE is able to complete the command Set/GetLifeCycle for all stages correctly | [Link to Source]()| [Last CI Run]()|
| sec_kse_ImportKey  | Verify KSE is able to complete the command ImportKey correctly | [Link to Source]()| [Last CI Run]()|
| sec_kse_RamInUseNotAccessible | Verify that when KSE is occupied running a command, the Data RAM is not accessible | [Link to Source]()| [Last CI Run]()|
| sec_kse_OTP_restricted_area | Verify that using KSE commands is possible to write and read from OTP (restricted area) | [Link to Source]()| [Last CI Run]()|
| sec_kse_OTP_host_area | Verify that using KSE commands is not possible to write and read from OTP (host area) | [Link to Source]()| [Last CI Run]()|
| sec_kse_AO_register | Verify that is possible to access AO registers using KSE commands | [Link to Source]()| [Last CI Run]()|
| sec_kse_fw | Verify that is possible to load a FW in IRAM from KSE using KSE commands | [Link to Source]()| [Last CI Run]()|
| sec_kse_interrupt | Verify that when a command has finished, the interrupt_o is raised | [Link to Source]()| [Last CI Run]()|
| sec_kse_lifecycle_test | Verify that is possible to set lifecycle from WAFER_TEST until EOL | [Link to Source]()| [Last CI Run]()|

## Useful links
 - [Security Verification Plan Document](index.md)
