---
title: SPM Verification Plan
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# SPM Verification Plan

## Introduction

### Overview
The aim of this document is to specify how and what will be verified regarding security on Europa project.


### Ownership
Who to contact for information

|  Team              | Contact         |
| ------------------ | --------------- |
| ***Architecture*** | Spyridoula Koumousi |
| ***Design***       | Joao Martins |
| ***Verification*** | Vito Luca Guglielmi |

### Reference (TODO)
Where to find the design documentation

| Team               | Specification |
| ------------------ | ------------- |
| ***Architecture*** |[Arch Spec](https://git.axelera.ai/prod/europa/-/issues/580) FIXME|
| ***Design***       |[Block Spec](https://git.axelera.ai/prod/europa/-/issues/589)|

### Project Planning and Tracking (TODO)
Where to find project plans and trackers

|   | Link |
| - | ---- |
| ***Plan*** |[Gitlab Issues Board](https://git.axelera.ai/ai-dv-team/dv-europa-planning/SPM/-/issues)|
| ***Issues*** |[Gitlab Open Issues](https://git.axelera.ai/ai-dv-team/dv-europa-planning/SPM/-/issues)|


## Block Level Testbenches

### Testbench
#### Overview
This testbench aims to test the scratchpad memory with a serier of read and write operations. An important part of this is made also by testing the ECC functionality. Specifically it is important to test that the SPM revoers single bit erros and that signals double bit errors. This can be dpone with backdoor access to the memory. It is also important to test the hazard avoidment of the spm_controller by changing only a partial line of the memory and thus forcing the ECC to change, creating a timeframe for an hazard to happen. In that timeframe a read should be performed. 
Extensive use of the AXI VP is done in order to encapsulate these behaviours in sequences.

#### Diagram
![*Example*](img/Example_TB.drawio.png)

#### How to Run
How to check out and run

```
git clone etc.
source ....
cd ...
make ...
```
#### Regressions
Which regressions to run

| Regression | Description | Source | Link |
| ---------- | ----------- | ------ | ---- |
| regression | description | [Link to Source]() | [Last CI Run]()|

#### Metrics / Coverage Plan
VPlan / Verification IQ excel / csv file

- [Link](https://git.axelera.ai/ai-hw-team/triton/-/blob/main/verif_tb/spm/vplan/spm_vplan.csv?ref_type=heads) OLD-FIXME

## Formal Proofs
### Overview
Description of any formal environments

### How To Run

```
git clone etc.
source ....
cd ...
make ...
```

#### Regressions
Which regressions to run

| Regression | Description | Source | Link |
| ---------- | ----------- | ------ | ---- |
| regression | description | [Link to Source]() | [Last CI Run]()|

#### Metrics / Coverage Plan
VPlan / Verification IQ excel / csv file

- [Link]()

## System Level Testcases
Tests to be run at top level / Veloce

| Testcase   | Description | Source | Link |
| --------   | ----------- | ------ | ---- |
| testcase   | description | [Link to Source]()| [Last CI Run]()|

