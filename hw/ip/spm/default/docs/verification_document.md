---
title: SPM Verification Specification
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# SPM Verification Specification

## Introduction

### Overview

The ScratchPad Memory (SPM) is used in Europa to contain sensible code to be executed. Because of this sensible nature, the SPM also allows to enable ECC for 1 bit correction 2 bit detection.


### Ownership
Who to contact for information

|  Team              | Contact         |
| ------------------ | --------------- |
| ***Architecture*** | Spyridoula Koumousi|
| ***Design***       | Joao Martins|
| ***Verification*** | Vito Luca Guglielmi|

### Reference
Where to find the design documentation

| Team               | Specification |
| ------------------ | ------------- |
| ***Architecture*** |[Arch Spec](https://axeleraai.atlassian.net/wiki/spaces/archrd/pages/399835388/SYS-SPM)|
| ***Design***       |[Block Spec]()|

### Project Planning and Tracking
Where to find project plans and trackers

|   | Link |
| - | ---- |
| ***Plan*** |[Gitlab Issues Board](https://git.axelera.ai/prod/europa/-/boards/258?label_name[]=block%3Asys-spm)|
| ***Issues*** |[Gitlab Open Issues](https://git.axelera.ai/prod/europa/-/issues/?sort=updated_desc&state=opened&label_name%5B%5D=block%3Aspm&first_page_size=20)|

## Verification strategy

The IP will be mostly verified with UVM.
A TB is already present in Triton. It will be ported to Europa integrating AXI instead of AHB and adding the new interface signals.
The AXI protocol will be handled with the Synopsis AMBA VIP and it will also check the correctness of the protocol. 
The memory will be tested with multiple approaches. 

A model memory will be used for scoreboarding. 

When a write happens it will go both to the SPM and to the model, then, on the read, it will be possible to check the DUT value against the model.
In order to reduce the randomness, the memory will be treated as several small memories, splitting the address space in multiple spaces.
This will allow each test sequence to operate on a smaller memory and thus having better chances to catch values previously written.
A "full memory" test will also be present.
Directed tests with backdoor access to the memory will be used to initialize the values and then read them.
Finally the ECC behaviour will be tested with backdoor access in order to modify some values. Both for full and partial operations.

A check at the end of each test should be added to verfy that the values are the expected ones.

## Block Level Testbenches

The block level testbench will be the core of the verification, providing reusable sequences to be used on higher level. It should adapt to different sizes of the memory and both with ECC enabled and not.

## System level testbench
#### Overview

The system level testbench should reuse the ip tb and then add the CRS and the JTAG interface.


#### Diagram


#### How to Run
TODO
How to check out and run

```
git clone etc.
source ....
cd ...
make ...
```
#### Regressions
TODO
Which regressions to run

| Regression | Description | Source | Link |
| ---------- | ----------- | ------ | ---- |
| regression | description | [Link to Source]() | [Last CI Run]()|

#### Metrics / Coverage Plan
TODO

##### Tests



- [Testlist](/verifsdk/tests_spm.yaml)

##### Coverage

TODO: link to the coverage configuration file
- [Coverage plan]()

## Formal Proofs
TODO
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
