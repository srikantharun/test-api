---
title: Baseband Interfaces
doc:
  status: draft
  version: [0, 0, 3]
  confidentiality: internal
---


# Baseband Interfaces

The NoC interfaces with the following blocks:

* APU
* AI Cores (x8)
* SDMAs (x2)
* PVE (x2)
* Decoder
* SOC-MGMT
* SOC-PERIPH
* SYS-SPM
* L2 (x8)
* LPDDR (x8)

Every Europa Block interacts with the NoC over AXI4, APB3 & APB4 baseband socket protocols, in fully-synchronous interfaces. At the NoC side, a Network Interface Unit (NIU) handles the conversion of the Socket Protocol (AXI/APB) to the internal NoC packetized protocol and back. Initiator NIUs expose a NoC Subordinate Port externally, which is connected to an external Manager Port. Target NIUs expose a NoC Manager Port externally, which is connected to an external Subordinate Port.


## Traffic Classes

Each Interface is assigned a **Traffic Class** depending on the type of data flowing through its bus: Streaming, Control, Configuration or a mixture of those. Depending on the Architectural Requirements for this Interface and Traffic Class, a Data Bus Width (DW) range is assigned per Traffic class, as in the following table:

| Traffic Class | Traffic type | Name | DW
| ------------: | ------------ | ---- | ---:
| **HT**        | Streaming | High-Throughput | 512 or 256
| **MT**        | Streaming and Control | Mixed-Throughput | 256 or 128
| **LT**        | Control | Low-Throughput | 64
| **Cfg**       | Configuration | IP Configuration | 32
| **SysCfg**    | PPMU Configuration (aka AO CSRs) | System Configuration | 32


## Clocks

Each Interface is assigned a **Clock** from the following list:

| Clock    | Frequency | Comments
| -------- |---------- | --------
| Ref      | 50MHz     | Ref clock
| Fast     | 1200MHz   | Primary High-Performance
| Codec    | 600MHz    | Codec (aka Decoder)
| eMMC     | 200MHz    | eMMC SOC-PERIPH (unused in the NoC)
| Periph   | 100MHz    | Peripherals
| DDR East | 800MHz    | DDR East Ref
| DDR West | 800MHz    | DDR West Ref

Most Interfaces are clocked at the Fast Clock except from:

* LPDDR: clocked at the core DDR clock
* Decoder: clocked at both the Codec and the Fast clock
* SOC-PERIPH: clocked at the Periph clock

[Source: https://git.axelera.ai/prod/europa/-/issues/251 accessed at Fri, Jun 21, 2024]

Note that the inner NoC logic (links, buffers, switches etc) runs at the **Fast** clock.

<!-- (TODO; psarras; change this table to point to the official clock docs once they're in) -->

## Interfaces

Below tables list all interfaces connected to the NoC per Block. Note that:

* The **Type** column indicates the _external_ port type & direction. The NoC interface attached to this port will be of the _inverse_ direction (e.g. an AXI-M Block port shall connect to an AXI-S NoC port etc).
* The **Clock** column indicates the "canonical" clock frequency of that interface, according to the [Clock Frequencies](#clock-frequencies) table above.
* The **Domain** column indicates the Clock Domain of every interface. For every clock domain, a dedicated **clock/reset pair** is assumed, that's independent from every other. More details in [Clock & Reset Architecture](clocks-resets-fences.md). Every block requires at least 2 Clock Domains:
    1. An Always-On (AON) domain, serving the SysCfg interface
    2. One (or more) Fenceable domain(s) that can be individually reset/gated
        * All Blocks only need a single Fenceable domain, **except from** the Decoder (aka Codec) block that needs 2
* The **Addressing** column indicates _Relative_ or _Absolute_ addressing for _Subordinate_ Ports:
    * When _Absolute_, the NoC retains the Subordinate's offset (starting address) in the request address
    * When _Relative_, the NoC strips off the Subordinate's offset (starting address) from the request
    * All Initiators assumed to use Absolute addresses.
* The **Duplex** column indicates whether the AXI Writes and Reads can be served in parallel or are serialized. Specifically;
  *  **Half**-Duplex NIUs serialize Writes and Reads and can only serve one of them in a given time window
    * **Full**-Duplex NIUs can process a Write and a Read at the same time

### APU

| Name                       | Type   |  DW   | AXI-IDW  | Clock | Domain  | Addressing | Duplex | Description
| -------------------------- | ------ | ----: | -------: | :---- | ------- | ---------- | ------ |------------
| `apu_init_mt`              | AXI4-M | 256   |    9     | Fast  | APU | Absolute   | Full   |  MT Initiator
| `apu_init_lt`              | AXI4-M | 64    |   10     | Fast  | APU | Absolute   | Half   | LT Initiator
| `apu_targ_lt`              | AXI4-S | 64    |    8     | Fast  | APU | Absolute   | Half   | LT Target
| `apu_targ_syscfg`          | APB4-S | 32    |    -     | Ref   | APU AON | Relative   | -      | SysCfg Target


### AI Core (x8)

| Name                | Type   |  DW   | AXI-IDW  | Clock | Domain          | Addressing | Duplex | Description
| ------------------- | ------ | ----: | -------: | ----- | --------------- | ---------- | ------ |------------
| `aic_$_init_ht`     | AXI4-M | 512   |    9     | Fast  | AI Core `$` | Absolute   | Full   | HT Initiator
| `aic_$_init_lt`     | AXI4-M | 64    |    9     | Fast  | AI Core `$` | Absolute   | Half   | LT Initiator
| `aic_$_targ_lt`     | AXI4-S | 64    |    6     | Fast  | AI Core `$` | Absolute   | Half   | LT Target
| `aic_$_targ_syscfg` | APB4-S | 32    |    -     | Ref   | AI Core `$` AON | Relative   | -      |  SysCfg Target


### SDMA (x2)

| Name                 | Type   |  DW   | AXI-IDW  | Clock | Domain       | Addressing | Duplex | Description
| -------------------- | ------ | ----: | -------: | :---- | ------------ | ---------- | ------ |-----------
| `sdma_$_init_ht_0`   | AXI4-M | 512   |    8     | Fast  | SDMA `$` | Absolute   | Full   | HT Initiator 0
| `sdma_$_init_ht_1`   | AXI4-M | 512   |    8     | Fast  | SDMA `$` | Absolute   | Full   | HT Initiator 1
| `sdma_$_init_lt`     | AXI4-M | 64    |    4     | Fast  | SDMA `$` | Absolute   | Half   | LT Tracing Initiator
| `sdma_$_targ_lt`     | AXI4-S | 64    |    4     | Fast  | SDMA `$` | Relative   | Half   | LT Configuration & Tracing Target
| `sdma_$_targ_syscfg` | APB4-S | 32    |    -     | Ref   | SDMA `$` AON | Relative   | -      | SysCfg Target


### PVE (x2)

| Name                | Type   |  DW   | AXI-IDW  | Clock | Domain      | Addressing | Duplex | Description
| ------------------- | ------ | ----: | -------: | :---- | ----------- | ---------- | ------ |-----------
| `pve_$_init_ht`     | AXI4-M | 512   |   11     | Fast  | PVE `$` | Absolute   | Full   | HT Initiator
| `pve_$_init_lt`     | AXI4-M | 64    |   8      | Fast  | PVE `$` | Absolute   | Full   | LT Initiator
| `pve_$_targ_lt`     | AXI4-S | 64    |   4      | Fast  | PVE `$` | Absolute   | Half   | LT Target
| `pve_$_targ_syscfg` | APB4-S | 32    |   -      | Ref   | PVE `$` AON | Relative   | -      | SysCfg Target


### L2 (x8)

| Name               | Type   |  DW   | AXI-IDW  | Clock | Domain     | Addressing | Duplex | Description
| ------------------ | ------ | ----: | -------: | :---- | ---------- | ---------- | ------ | -----------
| `l2_$_targ_ht`     | AXI4-S | 512   |    4     | Fast  | L2 `$` | Relative   | Full   | HT Initiator
| `l2_$_targ_syscfg` | APB4-S | 32    |    -     | Ref   | L2 `$` AON | Relative   | -      | SysCfg Target


### LPDDR West PLL

| Name                            | Type   |  DW   | AXI-IDW  | Clock    | Domain       | Addressing | Duplex | Description
| ------------------------------- | ------ | ----: | -------: | :------- | ------------ | ---------- | ------ | -----------
| `ddr_wpll_targ_syscfg`         | APB4-S | 32    |   -      | Ref      | DDR West PLL AON | Relative   | -      | SysCfg Target



### LPDDR West (Graph) (x4)

| Name                            | Type   |  DW   | AXI-IDW  | Clock    | Domain       | Addressing | Duplex | Description
| ------------------------------- | ------ | ----: | -------: | :------- | ------------ | ---------- | ------ | -----------
| `lpddr_graph_$_targ_ht`         | AXI4-S | 256   |   8      | DDR West | LPDDR West Data | Relative   | Half   | HT Target
| `lpddr_graph_$_targ_cfg`        | APB3-S | 32    |   -      | DDR West | LPDDR West Cfg | Relative   | -      | Configuration Target
| `lpddr_graph_$_targ_syscfg`     | APB4-S | 32    |   -      | Ref      | LPDDR West AON | Relative   | -      | SysCfg Target


### LPDDR East (PPP) (x4)

| Name                          | Type   |  DW   | AXI-IDW  | Clock    | Domain       | Addressing | Duplex | Description
| ----------------------------- | ------ | ----: | -------: | :------- | ------------ | ---------- | ------ | -----------
| `lpddr_ppp_$_targ_mt`         | AXI4-S | 256   |    8     | DDR East | LPDDR East Data | Relative   | Half   | MT Target
| `lpddr_ppp_$_targ_cfg`        | APB3-S | 32    |    -     | DDR East | LPDDR East Cfg | Relative   | -      | Configuration Target
| `lpddr_ppp_$_targ_syscfg`     | APB4-S | 32    |    -     | Ref      | LPDDR East AON | Relative   | -      | SysCfg Target


### Decoder (Codec)

| Name                   | Type   |  DW   | AXI-IDW  | Clock | Domain            | Addressing | Duplex | Description
| ---------------------- | ------ | ----: | -------: | :---- | ----------------- | ---------- | ------ | -----------
| `dcd_dec_0_init_mt`    | AXI4-M | 128   |    5     | Codec | Decoder Codec | Absolute   | Full   | MT Initiator 0 (Decoder data)
| `dcd_dec_1_init_mt`    | AXI4-M | 128   |    5     | Codec | Decoder Codec | Absolute   | Full   | MT Initiator 1 (Decoder data)
| `dcd_dec_2_init_mt`    | AXI4-M | 128   |    5     | Codec | Decoder Codec | Absolute   | Full   | MT Initiator (Post process data)
| `dcd_mcu_init_lt`      | AXI4-M | 128   |    5     | Fast  | Decoder MCU   | Absolute   | Full   | LT Initiator (CPU data)
| `dcd_targ_cfg`         | APB4-S | 32    |    -     | Codec | Decoder Codec | Relative   | -      | Cfg Target
| `dcd_targ_syscfg`      | APB4-S | 32    |    -     | Ref   | Decoder AON   | Relative   | -      | SysCfg Target

### PCIe

| Name                       | Type   |  DW   | AXI-IDW  | Clock  | Domain          | Addressing | Duplex | Description
| -------------------------- | ------ | ----: | -------: | :----- | --------------- | ---------- | ------ | -----------
| `pcie_init_mt`             | AXI4-M | 128   |    7     | Codec  | PCIe Init | Absolute   | Full   | MT Initiator (Host + DMA)
| `pcie_targ_mt`             | AXI4-S | 128   |    6     | Codec  | PCIe Targ | Absolute   | Full   | MT Target (Host)
| `pcie_targ_cfg_dbi`        | AXI4-S | 32    |    4     | Periph | PCIe DBI  | Relative   | -      | Cfg Target - DBI port
| `pcie_targ_cfg`            | APB3-S | 32    |    -     | Periph | PCIe Cfg  | Relative   | -      | Cfg Target (Configuration Traget (CTL and PHY))
| `pcie_targ_syscfg`         | APB4-S | 32    |    -     | Ref    | PCIe AON  | Relative   | -      | SysCfg Target


### SOC-MGMT

| Name                       | Type   |  DW   | AXI-IDW  | Clock  | Domain       | Addressing | Duplex | Description
| -------------------------- | ------ | ----: | -------: | :----- | ------------ | ---------- | ------ | -----------
| `soc_mgmt_init_lt`         | AXI4-M | 64    |    4     | Periph | SOC-MGMT | Absolute   | Half   | LT Initiator
| `soc_mgmt_targ_lt`         | AXI4-S | 64    |    4     | Periph | SOC-MGMT | Absolute   | Half   | LT Target
| `soc_mgmt_targ_syscfg`     | APB4-S | 32    |    -     | Ref    | SOC-MGMT AON | Relative   | -      | SysCfg Target


### SOC-PERIPH

| Name                       | Type   |  DW   | AXI-IDW  | Clock  | Domain         | Addressing | Duplex | Description
| -------------------------- | ------ | ----: | -------: | :----- | -------------- | ---------- | ------ | -----------
| `soc_periph_init_lt`       | AXI4-M | 64    |    4     | Periph | SOC-PERIPH | Absolute   |  Half  | LT Initiator
| `soc_periph_targ_lt`       | AXI4-S | 64    |    4     | Periph | SOC-PERIPH | Absolute   |  Half  | LT Target
| `soc_periph_targ_syscfg`   | APB4-S | 32    |    -     | Ref    | SOC-PERIPH AON | Relative   |  -     | SysCfg Target


### SYS-SPM

| Name                       | Type   |  DW   | AXI-IDW  | Clock | Domain      | Addressing |  Duplex | Description
| -------------------------- | ------ | ----: | -------: | :---- | ----------- | ---------- |  ------ | -----------
| `sys_spm_targ_lt`          | AXI4-S | 64    |    4     | Fast  | SYS-SPM | Relative   |   Half  | LT Target (Memory)
| `sys_spm_targ_syscfg`      | APB4-S | 32    |    -     | Ref   | SYS-SPM AON | Relative   |   -     | SysCfg Target
