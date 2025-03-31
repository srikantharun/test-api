---
title: Release Notes
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# Release Notes

## Version 1.5

* Date: 2025.01.27
* MR: [!2859](https://git.axelera.ai/prod/europa/-/merge_requests/2859)
* Affects: All partitions, incl. Top

1. Integrated the Token Network -- new I/Os
2. Fixed missing connections from SOC-MGMT/-PERIPH towards L2 HT

## Version 1.2b

* Date: 2025.01.22
* MR: [!2800](https://git.axelera.ai/prod/europa/-/merge_requests/2800)
* Affects: **All** partitions' constraints

1. Remove Async registers references in partitions that don't have async (East & West)

## Version 1.2

* Date: 2025.01.20
* MR: [!2765](https://git.axelera.ai/prod/europa/-/merge_requests/2765)
* Affects: **All** partitions **except** (East, West, DDR-West & Top)

1. Connectivity Matrix Complete

## Version 1.1

* Date: 2025.01.10
* MR: [!2641](https://git.axelera.ai/prod/europa/-/merge_requests/2641)
* Affects: **All** partitions

1. NIU Logic modifications to fix functional bug on L2 interleaving of 2x4/4k [#2224](https://git.axelera.ai/prod/europa/-/issues/2224)
2. `apu_clk/_clken/_rst_n` renaming -- fixes [#2298](https://git.axelera.ai/prod/europa/-/issues/2298)
    * **Constraints Update**: Renamed `apu_clk` clock definition to `apu_x_clk`
    * **I/O change**: APU clock/clock-enable & reset pins renamed from `i_apu_clk/_clken/_rst_n` to `i_apu_x_clk/_x_clken/_x_rst_n`


## Version 1.0

* Date: 2024.12.19
* MR: [!2558](https://git.axelera.ai/prod/europa/-/merge_requests/2558)
* Affects: **South** partition

1. South Topology refactoring -- [wi:#2095](https://git.axelera.ai/prod/europa/-/work_items/2095)
   * See the details/docs in [#2095#note_288573](https://git.axelera.ai/prod/europa/-/work_items/2095#note_288573)


## Version 0.9

* Date: 2024.12.16
* MR: [!2502](https://git.axelera.ai/prod/europa/-/merge_requests/2502)
* Affects: **Center** & **SoC** partitions

1. Center Topology refactoring -- [wi:#2096](https://git.axelera.ai/prod/europa/-/work_items/2096)
   * More pessimistic distance pipelining (1 pipe / 800u)
   * Criss-crossing of wires occurs only in wide corridors
   * All switching occurs in the middle
2. Extend by +1b the IDs used for Exclusives in PVEs -- [wi:#2239](https://git.axelera.ai/prod/europa/-/work_items/2239)


```
| Partition | v0.9 Release Directory
| --------- | -----------------------
| SoC       | /data/releases/europa/noc/noc_soc/202412161551-v0.9
| Center    | /data/releases/europa/noc/noc_v_center/202412161551-v0.9
| Top       | /data/releases/europa/noc/noc_top/202412161553-v0.9
```

## Version 0.8.5

* Date: 2024.12.11
* MR: [!2470](https://git.axelera.ai/prod/europa/-/merge_requests/2470)
* Affects: **SoC** + **Top** partitions

1. Change the AXI ID (`*id`) Width for Init LT and Targ LT interfaces
    * `*_apu_init_lt_*_id`: 10b (was 8b)
    * `*_apu_targ_lt_*_id`: 8b (was 10b)


## Version 0.8

* Date: 2024.12.11
* MR: [!2429](https://git.axelera.ai/prod/europa/-/merge_requests/2429)
* Affects All Partitions

1. Align North Topology with floorplan v11 + refactor it for less wire spaghetti [#2094](https://git.axelera.ai/prod/europa/-/work_items/2094)
   1. **I/O Impact** +1b on **all** `_data` NoC bundles (because of the extended Header, to support more Exclusives)
   2. Affects **all** partitions including Top
2. Connectivity fix for bug [#2115](https://git.axelera.ai/prod/europa/-/issues/2115): routed missing PVE-1 HT WR -> L2-7 HT WR
3. Topology perf-bug fix at the SoC partition [#2076](https://git.axelera.ai/prod/europa/-/work_items/2076)
4. Extend outstanding exclusive accesses for APU & PVE


```
| Partition | v0.8 Release Directory
| --------- | -----------------------
| DDR-East  | /data/releases/europa/noc/noc_ddr_east/202412120827-v0.8
| DDR-West  | /data/releases/europa/noc/noc_ddr_west/202412120827-v0.8
| East      | /data/releases/europa/noc/noc_h_east/202412120827-v0.8
| North     | /data/releases/europa/noc/noc_h_north/202412120827-v0.8
| West      | /data/releases/europa/noc/noc_h_west/202412120827-v0.8
| SoC       | /data/releases/europa/noc/noc_soc/202412120827-v0.8
| Top       | /data/releases/europa/noc/noc_top/202412120827-v0.8
```


## Version 0.7c

* Date: 2024.12.05
* MR: [!2408](https://git.axelera.ai/prod/europa/-/merge_requests/2408)

This Version only modifies **constraints**. It **affects** all NoC sub-partitions _except_ West, East & Top.

1. Modified `idle_req` constraint -- re-fix for [#2001](https://git.axelera.ai/prod/europa/-/issues/2001)
    * `idle_req` inputs: replaced 8-cycle MCP in `internalConstraints.sdc` with a 4-cycle `set_max_delay`

```
| Partition | v0.7c Release Directory
| --------- | -----------------------
| DDR-East  | /data/releases/europa/noc/noc_ddr_east/202412091047-v0.7c
| DDR-West  | /data/releases/europa/noc/noc_ddr_west/202412091047-v0.7c
| SoC       | /data/releases/europa/noc/noc_soc/202412091047-v0.7c
```


## Version 0.7b

* Date: 2024.11.27
* MR: [!2295](https://git.axelera.ai/prod/europa/-/merge_requests/2295)

This Version only modifies **constraints**. It **affects** all NoC sub-partitions _except_ West, East & Top.

1. Removed `set_max_delay` constraint on non-existent pins (**bug** of the v0.7 constraints!)
2. Relaxed constraints on `idle_req` constraint to fix [#2001](https://git.axelera.ai/prod/europa/-/issues/2001) -- **affects**: all sub-partitions except West & East
    * Replaced single-cycle `set_max_delay` constraint on `idle_req` inputs with an 8-cycle MCP in `internalConstraints.sdc`
3. Relaxed CDC constraints to fix [#1993](https://git.axelera.ai/prod/europa/-/issues/1993)
    * Ignore clock latency by adding the `-ignore_clock_latency` switch to the `set_max_delay` constraint
    * Subtracts `2 x CDC_MAX_SKEW_*` from the `set_max_delay` value
    * Eventually, it must be **verified** that the skew among _sending_ and _receiving_ flops can't exceed `2 x CDC_MAX_SKEW_*`
4. Document pin placement constraints in [Pin Placement](./pin-placement.md)
5. Updated connectivity CSV to simplify its entries

```
| Partition | v0.7b Release Directory
| --------- | -----------------------
| DDR-East  | /data/releases/europa/noc/noc_ddr_east/202411291220-v0.7b
| DDR-West  | /data/releases/europa/noc/noc_ddr_west/202411291220-v0.7b
| SoC       | /data/releases/europa/noc/noc_soc/202411291220-v0.7b
```


## Version 0.7

* Date: 2024.11.22
* MR: [!2248](https://git.axelera.ai/prod/europa/-/merge_requests/2248)

## Summary

* Update with PD floorplan v11 and align topology accordingly - [#1518](https://git.axelera.ai/prod/europa/-/issues/1518)
* Added DDR West PLL APB Interface - [#1622](https://git.axelera.ai/prod/europa/-/issues/1622)
* Extend SOC-MGMT SysCfg PADDR to 19b - [#1990](https://git.axelera.ai/prod/europa/-/issues/1990)
* Add one clk/rst/clken per PCIe Interface - [#1952](https://git.axelera.ai/prod/europa/-/issues/1952)
* Add one Fence per PCIe Interface - [#1670](https://git.axelera.ai/prod/europa/-/issues/1670)
* Add a 2nd Fence to LPDDR - 1 for AXI, 1 for APB - [#1936](https://git.axelera.ai/prod/europa/-/issues/1936)
* Add a SOC-MGMT Fence - [#2048](https://git.axelera.ai/prod/europa/-/issues/2048)
* Align memory map with latest Europa one - [#1845](https://git.axelera.ai/prod/europa/-/issues/1845)
* Add some new connections for - part of [#1792](https://git.axelera.ai/prod/europa/-/issues/1792)
* Makw SOC-PERIPH Targ LT accessible by most of INITs - [#1906](https://git.axelera.ai/prod/europa/-/issues/1906)
* Add an extra 512b FD NoC link towards LPDDRs to North/South - [#1947](https://git.axelera.ai/prod/europa/-/issues/1947)
* Fix West & SoC memory configuration & reduce macro banks - [#1946](https://git.axelera.ai/prod/europa/-/issues/1946)


## Per sub-partition


### Center

* I/O change: -5b on all `*_dp_*_data` pins
* New I/O
    * `*_dp_lnk_cross_north_to_center_512_a_*`
    * `*_dp_lnk_cross_north_to_center_512_b_*`
    * `*_dp_lnk_cross_south_to_center_512_a_*`
    * `*_dp_lnk_cross_south_to_center_512_b_*`


### DDR-East

* I/O change: -5b on all `*_dp_*_data` pins
* New I/O:
    * `*_lpddr_ppp_0_cfg_pwr_idle_*`
    * `*_lpddr_ppp_1_cfg_pwr_idle_*`
    * `*_lpddr_ppp_2_cfg_pwr_idle_*`
    * `*_lpddr_ppp_3_cfg_pwr_idle_*`
* Constraints: new clock for `cfg` interface -- assumed synchronous to AXI clock

### DDR-West

* I/O change: -5b on all `*_dp_*_data` pins
* New clk/rst
    * `*_ddr_wpll_aon_clk`
    * `*_ddr_wpll_aon_rst_n`
* New I/O
    * `*_ddr_wpll_targ_syscfg_apb_m_*`
    * `*_lpddr_graph_0_cfg_pwr_idle_*`
    * `*_lpddr_graph_1_cfg_pwr_idle_*`
    * `*_lpddr_graph_2_cfg_pwr_idle_*`
    * `*_lpddr_graph_3_cfg_pwr_idle_*`
* Constraints: new clock for `cfg` interface -- assumed synchronous to AXI clock

### North

* I/O change: -5b on all `*_dp_*_data` pins
* New I/O
    * `*_dp_lnk_cross_north_to_center_512_a_*`
    * `*_dp_lnk_cross_north_to_center_512_b_*`
    * `*_dp_lnk_cross_south_to_center_512_a_*`
    * `*_dp_lnk_cross_south_to_center_512_b_*`

### South

* I/O change: -5b on all `*_dp_*_data` pins
* New I/O
    * `*_dp_lnk_cross_north_to_center_512_a_*`
    * `*_dp_lnk_cross_north_to_center_512_b_*`
    * `*_dp_lnk_cross_south_to_center_512_a_*`
    * `*_dp_lnk_cross_south_to_center_512_b_*`

### East

* I/O change: -5b on all `*_dp_*_data` pins

### SoC

* I/O change: -5b on all `*_dp_*_data` pins
* Removed clk/rst/clen
  *  `*_pcie_init_mt_clk`/`_clken`/`_rst_n`
* New clk/rst
    * `i_pcie_init_mt_clk`/`_clken`/`_rst_n`
    * `i_pcie_targ_mt_clk`/`_clken`/`_rst_n`
    * `i_pcie_targ_cfg_clk`/`_clken`/`_rst_n`
    * `i_pcie_targ_cfg_dbi_clk`/`_clken`/`_rst_n`
* Removed I/O
    * `*_pcie_pwr_idle_*`
* New I/O
    * `*_pcie_init_mt_pwr_idle_*`
    * `*_pcie_targ_mt_pwr_idle_*`
    * `*_pcie_targ_cfg_pwr_idle_*`
    * `*_pcie_targ_cfg_dbi_pwr_idle_*`
    * `*_soc_mgmt_pwr_idle_*`
* Constraints: New clock definitions for PCIe clocks (one clock/reset per PCIe interface)
* Macros: 116 in total vs 156 in v0.6.1 -- see details in [Memory Macros](./memory-macros.md)

### West

* I/O change: -5b on all `*_dp_*_data` pins
* Macros: 32 in total vs 16 in v0.6.1 -- see details in [Memory Macros](./memory-macros.md)

```
| Partition | v0.7 Release Directory
| --------- | -----------------------
| DDR-East  | /data/releases/europa/noc/noc_ddr_east/202411260901-v0.7
| DDR-West  | /data/releases/europa/noc/noc_ddr_west/202411260909-v0.7
| West      | /data/releases/europa/noc/noc_h_west/202411260910-v0.7
| East      | /data/releases/europa/noc/noc_h_east/202411260911-v0.7
| SoC       | /data/releases/europa/noc/noc_soc/202411260912-v0.7
| Top       | /data/releases/europa/noc/noc_top/202411260913-v0.7
```


## Version 0.6.1

* Date: 2024.10.29
* MR: [Europa!1993](https://git.axelera.ai/prod/europa/-/merge_requests/1993)

| \# | Change         | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | V-Center | Top
| -- | -------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | -------- | ---
| 1  | SoC hierarchy  |    -     |     -    |   -    |    -    |    -    |   -    | yes |     -    |  -

1. Restore SoC hierarchy by removing `*_grid_*` modules completely

| Partition | v0.6 Release Directory
| --------- | -----------------------
| SoC       | `/data/releases/europa/noc/noc_soc/202410300952`

## Version 0.6

* Date: 2024.10.25
* MR: [Europa!1944](https://git.axelera.ai/prod/europa/-/merge_requests/1944)
* Fixes [#572](https://git.axelera.ai/prod/europa/-/issues/572) + [#1569](https://git.axelera.ai/prod/europa/-/issues/1569) + [#1812](https://git.axelera.ai/prod/europa/-/issues/1812) + [#1755](https://git.axelera.ai/prod/europa/-/issues/1755) + [#1863](https://git.axelera.ai/prod/europa/-/issues/1863) + [#1791](https://git.axelera.ai/prod/europa/-/issues/1791)

| \# | Change                   | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | V-Center | Top
| -- | ------------------------ | -------- | -------- | ------ | ------- | ------- | ------ | --- | -------- | ---
| 1  | L2 & LPDDR Interleaving  |   yes    |    yes   |  yes   |   yes   |   yes   |  yes   | yes |    yes   | yes
| 2  | SoC-Periph Init Routing  |   yes    |     -    |   -    |    -    |    -    |   -    |  -  |     -    |  -
| 3  | Single-Cycle SysCfg NIU  |   yes    |    yes   |  yes   |   yes   |   yes   |  yes   | yes |    yes   |  -
| 4  | PCIe NIU Pipelining      |    -     |     -    |   -    |    -    |    -    |   -    | yes |     -    |  -
| 5  | Memory Map Updates       |   yes    |     -    |   -    |   yes   |   yes   |   -    | yes |    yes   |  -
| 6  | Topology Refinements     |    -     |     -    |   -    |   yes   |   yes   |   -    | yes |    yes   |  -

1. Implements L2 & LPDDR Memory Interleaving Modes -- fix [#572](https://git.axelera.ai/prod/europa/-/issues/572)
    * Adds complexity to _every_ Initiator NIU's Address Decoding pipeline stage
    * Extends inter-partition `_data` buses by +1b
    * Extra pins (`i_l2_*_mode_port_*` & `i_lpddr_*_mode_port_*`) on almost every partition & `noc_top`
        * These are added **temporarily** & will be **removed** by NoC Bronze and driven by CSRs
        * These are **asynchronous** and **quasi-static** -- a 10-cycle max-delay constraint is applied
2. Adds connections from SoC-Periph Init LT -> to every Target -- fix [#1569](https://git.axelera.ai/prod/europa/-/issues/1569)
    * Adds complexity to the SoC-Periph Initiator NIU
    * Topology impact only on DDR-East (+4 2:1 switches)
3. Reduce SysCfg NIU pipelining to a single cycle -- fix [#1812](https://git.axelera.ai/prod/europa/-/issues/1812)
    * Expecting 100+ logic levels of logic in these NIUs
    * No timing challenges expected -- these NIUs are clocked at 50MHz `ref_clk`
4. Add pipeline stages to PCIe NIUs -- fix [#1755](https://git.axelera.ai/prod/europa/-/issues/1755)
    * That was an accidental design bug
5. Memory map updates -- fix [#1863](https://git.axelera.ai/prod/europa/-/issues/1863) + [#1791](https://git.axelera.ai/prod/europa/-/issues/1791)
    * Minimal impact on all Initiator NIU Address Decoding pipeline stage
6. Topology Refinements for improved physical implementation
    * A few extra links on **Center**, **North** & **South** to reduce worst pipe-to-pipe distance (was 1.8mm, now it's approx 1.4mm)
    * A bit of "untangling" at the **South** switches


| Partition | v0.6 Release Directory
| --------- | -----------------------
| DDR-East  | `/data/releases/europa/noc/noc_ddr_east/202410251847`
| DDR-West  | `/data/releases/europa/noc/noc_ddr_west/202410251847`
| H-East    | `/data/releases/europa/noc/noc_h_east/202410251847`
| H-North   | `/data/releases/europa/noc/noc_h_north/202410251847`
| H-South   | `/data/releases/europa/noc/noc_h_south/202410251847`
| H-West    | `/data/releases/europa/noc/noc_h_west/202410251847`
| SoC       | `/data/releases/europa/noc/noc_soc/202410251847`
| V-Center  | `/data/releases/europa/noc/noc_v_center/202410251847`
| Top       | `/data/releases/europa/noc/noc_top/202410071502`


## Version 0.5

* Date: 2024.10.22
* MR: [Europa!1902](https://git.axelera.ai/prod/europa/-/merge_requests/1902)
* Addresses [#1782](https://git.axelera.ai/prod/europa/-/issues/1782) + Fix [#1827](https://git.axelera.ai/prod/europa/-/issues/1827) + Fix [#1908](https://git.axelera.ai/prod/europa/-/issues/1908)

| \# | Change                   | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | V-Center | Top
| -- | ------------------------ | -------- | -------- | ------ | ------- | ------- | ------ | --- | -------- | ---
| 1  | Memory macro impl pins   |    -     |    -     |   -    |    -    |    -    |  yes   | yes |     -    |  -
| 2  | 2-stage Reset syncs      |   yes    |   yes    |   -    |    -    |    -    |   -    |  -  |     -    |  -
| 3  | SDMA pins                |    -     |    -     |   -    |    -    |    -    |  yes   | yes |     -    | yes
| 4  | Temp fix PCIe Targ MT    |   yes    |    -     |   -    |   yes   |   yes   |   -    | yes |    yes   |  -

1. Added memory macro `impl` pins [#1782](https://git.axelera.ai/prod/europa/-/issues/1782) -- temporarily **tied to constants**
2. 2-stage reset synchronizers for all resets (some had 3-stage)
3. Connect missing SDMA pins in `noc_top` -- fixes [#1827](https://git.axelera.ai/prod/europa/-/issues/1827)
4. Temporary fix for inaccessible PCIe Targ MT -- fixes [#1908](https://git.axelera.ai/prod/europa/-/issues/1908)

## Version 0.4.6b

* Date: 2024.10.16
* MR: [Europa!1746](https://git.axelera.ai/prod/europa/-/merge_requests/1746)
* Addresses constraints CR [ai-pd#117](https://git.axelera.ai/ai-pd-team/europa/-/issues/117)

| \# | Change                   | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | V-Center | Top
| -- | ------------------------ | -------- | -------- | ------ | ------- | ------- | ------ | --- | -------- | ---
| 1  | Constraints hold CDC fix |   yes    |    yes   |  yes   |   yes   |   yes   |  yes   | yes |    yes   |  -

1. Adds `set_false_path -hold` for CDCs -- check [ai-pd#117](https://git.axelera.ai/ai-pd-team/europa/-/issues/117) for more info

## Version 0.4.6

* Date: 2024.10.14
* MR: [Europa!1725](https://git.axelera.ai/prod/europa/-/merge_requests/1725/)
* Addresses functional bug: [#1830](https://git.axelera.ai/prod/europa/-/issues/1830)

| \# | Change              | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | Top
| -- | ------------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | ---
| 1  | Fix Mem Wrapper     |    -     |     -    |   -    |    -    |    -    |  yes   | yes |  -

1. Fix memory macro wrapper logic bugs -- fix [#1830](https://git.axelera.ai/prod/europa/-/issues/1830)

| Partition | v0.4.6 Release Directory
| --------- | -----------------------
| H-West    | `/data/releases/europa/noc/noc_h_west/202410141832`
| SoC       | `/data/releases/europa/noc/noc_soc/202410141829`

## Version 0.4.5

* Date: 2024.10.07
* MR: [Europa!1701](https://git.axelera.ai/prod/europa/-/merge_requests/1701/)
* Addresses issues: [#1615](https://git.axelera.ai/prod/europa/-/issues/1615)

| \# | Change              | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | Top
| -- | ------------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | ---
| 1  | Replace Macros      |    -     |     -    |   -    |    -    |    -    |  yes   |  -  |  -

1. Replace West memory macros with dual-port ones -- fix [#1615](https://git.axelera.ai/prod/europa/-/issues/1615)

## Version 0.4

* Date: 2024.10.04
* MR: [Europa!1645](https://git.axelera.ai/prod/europa/-/merge_requests/1645) + [noc-art#58](https://git.axelera.ai/prod/noc-art/-/merge_requests/58)
* Addresses issues: [#1601](https://git.axelera.ai/prod/europa/-/issues/1601) + [#1422](https://git.axelera.ai/prod/europa/-/issues/1422) + [#1629](https://git.axelera.ai/prod/europa/-/issues/1629) + [#1320](https://git.axelera.ai/prod/europa/-/issues/1320) + [#1531](https://git.axelera.ai/prod/europa/-/issues/1531)

| \# | Change              | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | Top
| -- | ------------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | ---
| 1  | 50MHz AON Clocks    |   yes    |    yes   |   -    |   yes   |   yes   |   -    | yes | yes
| 2  | AON Reset Sync      |   yes    |    yes   |   -    |   yes   |   yes   |   -    | yes | yes
| 3  | DFT Interface       |   yes    |    yes   |   yes  |   yes   |   yes   |  yes   | yes | yes


1. Add 50MHz AON clocks
    * Add `*_aon_clk` for all blocks -- connected to `ref_clk`
    * Modified constraints accordingly
    * Decided in
        * [#1199](https://git.axelera.ai/prod/europa/-/issues/1199): assign all SysCfg interfaces to `ref_clk`
        * [#1198](https://git.axelera.ai/prod/europa/-/issues/1198): move `ref_clk` to 50MHz (was 20MHz)
2. Add Reset synchronizers to AON Resets
    * A synchronizer is added at the p-wrapper for the partition's resets that need to be synchronized. CAUTION: `noc_rst_n` is still not synchronized although it should!
3. DFT interface added -- fixes [#1601](https://git.axelera.ai/prod/europa/-/issues/1601)
    * Rename `i_tm` to `scan_en`
    * `scan_en` forces Clock Gaters' clock-enable to 1 for DFT; see [Europa#1724](https://git.axelera.ai/prod/europa/-/issues/1724))
    * `test_mode` controls the bypass pin of the reset synchronizers; see [Europa#1724](https://git.axelera.ai/prod/europa/-/issues/1724))

| Partition | v0.4 Release Directory
| --------- | -----------------------
| DDR-East  | `/data/releases/europa/noc/noc_ddr_east/202410071500`
| DDR-West  | `/data/releases/europa/noc/noc_ddr_west/202410071501`
| H-East    | `/data/releases/europa/noc/noc_h_east/202410071501`
| H-North   | `/data/releases/europa/noc/noc_h_north/202410071501`
| H-South   | `/data/releases/europa/noc/noc_h_south/202410071501`
| H-West    | `/data/releases/europa/noc/noc_h_west/202410071502`
| SoC       | `/data/releases/europa/noc/noc_soc/202410071502`
| V-Center  | `/data/releases/europa/noc/noc_v_center/202410071502`
| Top       | `/data/releases/europa/noc/noc_top/202410071502`


## Version 0.3c

* Date: 2024.09.27
* MR: [Europa!1595](https://git.axelera.ai/prod/europa/-/merge_requests/1595)
* **Temporary** Fix for [Europa#1265](https://git.axelera.ai/prod/europa/-/issues/1265)
* **Not** released to PD

| \# | Change           | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | Top |
| -- | ---------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | --- |
| 1  | Address Decoder  | yes      |    -     |   -    | yes     | yes     |   -    | yes |   - |

1. Address Decoder block was added at the Initiator ports.
    * The decoding logic assigns `ARADDR[40]` depending on the `ARADDR[39:0]` value (it's set to 1 if the address maps to L2, otherwise 0)
    * The decoding logic adds **combinational** paths from partition boundaries to the NIU inputs
    * The plan is to replace this "temporary" patch until Bronze, move this logic into the NIU and thus, remove the combinational decoding stage from the inputs


## Version 0.3b

* Date: 2024.09.27
* MR: [Europa!1577](https://git.axelera.ai/prod/europa/-/merge_requests/1577)
* Fixes Issue: [#1535](https://git.axelera.ai/prod/europa/-/work_items/1535)
* **Not** released to PD

| \# | Change           | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | Top
| -- | ---------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | ---
| 1  | Token Interfaces |    -     |    -     |    -   |    -    |    -    |    -   |  -  | yes

1. Add Token OCP-Lite Interfaces to NoC Top -- WARNING: Unconnected/dangling signals!


## Version 0.3

* Date: 2024.09.26
* MR: [Europa!1538](https://git.axelera.ai/prod/europa/-/merge_requests/1538) + [noc-art!55](https://git.axelera.ai/prod/noc-art/-/merge_requests/55)
* Addresses issues: [#1539](https://git.axelera.ai/prod/europa/-/issues/1539) + [#1297](https://git.axelera.ai/prod/europa/-/issues/1297) + [#1665](https://git.axelera.ai/prod/europa/-/issues/1665) + [#1331](https://git.axelera.ai/prod/europa/-/issues/1331) + [#1683](https://git.axelera.ai/prod/europa/-/issues/1683) + [ai-pd#114](https://git.axelera.ai/ai-pd-team/europa/-/issues/114) + [#1277](https://git.axelera.ai/prod/europa/-/issues/1277)

| \# | Change           | DDR-East | DDR-West | H-East | H-North | H-South | H-West | SoC | Top |
| -- | ---------------- | -------- | -------- | ------ | ------- | ------- | ------ | --- | --- |
| 1  | Idle Pins Rename | yes      | yes      | yes    | yes     | yes     | yes    | yes | yes |
| 2  | LPDDR AXI Rename | yes      | yes      | -      |   -     |   -     |   -    |   - | yes |
| 3  | DCD MCU CLK-EN   |    -     |  -       | -      |   -     |   -     |   -    | yes | yes |
| 4  | PCIe LT Rename   |    -     |  -       | -      |   -     |   -     |   -    | yes | yes |
| 5  | PVE Clk-Freq Fix |    -     |  -       | -      |   -     |   -     |   -    | yes | -   |
| 6  | Top region fix   |    yes   |  yes     | yes    |   -     |   -     |  yes   | -   | -   |
| 7  | DCD +1 AXI       |   -      |  -       | -      |   -     |   -     |   -    | yes | yes |

1. Idle pins rename - fixes #1539
    * Rename of `*_pwr_idle_valAck` -> `*_pwr_idle_ack`
    * Rename of `*_pwr_idle_valReq` -> `*_pwr_idle_req`
    * External constraints update for the renamed signals
2. LPDDR HT/MT rename -fixes #1297
    * Rename of `*_lpddr_graph_*_targ_mt_*` ->  `*_lpddr_graph_*_targ_ht_*`
    * Rename of `*_lpddr_ppp_*_targ_ht_*` ->  `*_lpddr_ppp_*_targ_mt_*`
    * External constraints update for the renamed signals
3. Add Clk Enable for DCD MCU Interface - fixes #1665
    * Adds `i_dcd_mcu_clken` input (controls Clock Gater)
    * Adds extra generated clock in constraints
4. Rename & Resize PCIe Targ Cfg DBI interface - fixes #1331 & #1337
    * Rename `*_pcie_targ_lt_*` -> `*_pcie_targ_cfg_dbi_*`
    * Resize AXI DW to 32b (was mistakenly 64b)
5. Fix PVE AXI clock frequency bug - fixes #1683
    * Modify timing constraints to set PVE AXI clock to 1.2GHz (was mistakenly 1.2MHz)
6. Remove top-level region from each partition - fixes 1/2 of https://git.axelera.ai/ai-pd-team/europa/-/issues/114
    * Modify placement constraints to not contain a top-level region for each partition
7. Added extra AXI interface for Decoder - fixes #1277
    * Extra I/Os `*_dcd_dec_2_*` in RTL, constraints and top RTL
    * Extra logic (e.g. switches & links) to accommodate the extra interface

| Partition | v0.3 Release Directory
| --------- | -----------------------
| DDR-East  | `/data/releases/europa/noc/noc_ddr_east/202409261057`
| DDR-West  | `/data/releases/europa/noc/noc_ddr_west/202409261057`
| H-East    | `/data/releases/europa/noc/noc_h_east/202409261057`
| H-North   | `/data/releases/europa/noc/noc_h_north/202409261057`
| H-South   | `/data/releases/europa/noc/noc_h_south/202409261056`
| H-West    | `/data/releases/europa/noc/noc_h_west/202409261056`
| SoC       | `/data/releases/europa/noc/noc_soc/202409261051`
| V-Center  | `/data/releases/europa/noc/noc_v_center/202409261055`
| Top       | `/data/releases/europa/noc/noc_top/202409261052`
