---
title: NoC Memory Macros
doc:
  status: draft
  version: [0, 0, 2]
  confidentiality: internal
---

# Memory Macros

Memory macros are used in the SoC & West partitions to implement Rate Adapters & FIFOs.

## Macro Summary

The following macros are instantiated to implement each memory:

| Macro                                          | SoC | West |
|------------------------------------------------|----:|-----:|
| `ln05lpe_a00_mc_rf2rp_hsr_rvt_144x24m1b4c1r2`  | 32  | 0
| `ln05lpe_a00_mc_rf2rp_hsr_rvt_160x72m1b4c1r2`  | 24  | 0
| `ln05lpe_a00_mc_rf2rp_hsr_rvt_160x136m1b4c1r2` | 12  | 0
| `ln05lpe_a00_mc_rf2rp_hsr_rvt_160x64m1b4c1r2`  | 48  | 32
| Total                                          | 116 | 32

## Breakdown

Below table lists the memory requirements per FlexNoC module:

| \# | Partition | FlexNoC Module                                 | DataW | Depth | Instances |
|----|-----------|------------------------------------------------|------:|------:|----------:|
| 1  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_cef99a6a_D401`    |  401  |    23 |        8  |
| 2  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_359fbb95_D583`    |  583  |    71 |        6  |
| 3  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_d623c3b0_D295`    |  295  |   135 |        4  |
| 4  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_94448790_D579`    |  579  |    63 |       12  |
| 5  | West      | `noc_art_h_west_z_H_R_U_Rfm_Rfh_94448790_D579` |  579  |    63 |        8  |

Based on the technology library macro availability, we've implemented each one of them using a combination of macros as shown in the table below. Note that:

* **MDataW** is the Data Width of the used Macro
* **MDepth** is the Depth of the used Macro
* **MInst (Data)** is the number of Macros instantiated _in-parallel_ to implement the required Data Width. This is equal to `ceil(DataW/MDataW)`
* **MInst (Depth)** is the number of Macros instantiated _in-series_ to implement the required Depth. This is equal to `ceil(Depth/MDepth)`
* **MInst** is the total number of Macros instantiated to implement the required Memory. It's the product of the _in-series_ and _in-parallel_ columns.

| \# | Partition | DataW | Depth | Macro                                          | MDataW | MDepth | MInst (Data) | MInst (Depth) | MInst |
|----|-----------|------:|------:|------------------------------------------------|-------:|-------:|-------------:|--------------:|------:|
| 1  | SoC       |   401 |    23 | `ln05lpe_a00_mc_rf2rp_hsr_rvt_24x144m1b2c1r2`  |    144 |     24 |            4 |             1 |     4 |
| 2  | SoC       |   583 |    71 | `ln05lpe_a00_mc_rf2rp_hsr_rvt_72x160m1b4c1r2`  |    160 |     72 |            4 |             1 |     4 |
| 3  | SoC       |   295 |   135 | `ln05lpe_a00_mc_rf2rp_hsr_rvt_136x160m1b4c1r2` |    160 |    136 |            3 |             1 |     3 |
| 4  | SoC       |   579 |    63 | `ln05lpe_a00_mc_rf2rp_hsr_rvt_64x160m1b4c1r2`  |    160 |     64 |            4 |             1 |     4 |
| 6  | West      |   579 |    63 | `ln05lpe_a00_mc_rf2rp_hsr_rvt_64x160m1b4c1r2`  |    160 |     64 |            4 |             1 |     4 |

Therefore, we get the following Macro Counts instantiated per FlexNoC module (multiply MInst x Instances):

| \# | Partition | FlexNoC Module                                 | Macro Count | Macro Name                                     |
|----|-----------|------------------------------------------------|-------------|------------------------------------------------|
| 1  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_cef99a6a_D401`    | 32          | `ln05lpe_a00_mc_rf2rp_hsr_rvt_24x144m1b2c1r2`  |
| 2  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_359fbb95_D583`    | 24          | `ln05lpe_a00_mc_rf2rp_hsr_rvt_72x160m1b4c1r2`  |
| 3  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_d623c3b0_D295`    | 12          | `ln05lpe_a00_mc_rf2rp_hsr_rvt_136x160m1b4c1r2` |
| 4  | SoC       | `noc_art_soc_z_H_R_U_Rfm_Rfh_94448790_D579`    | 48          | `ln05lpe_a00_mc_rf2rp_hsr_rvt_64x160m1b4c1r2`  |
| 5  | West      | `noc_art_h_west_z_H_R_U_Rfm_Rfh_94448790_D579` | 32          | `ln05lpe_a00_mc_rf2rp_hsr_rvt_64x160m1b4c1r2`  |


## RTL & Verification

The required memory macros for these memories are instantiated in the generic wrapper `noc_common_mem_wrap_top`. Designer sets the 4 parameters:

* DataW - parameter `DATAW`
* Depth - parameter `DEPTH`
* MDataW - parameter `MACRO_DATAW`
* MDepth - parameter `MACRO_DEPTH`

The design then instantiates the proper number of macros. Keep in mind that, when a macro needs to be instantiated multiple times to cover the Depth, the Macro Depth (MDepth) must be a power of 2, so that address decoding logic remains simplified. If a single macro suffices to cover the required depth, there's no requirement for MDepth.

There's a block-level TB available for quickly checking that `noc_common_mem_wrap_top` works nicely for any configuration. Use that when using a new combination of DataW/Depth/MDataw/MDepth values. Run as follows:

```bash
make -C hw/impl/europa/blocks/noc/dv/sim-regfile-hm-cell run_vsim TESTNAME=noc_mem_random_test
```

* `TESTNAME` can be `noc_mem_capacity_test` or `noc_mem_random_test`
* Add `GUI=1` for interactive debugging
* Change the 4 design parameters (DataW/Depth/MDataW/MDepth) by defining plusargs `DATAW`, `DEPTH`, `MACRO_DATAW` and `MACRO_DEPTH` respectively
* Check `hw/impl/europa/blocks/noc/dv/sim-regfile-hm-cell/simulation_config.mk` for all the available options
