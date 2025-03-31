# System Orchestration for Clocks, Resets and Fences

---------------------------------------------------------------------------------------------------------------------------------------

## Introduction
This document's purpose is to provide information about all clocks, resets and fences in the Europa chip. It should provide information over what is generated, where it is generated and where it is used.

---------------------------------------------------------------------------------------------------------------------------------------

 ## Clocks

Most clocks (under System Orchestration oversight) are generated internally using a total of 4 PLLs split between 2 locations: the SoC Management block and the DDR West Clock Gen block.

### PLL configuration
The PLL used in Europa is the _LeoLSI Integer PLL_.

Its base configuration can be seen below, knowing that SysPLL<0,1> are expected at Architecture definition to be configured for the 1.2GHz target and the DDR PLL to be configured for the 800MHz target.

|           | Min   | Max  | fast_clk | ddr_clk |
| ---       | ----  | ---- | ---      | ---     |
| **F_in**  | 4     | 300  | 50       | 50      |
| ---       | ----  | ---- | ---      | ---     |
| P[5:0]    | 1     | 63   | 5        | 5       |
| M[9:0]    | 64    | 1023 | 240      | 160     |
| S[2:0]    | 0     | 7    | 1        | 1       |
| K         | -     | -    | NA       | NA      |
| ---       | ----  | ---- | ---      | ---     |
| F_ref     | 4     | 12   | 10.0     | 10.0    |
| F_vco     | 1600  | 3200 | 2400     | 1600    |
| **F_out** | 25    | 3200 | 1200     | 800     |

### DDR West Clock Gen
This partition consists of a single PLL controlled by a PCTL block and has the sole purpose of generating the clock for the DDR partitions located at the West side of the chip.

It uses the configuration presented for _ddr_clk_ to run at 800MHz.

### SoC Management Generated

Inside the SoC Management block there is a sub-module called Clock Gen. It is responsible for generating most of Europa's internal clocks.

It consists of 3 PLLs, controlled through CSRs, and a set of clock selectors and dividers that provide flexibility over which PLL to use for each output clock and which division to apply. This allows us to be able to run some partitions at a slightly lower frequency than originally designed while maintaining one of the PLLs running at maximum speed.

The PLLs are:
- SysPLL0 - One of the system PLLs used for main clocks generation
- SysPLL1 - The second system PLL
- DDRPLL  - The PLL that, similarly to the one present in DDR West Clock Gen has the sole purpose of generating the clock for the DDR partitions in the East area of Europa.

Below a table shows all generated clocks at SoC Management clock gen module:

| Clock Name       | Frequency      |  Source                       | Usage                               |
| --------------   | -------------- | ------------                  | ----------------------------------- |
| `ref_clk`        | 50MHz          | PAD                           | Reference clock                  |
| `rtc_clk`        | 50MHz          | ref_clk                       | For the RTC timer                   |
| `fast_clk`       | 1.2GHz         | SysPLL0 or SysPLL1            | Main clock for NOC, PVE, AIC, L2, SYS_SPM, SDMA, and MCU clock in DCD. |
| `apu_clk`        | 1.2GHz (max)   | SysPLL0 or SysPLL1            | Main clock for APU cores, L2 and subsystem. |
| `codec_clk`      | 600MHz         | SysPLL0 or SysPLL1            | Main clock for Decoder and PCIe.    |
| `emmc_clk`       | 200MHz         | SysPLL0 or SysPLL1            | Pin side soft Phy Clock for eMMC    |
| `periph_clk`     | 100MHz         | SysPLL0 or SysPLL1            | Slow speed peripheral clock for slow peripheral and soc management IP |
| `ddr_clk`        | 800MHz         | DdrPLL                        | LPDDR clock |
| `tck`            | 100MHz         | PAD                           | JTAG clock - synchronous across the chip |
| `ssn`            | 100MHz         | PAD                           | DFT clock |
| `test_clk`       | 100MHz         | PAD                           | DFT clock |
| `pvt_clk`        | 4MHz or 8MHz   | SysPLL0 or SysPLL1 or DFT Pad | Reference clock for PVT sensors IP.  |


### Per-Partition clocks
The clocks generated are used in one or more partitions (or SoC Management sub-modules) of Europa.

#### SysCfg Bus / Always-on domain
Every partition receives **ref_clk** (50MHz).

#### Functional clocks
| Partition    | Frequency | Clock       | SocMgmt output |
| ---          | ---       | ---         | --- |
| AIC          | 1.2GHz    | `i_clk`       | `fast_clk`             |
| APU          | 1.2GHz    | `i_clk`       | `apu_clk`              |
| Decoder      | 600MHz    | `i_clk`       | `codec_clk`            |
| Decoder      | 1.2GHz    | `i_mcu_clk`   | `fast_clk`             |
| L2           | 1.2GHz    | `i_clk`       | `fast_clk`             |
| LPDDR PPP    | 800MHz    | `i_lpddr_clk` | `ddr_ref_east_clk`     |
| LPDDR Graph  | 800MHz    | `i_lpddr_clk` | **Not from SoCMgmt** -> DDR West Clk Gen output -> `o_ddr_west_clk` |
| PCIe         | 100MHz    | `apb_pclk`    | `periph_clk`           |
| PCIe         | 100MHz    | `aux_clk`     | `periph_clk`           |
| PCIe         | 100MHz    | `phy_fw_clk`  | `periph_clk`           |
| PCIe         | 100MHz    | `dbi_aclk`    | `periph_clk`           |
| PCIe         | 600MHz    | `AXI`         | `codec_clk`            |
| PVE          | 1.2GHz    | `i_clk`       | `fast_clk`             |
| SDMA         | 1.2GHz    | `i_clk`       | `fast_clk`             |
| SocPeriph    | 100MHz    | `i_periph_clk`| `periph_clk`           |
| SocPeriph    | 200MHz    | `i_emmc_clk`  | `emmc_clk`             |
| SysSPM       | 1.2GHz    | `i_clk`       | `fast_clk`             |
| SocMgmt      | 1.2GHz    | `fast_clk`    | `fast_clk`             |
| SocMgmt      | 100MHz    | `periph_clk`  | `periph_clk`           |
| SocMgmt      | 4/8MHz    | `pvt_clk`     | `pvt_clk`              |
| NoC          | 1.2GHz    | `i_noc_clk`   | `noc_clk`              |

---------------------------------------------------------------------------------------------------------------------------------------

## Resets

### Pin driven
There's 1 main reset IO. It is only used by the SoC Management block for the generation of system resets inside the Reset Gen sub-block.

| Reset        | Source  | Partition      |  Uses           |
| ----------   | ------  | ----           | -------         |
| i_por_n      | IO      | SoC Management | Reset gen block |

### SoC Management Generated

| Reset        | Source          |  Uses                                  |
| ----------   | ------          | -------------------------------------- |
| `i_por_n`      | IO              | Reset gen block |
| `i_hw_rst_n`   | IO              | Reset gen block |
| `wdt_rst_n`    | Watchdog timer  | Reset gen block |
| `debug_rst_n`  | DBG             | Reset gen block |
| `ao_rst_n`     | Reset gen block | CSRs, PLLs (clock gen), MBIST, output |
| `global_rst_n` | Reset gen block | All other logic, output |

### Per Partition
All partitions can receive the 2 resets output by the SoC Management block. While all should be using the AO reset, if there's no usecase for a warm reset there is no need to use global_rst_n.

It is also important to realise that most partitions will need SW intervention to exit reset, as the PCTL block provides a SW reset capability.

**Note**: If a partition has **automatic** reset exit it can theoretically still go through a reset, it would simply auto-exit it.

| Partition         | AO Reset                     | Global Reset         | PPMU Reset Exit    | Notes |
| -------------     | -----------------            | -------------------- | ------------------ | --- |
| NOC               | ( AO CSR (sits in SOC_MGMT)) | Everything else      | Automatic ( HW )   | |
| APU               | AO CSR                       | Everything else      | Automatic ( HW )   | |
| SOC_MGMT          | AO CSR, OTP, PLL, MBIST      | Everything else      | Automatic ( HW )   | |
| SOC_PERIPH        | AO CSR                       | Everything else      | Automatic ( HW )   | |
| SYS_SPM           | AO CSR                       | Everything else      | Automatic ( HW )   | |
| DDR West Clk Gen  | AO CSR, PLL                  | **Nothing**          | Automatic ( HW )   | |
| SDMA              | AO CSR                       | Everything else      | SW via AO CSR      | |
| L2                | AO CSR                       | Everything else      | SW via AO CSR      | |
| PVE               | AO CSR                       | Everything else      | SW via AO CSR      | |
| AIC               | AO CSR                       | Everything else      | SW via AO CSR      | |
| DCD               | AO CSR                       | Everything else      | SW via AO CSR      | |
| LPDDR             | AO CSR                       | Everything else      | SW via AO CSR      | |
| PCIE              | AO CSR                       | Everything else      | SW via AO CSR      | The PCIe has internal resets generated at PHY level that are not included in this document |

---------------------------------------------------------------------------------------------------------------------------------------

## Fences

### SysCfg Bus
No SysCfg interface should have a fence as we must ensure that this is always accessible and it targets the AO domain. If it is ever reset it means that the entire system has been reset.

| Partition | Interface | Fence present? | Fence # | Default out of Reset |
| ---       | ---       | ---            | ---     | ---     |
| AIC       | `aic_$_targ_syscfg`               | No  | NA | NA
| SDMA      | `sdma_$_targ_syscfg`              | No  | NA | NA
| APU       | `apu_targ_syscfg`                 | No  | NA | NA
| Decoder   | `dcd_targ_syscfg`                 | No  | NA | NA
| L2        | `l2_$_targ_syscfg`                | No  | NA | NA
| LPDDR     | `lpddr_<ppp,graph>_$_targ_syscfg` | No  | NA | NA
| PCIe      | `pcie_targ_syscfg`                | No  | NA | NA
| PVE       | `pve_$_targ_syscfg`               | No  | NA | NA
| SocMgmt   | `soc_mgmt_targ_syscfg`            | No  | NA | NA
| SocPeriph | `soc_periph_targ_syscfg`          | No  | NA | NA
| SysSPM    | `sys_spm_targ_syscfg`             | No  | NA | NA

### Other Buses

| Partition | Interface                       | Fence present? | Fence #                     | Default out of Reset |
| ---       | ---                             | ---            | ---                         | ---     |
| AIC       | `aic_$_init_ht`                 | Yes            | `aic_fence_0`               | **UP/Active** |
| AIC       | `aic_$_init_lt`                 | Yes            | `aic_fence_0`               | **UP/Active** |
| AIC       | `aic_$_targ_lt`                 | Yes            | `aic_fence_0`               | **UP/Active** |
| AIC       | `aic_$_init_tok_ocpl_s`         | Yes            | `aic_tok_fence_0`           | **UP/Active** |
| AIC       | `aic_$_targ_tok_ocpl_m`         | Yes            | `aic_tok_fence_0`           | **UP/Active** |
| SDMA      | `sdma_$_init_ht_0`              | Yes            | `sdma_fence0`               | **UP/Active** |
| SDMA      | `sdma_$_init_ht_1`              | Yes            | `sdma_fence0`               | **UP/Active** |
| SDMA      | `sdma_$_init_lt`                | Yes            | `sdma_fence0`               | **UP/Active** |
| SDMA      | `sdma_$_targ_lt`                | Yes            | `sdma_fence0`               | **UP/Active** |
| SDMA      | `sdma_$_targ_tok_ocpl_m`        | Yes            | `sdma_tok_fence0`           | **UP/Active** |
| SDMA      | `sdma_$_init_tok_ocpl_s`        | Yes            | `sdma_tok_fence0`           | **UP/Active** |
| APU       | `apu_init_mt`                   | Yes            | `apu_fence_0`               | **DOWN** |
| APU       | `apu_init_lt`                   | Yes            | `apu_fence_0`               | **DOWN** |
| APU       | `apu_targ_lt`                   | Yes            | `apu_fence_0`               | **DOWN** |
| APU       | `apu_targ_tok_ocpl_m`           | Yes            | `apu_tok_fence_0`           | **DOWN** |
| APU       | `apu_init_tok_ocpl_s`           | Yes            | `apu_tok_fence_0`           | **DOWN** |
| Decoder   | `dcd_dec_0_init_mt`             | Yes            | `decoder_fence_0`           | **UP/Active** |
| Decoder   | `dcd_dec_1_init_mt`             | Yes            | `decoder_fence_0`           | **UP/Active** |
| Decoder   | `dcd_dec_2_init_mt`             | Yes            | `decoder_fence_0`           | **UP/Active** |
| Decoder   | `dcd_mcu_init_lt`               | Yes            | `decoder_fence_1`           | **UP/Active** |
| Decoder   | `dcd_targ_cfg`                  | Yes            | `decoder_fence_0`           | **UP/Active** |
| L2        | `l2_$_targ_ht`                  | Yes            | `l2_fence_0`                | **UP/Active** |
| LPDDR     | `lpddr_<ppp,graph>_$_targ_ht`   | Yes            | `lpddr_<ppp,graph>_fence_0` | **UP/Active** |
| LPDDR     | `lpddr_<ppp,graph>_$_targ_cfg`  | Yes            | `lpddr_<ppp,graph>_fence_1` | **UP/Active** |
| PCIe      | `pcie_init_mt`                  | Yes            | `pcie_fence_0`              | **UP/Active** |
| PCIe      | `pcie_targ_mt`                  | Yes            | `pcie_fence_1`              | **UP/Active** |
| PCIe      | `pcie_targ_cfg_dbi`             | Yes            | `pcie_fence_2`              | **UP/Active** |
| PCIe      | `pcie_targ_cfg`                 | Yes            | `pcie_fence_3`              | **UP/Active** |
| PVE       | `pve_$_init_ht`                 | Yes            | `pve_fence_0`               | **UP/Active** |
| PVE       | `pve_$_init_lt`                 | Yes            | `pve_fence_0`               | **UP/Active** |
| PVE       | `pve_$_targ_lt`                 | Yes            | `pve_fence_0`               | **UP/Active** |
| SocPeriph | `soc_periph_init_lt`            | Yes            | `socperiph_fence_0`         | **DOWN** |
| SocPeriph | `soc_periph_targ_lt`            | Yes            | `socperiph_fence_0`         | **DOWN** |
| SysSPM    | `sys_spm_targ_lt`               | Yes            | `sysspm_fence_0`            | **DOWN** |
| SocMgmt   | `soc_mgmt_init_lt`              | Yes            | `socmgmt_fence_0`           | **DOWN** |
| SocMgmt   | `soc_mgmt_targ_lt`              | Yes            | `socmgmt_fence_0`           | **DOWN** |
| NoC       | NA | NA  | NA | NA |
