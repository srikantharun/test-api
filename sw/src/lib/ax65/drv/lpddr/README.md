# LPDDR software drivers and related files

```
.
├── drv_lpddr.c
├── drv_lpddr.h
├── generated
│   └── lpddrPhyInit_cpu_dpi_ss4_skiptrain.c
├── iccm_preload_fw
│   ├── lpddr5_pmu_train_imem_bank0_ecc_0.txt
│   ├── lpddr5_pmu_train_imem_bank0_ecc_1.txt
│   ├── lpddr5_pmu_train_imem_bank0_ecc_2.txt
│   ├── lpddr5_pmu_train_imem_bank0_ecc_3.txt
│   ├── lpddr5_pmu_train_imem_bank1_ecc_0.txt
│   ├── lpddr5_pmu_train_imem_bank1_ecc_1.txt
│   ├── lpddr5_pmu_train_imem_bank1_ecc_2.txt
│   ├── lpddr5_pmu_train_imem_bank1_ecc_3.txt
│   └── README.md
├── lpddr_ctl_memorymap.h
├── lpddr_phy_memorymap.h
├── phyinit_logs
│   └── phyinit_cpu_dpi_ss4.txt
├── README.md
└── waveforms
    ├── lpddr_apb.do
    └── lpddr_datapath.do
```

## Driver files and auxiliary files

- `drv_lpddr.c` and respective header contain the LPDDR methods for reset assertion/deassertion, controller configuration and PHY initialization sequence.

- `lpddr_ctl_memorymap.h` and `lpddr_phy_memorymap.h` contain the register memory maps of the Controller and PHY.

- `generated/lpddrPhyInit_cpu_dpi_ss4_skiptrain.c`contain the PHYinit sequence of steps to perform the PHY and DRAM initialization. These are auto-generated using `sw/scripts/lpddr/convert_snps_phyinit_to_europa_c_code.py` and is based on `phyinit_logs/phyinit_cpu_dpi_ss4.txt`.

## Synopsys or CINIT/PHYinit output files

These files are generated from running CINIT or have been copied from a Synopsys testcase from the SS3 subsystem delivery.

- `phyinit_logs/phyinit_cpu_dpi_ss4.txt` is copied from `/home/rodrigo.borges/workspace/hw/europa_cpu_dpi_ss4/hw/vendor/synopsys/lpddr_subsys/default/workspaces/ss4_simulations/sim/test_dwc_ddrctl_cinit_cpu_dpi_lpddr5_LPDDR5_DEMO_6400_4G_x16_4BK4BG_1_4_defconfig`

## Miscellaneous

- `iccm_preload_fw/` - contains ICCM binary to be preloaded.

- `waveform/` - contains LPDDR signal list for opening waveforms for debugging.
