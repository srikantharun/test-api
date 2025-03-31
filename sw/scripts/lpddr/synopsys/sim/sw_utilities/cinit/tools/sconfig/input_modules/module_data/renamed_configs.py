#!/usr/bin/env python3
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
# -------------------------------------------------------------------------------


RENAMED_CONFIGS_LIST = {"DWC_DDRCTL_CINIT_RW11_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD": "DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD",
                        "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_0_BANKS": "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_0_BANKS_0",
                        "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_2_BANKS": "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_2_BANKS_0",
                        "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_4_BANKS": "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_4_BANKS_0",
                        "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_8_BANKS": "DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_8_BANKS_0",
                        "NUM_PSTATES_0": "NUM_PSTATES=0",
                        "NUM_PSTATES_1": "NUM_PSTATES=1",
                        "NUM_PSTATES_2": "NUM_PSTATES=2",
                        "NUM_PSTATES_3": "NUM_PSTATES=3",
                        "DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_DEVICE_RANKS_4_PACKAGE_RANK": "DWC_DDRCTL_CINIT_NUM_RANKS_PER_DIMM_4_RANK",
                        "DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_MEMORY_CLASS_DDR4": "DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4",
                        "DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_MEMORY_CLASS_DDR5": "DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5"}
