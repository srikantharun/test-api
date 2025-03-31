// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


#ifdef JESD79_4C_DDR4_SPEEDBINS

#include "cinit_ddr4_speedbins_c.h"
#include "dwc_cinit_macros.h"

/* TODO Check and update if needed 2133MHZ tck(AVG)min from 938 to 937 for impacted cas configs */

/* 1600 MHz */
static const ddr4_cas_cfg_t ddr4_1600J_cas_cfgs[] = {
    /*  -------------- 1333-1600MHz --------------- */
	/* MAX_TCK_PS   MIN_TCK_PS      CL      CLRDBI  */
    {  1499,        1250,           10,     12      },
    {  1499,        1250,           11,     13      },
    {  1499,        1250,           12,     14      },
    /* ---------------- 1250-1333MHz -------------- */
	/* MAX_TCK_PS   MIN_TCK_PS      CL      CLRDBI  */
    {  1600,        1500,           9,      11      },
    {  1600,        1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_1600K_cas_cfgs[] = {
    /* ---------------- 1333-1600MHz -------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ---------------- 1250-1333MHz -------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      }
};
static const ddr4_cas_cfg_t ddr4_1600L_cas_cfgs[] = {
	/* --------------- 1333-1600MHz --------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* --------------- 1250-1333MHz --------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};

/* 1866 MHz */
static const ddr4_cas_cfg_t ddr4_1866L_cas_cfgs[] = {
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           12,     14      },
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_1866M_cas_cfgs[] = {
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      }
};
static const ddr4_cas_cfg_t ddr4_1866N_cas_cfgs[] = {
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};

/* 2133 MHz */
static const ddr4_cas_cfg_t ddr4_2133N_cas_cfgs[] = {
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            14,     17      },
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2133P_cas_cfgs[] = {
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      }
};
static const ddr4_cas_cfg_t ddr4_2133R_cas_cfgs[] = {
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};


/* 2400 MHz */
static const ddr4_cas_cfg_t ddr4_2400P_cas_cfgs[] = {
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            15,     18      },
    { 937,          833,            16,     19      },
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2400R_cas_cfgs[] = {
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            16,     19      },
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      }
};
static const ddr4_cas_cfg_t ddr4_2400T_cas_cfgs[] = {
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2400U_cas_cfgs[] = {
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};

/* 2666 MHz */
static const ddr4_cas_cfg_t ddr4_2666T_cas_cfgs[] = {
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            17,     20      },
    { 832,          750,            18,     21      },
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            16,     19      },
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2666U_cas_cfgs[] = {
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            18,     21      },
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2666V_cas_cfgs[] = {
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2666W_cas_cfgs[] = {
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};

/* 2933 MHz */
static const ddr4_cas_cfg_t ddr4_2933V_cas_cfgs[] = {
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            19,     23      },
    { 749,          682,            20,     24      },
    { 749,          682,            21,     25      },
    { 749,          682,            22,     26      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            18,     21      },
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            16,     19      },
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2933W_cas_cfgs[] = {
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            20,     24      },
    { 749,          682,            21,     25      },
    { 749,          682,            22,     26      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2933Y_cas_cfgs[] = {
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            21,     25      },
    { 749,          682,            22,     26      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_2933AA_cas_cfgs[] = {
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            22,     26      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};

/* 3200 MHz */
static const ddr4_cas_cfg_t ddr4_3200W_cas_cfgs[] = {
    /* ---------------- 2933-3200MHz -------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 681,          625,            20,     24      },
    { 681,          625,            22,     26      },
    { 681,          625,            24,     28      },
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            20,     24      },
    { 749,          682,            21,     25      },
    { 749,          682,            22,     26      },
    { 749,          682,            24,     28      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            18,     21      },
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            16,     19      },
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           9,      11      },
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_3200AA_cas_cfgs[] = {
    /* ----------- 2933-3200MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 681,          625,            22,     26      },
    { 681,          625,            24,     28      },
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            21,     25      },
    { 749,          682,            22,     26      },
    { 749,          682,            24,     28      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            19,     22      },
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            17,     20      },
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            15,     18      },
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           13,     15      },
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           11,     13      },
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};
static const ddr4_cas_cfg_t ddr4_3200AC_cas_cfgs[] = {
    /* ---------------- 2933-3200MHz -------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 681,          625,            24,     28      },
    /* ----------- 2666-2933MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 749,          682,            22,     26      },
    { 749,          682,            24,     28      },
    /* ----------- 2400-2666MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 832,          750,            20,     23      },
    /* ----------- 2133-2400MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 937,          833,            18,     21      },
    /* ----------- 1866-2133MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1070,         938,            16,     19      },
    /* ----------- 1600-1866MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1249,         1071,           14,     16      },
    /* ----------- 1333-1600MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1499,         1250,           12,     14      },
    /* ----------- 1250-1333MHz ------------------- */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      CLRDBI  */
    { 1600,         1500,           10,     12      }
};

/**
 * @brief Table containing speed grades' Speed Bin timings found in JEDEC's JESD79-4C specification (Tables [144-150])
 *
 */
static const ddr4_speedbin_t ddr4_speedbin_table[] = {
/*  ---------------1600MHz---------------                ---------------1600MHz---------------                ---------------1600MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_1600J,  12500,  18000,  12500,  12500,  35000,  47500, {.spec_non_3ds={2,  ddr4_1600J_cas_cfgs }},  GET_ARR_NELEMS(ddr4_1600J_cas_cfgs) },
{ DWC_DDR4_1600K,  13750,  18000,  13750,  13750,  35000,  48750, {.spec_non_3ds={2,  ddr4_1600K_cas_cfgs }},  GET_ARR_NELEMS(ddr4_1600K_cas_cfgs) },
{ DWC_DDR4_1600L,  15000,  18000,  15000,  15000,  35000,  50000, {.spec_non_3ds={2,  ddr4_1600L_cas_cfgs }},  GET_ARR_NELEMS(ddr4_1600L_cas_cfgs) },
/*  ---------------1866MHz---------------                ---------------1866MHz---------------                ---------------1866MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_1866L,  12850,  18000,  12850,  12850,  34000,  46850, {.spec_non_3ds={2,  ddr4_1866L_cas_cfgs }},  GET_ARR_NELEMS(ddr4_1866L_cas_cfgs) },
{ DWC_DDR4_1866M,  13920,  18000,  13920,  13920,  34000,  47920, {.spec_non_3ds={2,  ddr4_1866M_cas_cfgs }},  GET_ARR_NELEMS(ddr4_1866M_cas_cfgs) },
{ DWC_DDR4_1866N,  15000,  18000,  15000,  15000,  34000,  49000, {.spec_non_3ds={2,  ddr4_1866N_cas_cfgs }},  GET_ARR_NELEMS(ddr4_1866N_cas_cfgs) },
/*  ---------------2133MHz---------------                ---------------2133MHz---------------                ---------------2133MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_2133N,  13130,  18000,  13130,  13130,  33000,  46130, {.spec_non_3ds={3,  ddr4_2133N_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2133N_cas_cfgs) },
{ DWC_DDR4_2133P,  14060,  18000,  14060,  14060,  33000,  47060, {.spec_non_3ds={3,  ddr4_2133P_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2133P_cas_cfgs) },
{ DWC_DDR4_2133R,  15000,  18000,  15000,  15000,  33000,  48000, {.spec_non_3ds={3,  ddr4_2133R_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2133R_cas_cfgs) },
/*  ---------------2400MHz---------------                ---------------2400MHz---------------                ---------------2400MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_2400P,  12500,  18000,  12500,  12500,  32000,  44500, {.spec_non_3ds={3,  ddr4_2400P_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2400P_cas_cfgs) },
{ DWC_DDR4_2400R,  13320,  18000,  13320,  13320,  32000,  45320, {.spec_non_3ds={3,  ddr4_2400R_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2400R_cas_cfgs) },
{ DWC_DDR4_2400T,  14160,  18000,  14160,  14160,  32000,  46160, {.spec_non_3ds={3,  ddr4_2400T_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2400T_cas_cfgs) },
{ DWC_DDR4_2400U,  15000,  18000,  15000,  15000,  32000,  47000, {.spec_non_3ds={3,  ddr4_2400U_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2400U_cas_cfgs) },
/*  ---------------2666MHz---------------                ---------------2666MHz---------------                ---------------2666MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_2666T,  12750,  18000,  12750,  12750,  32000,  44750, {.spec_non_3ds={3,  ddr4_2666T_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2666T_cas_cfgs) },
{ DWC_DDR4_2666U,  13500,  18000,  13500,  13500,  32000,  45500, {.spec_non_3ds={3,  ddr4_2666U_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2666U_cas_cfgs) },
{ DWC_DDR4_2666V,  14250,  18000,  14250,  14250,  32000,  46250, {.spec_non_3ds={3,  ddr4_2666V_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2666V_cas_cfgs) },
{ DWC_DDR4_2666W,  15000,  18000,  15000,  15000,  32000,  47000, {.spec_non_3ds={3,  ddr4_2666W_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2666W_cas_cfgs) },
/*  ---------------2933MHz---------------                ---------------2933MHz---------------                ---------------2933MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_2933V,  12960,  18000,  12960,  12960,  32000,  44750, {.spec_non_3ds={4,  ddr4_2933V_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2933V_cas_cfgs) },
{ DWC_DDR4_2933W,  13640,  18000,  13640,  13640,  32000,  45500, {.spec_non_3ds={4,  ddr4_2933W_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2933W_cas_cfgs) },
{ DWC_DDR4_2933Y,  14320,  18000,  14320,  14320,  32000,  46320, {.spec_non_3ds={4,  ddr4_2933Y_cas_cfgs }},  GET_ARR_NELEMS(ddr4_2933Y_cas_cfgs) },
{ DWC_DDR4_2933AA, 15000,  18000,  15000,  15000,  32000,  47000, {.spec_non_3ds={4,  ddr4_2933AA_cas_cfgs}},  GET_ARR_NELEMS(ddr4_2933AA_cas_cfgs)},
/*  ---------------3200MHz---------------                ---------------3200MHz---------------                ---------------3200MHz---------------*/
/* Speed grade    tAA min  tAA max  tRCD    tRP   tRAS min  tRC                tAA_DBI      CL table                    NumberOfValidCasConfigs    */
{ DWC_DDR4_3200W,  12500,  18000,  12500,  12500,  32000,  44500, {.spec_non_3ds={4,  ddr4_3200W_cas_cfgs }},  GET_ARR_NELEMS(ddr4_3200W_cas_cfgs) },
{ DWC_DDR4_3200AA, 13750,  18000,  13750,  13750,  32000,  45750, {.spec_non_3ds={4,  ddr4_3200AA_cas_cfgs}},  GET_ARR_NELEMS(ddr4_3200AA_cas_cfgs)},
{ DWC_DDR4_3200AC, 15000,  18000,  15000,  15000,  32000,  47000, {.spec_non_3ds={4,  ddr4_3200AC_cas_cfgs}},  GET_ARR_NELEMS(ddr4_3200AC_cas_cfgs)}
};


void get_ddr4_speedbin_table(const ddr4_speedbin_t** table_ptr, uint8_t* const n_sgs)
{
    *table_ptr = ddr4_speedbin_table;
    *n_sgs =  GET_ARR_NELEMS(ddr4_speedbin_table);
}

#endif /* JESD79_4C_DDR4_SPEEDBINS */
