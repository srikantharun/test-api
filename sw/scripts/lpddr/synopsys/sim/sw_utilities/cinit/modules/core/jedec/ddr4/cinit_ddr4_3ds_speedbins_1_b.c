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


#ifdef JESD79_4_1_B_DDR4_3DS_SPEEDBINS

#include "cinit_ddr4_3ds_speedbins_1_b.h"
#include "dwc_cinit_macros.h"

// TODO: Check and update if needed 2133MHZ tck(AVG)min from 938 to 937 for impacted cas configs
// TODO: Add support for 2133 MHz 3DS speedgrades

/* 1600 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_1600J_3DS2B_cas_cfgs[] =
{   /*       ----- 1333-1600MHz --      */
	/* MAX_TCK_PS   MIN_TCK_PS      CL  */
    {  1500,        1250,           12  },
    {  1500,        1250,           13  },
    {  1500,        1250,           14  }
};
static const ddr4_3ds_cas_cfg_t ddr4_1600K_3DS2B_cas_cfgs[] =
{   /*       ----- 1333-1600MHz --      */
	/* MAX_TCK_PS   MIN_TCK_PS      CL  */
    {  1500,        1250,           13  },
    {  1500,        1250,           14  }
};
static const ddr4_3ds_cas_cfg_t ddr4_1600L_3DS2B_cas_cfgs[] =
{
    /*       ----- 1333-1600MHz --       */
	/* MAX_TCK_PS   MIN_TCK_PS      CL  */
    {  1500,        1250,           14  }
};

/* 1866 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_1866L_3DS2B_cas_cfgs[] = {
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           14      },
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           12      },
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_1866M_3DS2B_cas_cfgs[] = {
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_1866N_3DS2B_cas_cfgs[] = {
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};

/* 2133 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_2133P_3DS2A_cas_cfgs[] = {
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            17      },
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2133P_3DS3A_cas_cfgs[] = {
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2133R_3DS4A_cas_cfgs[] = {
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};


/* 2400 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_2400P_3DS3B_cas_cfgs[] = {
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            18      },
    { 937,          833,            19      },
    { 937,          833,            20      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            17      },
    { 1070,         938,            18      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           14      },
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2400T_3DS2A_cas_cfgs[] = {
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            19      },
    { 937,          833,            20      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            17      },
    { 1070,         938,            18      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2400U_3DS2A_cas_cfgs[] = {
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2400U_3DS4A_cas_cfgs[] = {
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};

/* 2666 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_2666T_3DS3A_cas_cfgs[] =
{
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            20      },
    { 832,          750,            22      },
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2666V_3DS3A_cas_cfgs[] =
{
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            22      },
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2666W_3DS4A_cas_cfgs[] =
{
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};

// /* 2933 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_2933W_3DS3A_cas_cfgs[] =
{
    /*      ------ 2666-2933MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 749,          682,            23      },
    { 749,          682,            24      },
    { 749,          682,            25      },
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            22      },
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2933Y_3DS3A_cas_cfgs[] =
{
    /*      ------ 2666-2933MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 749,          682,            24      },
    { 749,          682,            25      },
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            22      },
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_2933AA_3DS43A_cas_cfgs[] =
{
    /*      ------ 2666-2933MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 749,          682,            25      },
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};

/* 3200 MHz */
static const ddr4_3ds_cas_cfg_t ddr4_3200W_3DS4A_cas_cfgs[] =
{
    /*      ------ 2933-3200MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 681,          625,            24      },
    { 681,          625,            26      },
    { 681,          625,            28      },
    /*      ------ 2666-2933MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 749,          682,            23      },
    { 749,          682,            24      },
    { 749,          682,            25      },
    { 749,          682,            26      },
    { 749,          682,            27      },
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            20      },
    { 832,          750,            22      },
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           15      },
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_3200AA_3DS4A_cas_cfgs[] =
{
    /*      ------ 2933-3200MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 681,          625,            26      },
    { 681,          625,            28      },
    /*      ------ 2666-2933MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 749,          682,            24      },
    { 749,          682,            25      },
    { 749,          682,            26      },
    { 749,          682,            27      },
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            22      },
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            20      },
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            18      },
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           13      },
    { 1500,         1250,           14      }
};
static const ddr4_3ds_cas_cfg_t ddr4_3200AC_3DS4A_cas_cfgs[] =
{
    /*      ------ 2933-3200MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 681,          625,            28      },
    /*      ------ 2666-2933MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 749,          682,            26      },
    { 749,          682,            27      },
    /*      ------ 2400-2666MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 832,          750,            24      },
    /*      ------ 2133-2400MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 937,          833,            22      },
    /*      ------ 1866-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1070,         938,            20      },
    /*      ------ 1600-2133MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1249,         1071,           16      },
    /*      ------ 1333-1600MHz ------      */
	/*MAX_TCK_PS    MIN_TCK_PS      CL      */
    { 1500,         1250,           14      }
};

/**
 * @brief Table containing speed grades' Speed Bin timings found in JEDEC's JESD79-4-1B specification (Tables [22-28])
 *
 */
static const ddr4_speedbin_t ddr4_3ds_speedbin_table[] = {
/*  --------------------1600MHz--------------------              --------------------1600MHz--------------------             --------------------1600MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_1600J_3DS2B,    15000,   21500,  13750,  12500,   35000,  47500, {.spec_3ds={10,  9,   ddr4_1600J_3DS2B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_1600J_3DS2B_cas_cfgs)   },
{ DWC_DDR4_1600K_3DS2B,    16250,   21500,  15000,  13750,   35000,  48750, {.spec_3ds={10,  10,  ddr4_1600K_3DS2B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_1600K_3DS2B_cas_cfgs)   },
{ DWC_DDR4_1600L_3DS2B,    17500,   21500,  16250,  15000,   35000,  50000, {.spec_3ds={11,  10,  ddr4_1600L_3DS2B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_1600L_3DS2B_cas_cfgs)   },
/*  --------------------1866MHz--------------------              --------------------1866MHz--------------------             --------------------1866MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_1866L_3DS2B,    15000,   21500,  13920,  12850,   34000,  46850, {.spec_3ds={10,  9,   ddr4_1866L_3DS2B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_1866L_3DS2B_cas_cfgs)   },
{ DWC_DDR4_1866M_3DS2B,    16070,   21500,  15000,  13920,   34000,  47920, {.spec_3ds={10,  10,  ddr4_1866M_3DS2B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_1866M_3DS2B_cas_cfgs)   },
{ DWC_DDR4_1866N_3DS2B,    17140,   21500,  16070,  15000,   34000,  49000, {.spec_3ds={11,  10,  ddr4_1866N_3DS2B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_1866N_3DS2B_cas_cfgs)   },
/*  --------------------2133MHz--------------------              --------------------2133MHz--------------------             --------------------2133MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_2133P_3DS2A,    15950,   21500,  14060,  14060,   33000,  47060, {.spec_3ds={10,  10,  ddr4_2133P_3DS2A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2133P_3DS2A_cas_cfgs)   },
{ DWC_DDR4_2133P_3DS3A,    16880,   21500,  14060,  14060,   33000,  47060, {.spec_3ds={10,  10,  ddr4_2133P_3DS3A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2133P_3DS3A_cas_cfgs)   },
{ DWC_DDR4_2133R_3DS4A,    18760,   21500,  15000,  15000,   33000,  48000, {.spec_3ds={11,  10,  ddr4_2133R_3DS4A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2133R_3DS4A_cas_cfgs)   },
/*  --------------------2400MHz--------------------              --------------------2400MHz--------------------             --------------------2400MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_2400P_3DS3B,    15000,   21500,  13330,  12500,   32000,  44500, {.spec_3ds={9,   9,   ddr4_2400P_3DS3B_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2400P_3DS3B_cas_cfgs)   },
{ DWC_DDR4_2400T_3DS2A,    15830,   21500,  14160,  14160,   32000,  46160, {.spec_3ds={10,  10,  ddr4_2400T_3DS2A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2400T_3DS2A_cas_cfgs)   },
{ DWC_DDR4_2400U_3DS2A,    16670,   21500,  15000,  15000,   32000,  47000, {.spec_3ds={10,  10,  ddr4_2400U_3DS2A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2400U_3DS2A_cas_cfgs)   },
{ DWC_DDR4_2400U_3DS4A,    18330,   21500,  15000,  15000,   32000,  47000, {.spec_3ds={11,  10,  ddr4_2400U_3DS4A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2400U_3DS4A_cas_cfgs)   },
/*  --------------------2666MHz--------------------              --------------------2666MHz--------------------             --------------------2666MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_2666T_3DS3A,    15000,   21500,  12750,  12750,   32000,  44750, {.spec_3ds={11,  10,  ddr4_2666T_3DS3A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2666T_3DS3A_cas_cfgs)   },
{ DWC_DDR4_2666V_3DS3A,    16500,   21500,  14250,  14250,   32000,  46250, {.spec_3ds={12,  12,  ddr4_2666V_3DS3A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2666V_3DS3A_cas_cfgs)   },
{ DWC_DDR4_2666W_3DS4A,    18000,   21500,  15000,  15000,   32000,  47000, {.spec_3ds={12,  12,  ddr4_2666W_3DS4A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2666W_3DS4A_cas_cfgs)   },
// /*  --------------------2933MHz--------------------              --------------------2933MHz--------------------             --------------------2933MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_2933W_3DS3A,    15690,   21500,  13640,  13640,   32000,  45640, {.spec_3ds={10,  10,  ddr4_2933W_3DS3A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2933W_3DS3A_cas_cfgs)   },
{ DWC_DDR4_2933Y_3DS3A,    16370,   21500,  14320,  14320,   32000,  46320, {.spec_3ds={10,  10,  ddr4_2933Y_3DS3A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_2933Y_3DS3A_cas_cfgs)   },
{ DWC_DDR4_2933AA_3DS43A,  17050,   21500,  15000,  15000,   32000,  47000, {.spec_3ds={10,  10,  ddr4_2933AA_3DS43A_cas_cfgs}},  GET_ARR_NELEMS(ddr4_2933AA_3DS43A_cas_cfgs) },
/*  --------------------3200MHz--------------------              --------------------3200MHz--------------------             --------------------3200MHz--------------------  */
/* Speed grade             tAA min tAA max  tRCD    tRP    tRAS min   tRC              nRCD  nRP          CL table                        NumberOfValidCasConfigs             */
{ DWC_DDR4_3200W_3DS4A,    15000,   21500,  12500,  12500,   32000,  44500, {.spec_3ds={11,  10,  ddr4_3200W_3DS4A_cas_cfgs  }},  GET_ARR_NELEMS(ddr4_3200W_3DS4A_cas_cfgs)   },
{ DWC_DDR4_3200AA_3DS4A,   16250,   21500,  13750,  13750,   32000,  45750, {.spec_3ds={12,  11,  ddr4_3200AA_3DS4A_cas_cfgs }},  GET_ARR_NELEMS(ddr4_3200AA_3DS4A_cas_cfgs)  },
{ DWC_DDR4_3200AC_3DS4A,   17500,   21500,  15000,  15000,   32000,  47000, {.spec_3ds={12,  12,  ddr4_3200AC_3DS4A_cas_cfgs }},  GET_ARR_NELEMS(ddr4_3200AC_3DS4A_cas_cfgs)  }
};



void get_ddr4_3ds_speedbin_table(const ddr4_speedbin_t** table_ptr, uint8_t* const n_sgs)
{
    *table_ptr = ddr4_3ds_speedbin_table;
    *n_sgs = GET_ARR_NELEMS(ddr4_3ds_speedbin_table);
}

#endif /* JESD79_4_1_B_DDR4_3DS_SPEEDBINS */
