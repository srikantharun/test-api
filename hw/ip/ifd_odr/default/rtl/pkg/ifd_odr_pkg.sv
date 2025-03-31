// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IFD ODR package containing all needed parameters
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_PKG_SV_
`define _IFD_ODR_PKG_SV_

package ifd_odr_pkg;

  parameter logic [7:0] IFD_ODR_IFD_HW_REVISION = 'b10;
  parameter logic [7:0] IFD_ODR_ODR_HW_REVISION = 'b10;

  parameter int IFD_ODR_DP_AW = 32;
  parameter int IFD_ODR_PWORD64_LEN = aic_common_pkg::AIC_PWORD_SIZE;
  parameter int IFD_ODR_PWORD32_LEN = aic_common_pkg::AIC_PWORD32_SIZE;
  parameter int IFD_ODR_PWORD64_LEN_BITS = $clog2(IFD_ODR_PWORD64_LEN);
  parameter int IFD_ODR_EL_DW = aic_common_pkg::AIC_PWORD_WIDTH / aic_common_pkg::AIC_PWORD32_SIZE;
  parameter int IFD_ODR_EL8_DW = aic_common_pkg::AIC_PWORD_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  parameter int IFD_ODR_AG_RING_BUFFER_SIZE_GRANULARITY = 64 * IFD_ODR_PWORD64_LEN;
  parameter int IFD_ODR_AG_RING_BUFFER_FLOPS = 3;

   // aipu_addr_map_pkg::AI_CORE_0__L1_MEMORY_ST_ADDR:
  parameter logic [35:0] IFD_ODR_L1_MEMORY_ST_ADDR = 'h1800000;

  parameter int unsigned IFD_ODR_NR_AXI_DEVS = 3;
  parameter int unsigned IFD_ODR_CSR_S_IDX = 0;
  parameter int unsigned IFD_ODR_CSR_ST_ADDR = 'h0000;
  parameter int unsigned IFD_ODR_CSR_CAP = 'h1000;
  parameter int unsigned IFD_ODR_CSR_ADDR_MSB = $clog2('h1000);
  parameter int unsigned IFD_ODR_CMDB_S_IDX = 1;
  parameter int unsigned IFD_ODR_CMDB_ST_ADDR = 'h1000;
  parameter int unsigned IFD_ODR_CMDB_CAP = 'h1000;
  parameter int unsigned IFD_ODR_CMDB_ADDR_MSB = $clog2('h1000);
  parameter int unsigned IFD_ODR_DEFMEM_S_IDX = 2;
  parameter int unsigned IFD_ODR_DEFMEM_ST_ADDR = 'h8000;
  parameter int unsigned IFD_ODR_DEFMEM_CAP = 'h8000;  // count on memory to do the required address checking
  parameter int unsigned IFD_ODR_DEFMEM_ADDR_MSB = $clog2('h10000);

  parameter int IFD_ODR_DEFMEM_WIDTH = 64;
  parameter int IFD_ODR_DEFMEM_MAX_LOOPS = 4;  /* goes hand in hand with address gen itself */

  parameter int  IFD_ODR_DPC_DATA_W = IFD_ODR_DP_AW + IFD_ODR_PWORD64_LEN + IFD_ODR_EL_DW + 2;

  parameter int IFD_ODR_AG_CMD_NR_FIELDS = 41;

  // AG CMD int Field sizes
  parameter int IFD_ODR_AG_DIM_W_A_DW = 16;
  parameter int IFD_ODR_AG_DIM_W_B_DW = 16;
  parameter int IFD_ODR_AG_DIM_W_C_DW = 16;
  parameter int IFD_ODR_AG_DIM_W_D_DW = 16;
  parameter int IFD_ODR_AG_DIM_OFF_A_DW = 16;
  parameter int IFD_ODR_AG_DIM_OFF_B_DW = 16;
  parameter int IFD_ODR_AG_DIM_OFF_C_DW = 16;
  parameter int IFD_ODR_AG_DIM_OFF_D_DW = 16;
  parameter int IFD_ODR_AG_INNER_LEN_A_DW = 16;
  parameter int IFD_ODR_AG_INNER_LEN_B_DW = 16;
  parameter int IFD_ODR_AG_INNER_LEN_C_DW = 16;
  parameter int IFD_ODR_AG_INNER_LEN_D_DW = 16;
  parameter int IFD_ODR_AG_OUTER_LEN_A_DW = 16;
  parameter int IFD_ODR_AG_OUTER_LEN_B_DW = 16;
  parameter int IFD_ODR_AG_OUTER_LEN_C_DW = 16;
  parameter int IFD_ODR_AG_OUTER_LEN_D_DW = 16;
  parameter int IFD_ODR_AG_INNER_STR_A_DW = 8;
  parameter int IFD_ODR_AG_INNER_STR_B_DW = 8;
  parameter int IFD_ODR_AG_INNER_STR_C_DW = 8;
  parameter int IFD_ODR_AG_INNER_STR_D_DW = 8;
  parameter int IFD_ODR_AG_OUTER_STR_A_DW = 8;
  parameter int IFD_ODR_AG_OUTER_STR_B_DW = 8;
  parameter int IFD_ODR_AG_OUTER_STR_C_DW = 8;
  parameter int IFD_ODR_AG_OUTER_STR_D_DW = 8;
  parameter int IFD_ODR_AG_MSK_START_DW = $clog2(IFD_ODR_PWORD64_LEN);
  parameter int IFD_ODR_AG_MSK_END_DW = $clog2(IFD_ODR_PWORD64_LEN + 1);
  // memory access info:
  parameter int IFD_ODR_AG_MEM_BASE_DW = IFD_ODR_DP_AW;
  parameter int IFD_ODR_AG_MEM_BSIZE_DW = 32;
  parameter int IFD_ODR_AG_MEM_STRIDE_A_DW = 32;
  parameter int IFD_ODR_AG_MEM_STRIDE_B_DW = 32;
  parameter int IFD_ODR_AG_MEM_STRIDE_C_DW = 32;
  parameter int IFD_ODR_AG_MEM_STRIDE_D_DW = 32;
  parameter int IFD_ODR_AG_MEM_OFFSET_DW = 32;
  parameter int IFD_ODR_AG_RING_BUFFER_SIZE_DW = 22;
  parameter int IFD_ODR_AG_PAD_VAL_DW = IFD_ODR_EL_DW;
  parameter int IFD_ODR_AG_INTRA_PAD_VAL_DW = IFD_ODR_EL_DW;
  parameter int IFD_ODR_AG_PAD_MODE_EDGE_DW = 1;
  parameter int IFD_ODR_AG_VTRSP_EN_DW = 2;
  parameter int IFD_ODR_AG_VECT_DIM_DW = 2;
  parameter int IFD_ODR_AG_DECOMP_EN_DW = 1;
  parameter int IFD_ODR_AG_FORMAT_DW = 1;

  parameter int IFD_ODR_AG_IFD_ODR_CMD_FIELD_SIZES[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_DIM_W_A_DW,
    IFD_ODR_AG_DIM_W_B_DW,
    IFD_ODR_AG_DIM_W_C_DW,
    IFD_ODR_AG_DIM_W_D_DW,
    IFD_ODR_AG_DIM_OFF_A_DW,
    IFD_ODR_AG_DIM_OFF_B_DW,
    IFD_ODR_AG_DIM_OFF_C_DW,
    IFD_ODR_AG_DIM_OFF_D_DW,
    IFD_ODR_AG_INNER_LEN_A_DW,
    IFD_ODR_AG_INNER_LEN_B_DW,
    IFD_ODR_AG_INNER_LEN_C_DW,
    IFD_ODR_AG_INNER_LEN_D_DW,
    IFD_ODR_AG_OUTER_LEN_A_DW,
    IFD_ODR_AG_OUTER_LEN_B_DW,
    IFD_ODR_AG_OUTER_LEN_C_DW,
    IFD_ODR_AG_OUTER_LEN_D_DW,
    IFD_ODR_AG_INNER_STR_A_DW,
    IFD_ODR_AG_INNER_STR_B_DW,
    IFD_ODR_AG_INNER_STR_C_DW,
    IFD_ODR_AG_INNER_STR_D_DW,
    IFD_ODR_AG_OUTER_STR_A_DW,
    IFD_ODR_AG_OUTER_STR_B_DW,
    IFD_ODR_AG_OUTER_STR_C_DW,
    IFD_ODR_AG_OUTER_STR_D_DW,
    IFD_ODR_AG_MSK_START_DW,
    IFD_ODR_AG_MSK_END_DW,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_DW,
    IFD_ODR_AG_MEM_BSIZE_DW,
    IFD_ODR_AG_MEM_STRIDE_A_DW,
    IFD_ODR_AG_MEM_STRIDE_B_DW,
    IFD_ODR_AG_MEM_STRIDE_C_DW,
    IFD_ODR_AG_MEM_STRIDE_D_DW,
    IFD_ODR_AG_MEM_OFFSET_DW,
    IFD_ODR_AG_RING_BUFFER_SIZE_DW,
    IFD_ODR_AG_PAD_VAL_DW,
    IFD_ODR_AG_INTRA_PAD_VAL_DW,
    IFD_ODR_AG_PAD_MODE_EDGE_DW,
    IFD_ODR_AG_VTRSP_EN_DW,
    IFD_ODR_AG_VECT_DIM_DW,
    IFD_ODR_AG_DECOMP_EN_DW,
    IFD_ODR_AG_FORMAT_DW
  };

  // CMD Field LSB idx's:
  parameter int IFD_ODR_AG_DIM_W_A_LSB = 208;
  parameter int IFD_ODR_AG_DIM_W_B_LSB = 272;
  parameter int IFD_ODR_AG_DIM_W_C_LSB = 336;
  parameter int IFD_ODR_AG_DIM_OFF_A_LSB = 192;
  parameter int IFD_ODR_AG_DIM_OFF_B_LSB = 256;
  parameter int IFD_ODR_AG_DIM_OFF_C_LSB = 320;
  parameter int IFD_ODR_AG_INNER_LEN_A_LSB = 384;
  parameter int IFD_ODR_AG_INNER_LEN_B_LSB = 448;
  parameter int IFD_ODR_AG_INNER_LEN_C_LSB = 128;
  parameter int IFD_ODR_AG_OUTER_LEN_A_LSB = 400;
  parameter int IFD_ODR_AG_OUTER_LEN_B_LSB = 464;
  parameter int IFD_ODR_AG_OUTER_LEN_C_LSB = 432;
  parameter int IFD_ODR_AG_INNER_STR_A_LSB = 416;
  parameter int IFD_ODR_AG_INNER_STR_B_LSB = 480;
  parameter int IFD_ODR_AG_INNER_STR_C_LSB = 496;
  parameter int IFD_ODR_AG_OUTER_STR_A_LSB = 424;
  parameter int IFD_ODR_AG_OUTER_STR_B_LSB = 488;
  parameter int IFD_ODR_AG_OUTER_STR_C_LSB = 504;
  parameter int IFD_ODR_AG_MSK_START_LSB = 144;
  parameter int IFD_ODR_AG_MSK_END_LSB = 152;
  // memory access info:
  parameter int IFD_ODR_AG_MEM_BASE_LSB = 0;
  parameter int IFD_ODR_AG_MEM_BSIZE_LSB = 160;
  parameter int IFD_ODR_AG_MEM_STRIDE_A_LSB = 224;
  parameter int IFD_ODR_AG_MEM_STRIDE_B_LSB = 288;
  parameter int IFD_ODR_AG_MEM_STRIDE_C_LSB = 352;
  parameter int IFD_ODR_AG_MEM_OFFSET_LSB = 64;
  parameter int IFD_ODR_AG_RING_BUFFER_SIZE_LSB = 96;
  parameter int IFD_ODR_AG_PAD_VAL_LSB = 32;
  parameter int IFD_ODR_AG_INTRA_PAD_VAL_LSB = 48;
  parameter int IFD_ODR_AG_SETTINGS_LSB = 120;
  parameter int IFD_ODR_AG_VECT_DIM_LSB      = IFD_ODR_AG_SETTINGS_LSB + 2;  // settings bit 3:2
  parameter int IFD_ODR_AG_VTRSP_EN_LSB      = IFD_ODR_AG_SETTINGS_LSB + 4;  // settings bit 5:4
  parameter int IFD_ODR_AG_PAD_MODE_EDGE_LSB = IFD_ODR_AG_SETTINGS_LSB + 6;  // settings bit 6
  parameter int IFD_ODR_AG_FORMAT_LSB        = IFD_ODR_AG_SETTINGS_LSB + 7;  // for now just placing it in some empty spot
  parameter int IFD_ODR_AG_DECOMP_EN_LSB     = 640;  // for now just placing it in some empty spot

  // loop D at the end:
  parameter int IFD_ODR_AG_DIM_OFF_D_LSB = 512;
  parameter int IFD_ODR_AG_DIM_W_D_LSB = 528;
  parameter int IFD_ODR_AG_MEM_STRIDE_D_LSB = 544;
  parameter int IFD_ODR_AG_INNER_LEN_D_LSB = 576;
  parameter int IFD_ODR_AG_INNER_STR_D_LSB = 592;
  parameter int IFD_ODR_AG_OUTER_LEN_D_LSB = 608;
  parameter int IFD_ODR_AG_OUTER_STR_D_LSB = 624;

  parameter int IFD_ODR_CMDB_MAX_CMD_DW = 641;

  // extended defmem contents (unpack can select, but won't end up in AG)
  parameter int IFD_ODR_DM_BASE_LSB = IFD_ODR_CMDB_MAX_CMD_DW;
  parameter int IFD_ODR_DM_BASE_DIM_W_A_LSB = IFD_ODR_DM_BASE_LSB;
  parameter int IFD_ODR_DM_BASE_DIM_W_B_LSB = IFD_ODR_DM_BASE_DIM_W_A_LSB + IFD_ODR_AG_DIM_W_A_DW;
  parameter int IFD_ODR_DM_BASE_DIM_W_C_LSB = IFD_ODR_DM_BASE_DIM_W_B_LSB + IFD_ODR_AG_DIM_W_B_DW;
  parameter int IFD_ODR_DM_BASE_DIM_W_D_LSB = IFD_ODR_DM_BASE_DIM_W_C_LSB + IFD_ODR_AG_DIM_W_C_DW;
  parameter int IFD_ODR_DM_BASE_DIM_OFF_A_LSB = IFD_ODR_DM_BASE_DIM_W_D_LSB + IFD_ODR_AG_DIM_W_D_DW;
  parameter int IFD_ODR_DM_BASE_DIM_OFF_B_LSB = IFD_ODR_DM_BASE_DIM_OFF_A_LSB + IFD_ODR_AG_DIM_OFF_A_DW;
  parameter int IFD_ODR_DM_BASE_DIM_OFF_C_LSB = IFD_ODR_DM_BASE_DIM_OFF_B_LSB + IFD_ODR_AG_DIM_OFF_B_DW;
  parameter int IFD_ODR_DM_BASE_DIM_OFF_D_LSB = IFD_ODR_DM_BASE_DIM_OFF_C_LSB + IFD_ODR_AG_DIM_OFF_C_DW;
  parameter int IFD_ODR_DM_BASE_STRIDE_A_LSB = IFD_ODR_DM_BASE_DIM_OFF_D_LSB + IFD_ODR_AG_DIM_OFF_D_DW;
  parameter int IFD_ODR_DM_BASE_STRIDE_B_LSB = IFD_ODR_DM_BASE_STRIDE_A_LSB + IFD_ODR_AG_MEM_STRIDE_A_DW;
  parameter int IFD_ODR_DM_BASE_STRIDE_C_LSB = IFD_ODR_DM_BASE_STRIDE_B_LSB + IFD_ODR_AG_MEM_STRIDE_B_DW;
  parameter int IFD_ODR_DM_BASE_STRIDE_D_LSB = IFD_ODR_DM_BASE_STRIDE_C_LSB + IFD_ODR_AG_MEM_STRIDE_C_DW;
  parameter int IFD_ODR_DM_BASE_INNER_LEN_A_LSB = IFD_ODR_DM_BASE_STRIDE_D_LSB + IFD_ODR_AG_MEM_STRIDE_D_DW;
  parameter int IFD_ODR_DM_BASE_INNER_LEN_B_LSB = IFD_ODR_DM_BASE_INNER_LEN_A_LSB + IFD_ODR_AG_INNER_LEN_A_DW;
  parameter int IFD_ODR_DM_BASE_INNER_LEN_C_LSB = IFD_ODR_DM_BASE_INNER_LEN_B_LSB + IFD_ODR_AG_INNER_LEN_B_DW;
  parameter int IFD_ODR_DM_BASE_INNER_LEN_D_LSB = IFD_ODR_DM_BASE_INNER_LEN_C_LSB + IFD_ODR_AG_INNER_LEN_C_DW;
  parameter int IFD_ODR_DM_BASE_INNER_STR_A_LSB = IFD_ODR_DM_BASE_INNER_LEN_D_LSB + IFD_ODR_AG_INNER_LEN_D_DW;
  parameter int IFD_ODR_DM_BASE_INNER_STR_B_LSB = IFD_ODR_DM_BASE_INNER_STR_A_LSB + IFD_ODR_AG_INNER_STR_A_DW;
  parameter int IFD_ODR_DM_BASE_INNER_STR_C_LSB = IFD_ODR_DM_BASE_INNER_STR_B_LSB + IFD_ODR_AG_INNER_STR_B_DW;
  parameter int IFD_ODR_DM_BASE_INNER_STR_D_LSB = IFD_ODR_DM_BASE_INNER_STR_C_LSB + IFD_ODR_AG_INNER_STR_C_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_LEN_A_LSB = IFD_ODR_DM_BASE_INNER_STR_D_LSB + IFD_ODR_AG_INNER_STR_D_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_LEN_B_LSB = IFD_ODR_DM_BASE_OUTER_LEN_A_LSB + IFD_ODR_AG_OUTER_LEN_A_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_LEN_C_LSB = IFD_ODR_DM_BASE_OUTER_LEN_B_LSB + IFD_ODR_AG_OUTER_LEN_B_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_LEN_D_LSB = IFD_ODR_DM_BASE_OUTER_LEN_C_LSB + IFD_ODR_AG_OUTER_LEN_C_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_STR_A_LSB = IFD_ODR_DM_BASE_OUTER_LEN_D_LSB + IFD_ODR_AG_OUTER_LEN_D_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_STR_B_LSB = IFD_ODR_DM_BASE_OUTER_STR_A_LSB + IFD_ODR_AG_OUTER_STR_A_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_STR_C_LSB = IFD_ODR_DM_BASE_OUTER_STR_B_LSB + IFD_ODR_AG_OUTER_STR_B_DW;
  parameter int IFD_ODR_DM_BASE_OUTER_STR_D_LSB = IFD_ODR_DM_BASE_OUTER_STR_C_LSB + IFD_ODR_AG_OUTER_STR_C_DW;

  parameter int IFD_ODR_DM_BASE_MSB = IFD_ODR_DM_BASE_OUTER_STR_D_LSB + IFD_ODR_AG_OUTER_STR_D_DW - 1;
  parameter int IFD_ODR_DM_BASE_DW = IFD_ODR_DM_BASE_MSB - IFD_ODR_DM_BASE_LSB + 1;

  parameter int IFD_ODR_UNROLL_CMD_DW = IFD_ODR_CMDB_MAX_CMD_DW + IFD_ODR_DM_BASE_DW;

  parameter int IFD_ODR_CMD_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_DIM_W_A_LSB,
    IFD_ODR_AG_DIM_W_B_LSB,
    IFD_ODR_AG_DIM_W_C_LSB,
    IFD_ODR_AG_DIM_W_D_LSB,
    IFD_ODR_AG_DIM_OFF_A_LSB,
    IFD_ODR_AG_DIM_OFF_B_LSB,
    IFD_ODR_AG_DIM_OFF_C_LSB,
    IFD_ODR_AG_DIM_OFF_D_LSB,
    IFD_ODR_AG_INNER_LEN_A_LSB,
    IFD_ODR_AG_INNER_LEN_B_LSB,
    IFD_ODR_AG_INNER_LEN_C_LSB,
    IFD_ODR_AG_INNER_LEN_D_LSB,
    IFD_ODR_AG_OUTER_LEN_A_LSB,
    IFD_ODR_AG_OUTER_LEN_B_LSB,
    IFD_ODR_AG_OUTER_LEN_C_LSB,
    IFD_ODR_AG_OUTER_LEN_D_LSB,
    IFD_ODR_AG_INNER_STR_A_LSB,
    IFD_ODR_AG_INNER_STR_B_LSB,
    IFD_ODR_AG_INNER_STR_C_LSB,
    IFD_ODR_AG_INNER_STR_D_LSB,
    IFD_ODR_AG_OUTER_STR_A_LSB,
    IFD_ODR_AG_OUTER_STR_B_LSB,
    IFD_ODR_AG_OUTER_STR_C_LSB,
    IFD_ODR_AG_OUTER_STR_D_LSB,
    IFD_ODR_AG_MSK_START_LSB,
    IFD_ODR_AG_MSK_END_LSB,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_LSB,
    IFD_ODR_AG_MEM_BSIZE_LSB,
    IFD_ODR_AG_MEM_STRIDE_A_LSB,
    IFD_ODR_AG_MEM_STRIDE_B_LSB,
    IFD_ODR_AG_MEM_STRIDE_C_LSB,
    IFD_ODR_AG_MEM_STRIDE_D_LSB,
    IFD_ODR_AG_MEM_OFFSET_LSB,
    IFD_ODR_AG_RING_BUFFER_SIZE_LSB,
    IFD_ODR_AG_PAD_VAL_LSB,
    IFD_ODR_AG_INTRA_PAD_VAL_LSB,
    IFD_ODR_AG_PAD_MODE_EDGE_LSB,
    IFD_ODR_AG_VTRSP_EN_LSB,
    IFD_ODR_AG_VECT_DIM_LSB,
    IFD_ODR_AG_FORMAT_LSB,
    IFD_ODR_AG_DECOMP_EN_LSB
  };

  // default values:
  parameter int IFD_ODR_AG_DIM_W_A_DEF_VAL = 1;
  parameter int IFD_ODR_AG_DIM_W_B_DEF_VAL = 1;
  parameter int IFD_ODR_AG_DIM_W_C_DEF_VAL = 64;
  parameter int IFD_ODR_AG_DIM_W_D_DEF_VAL = 1;
  parameter int IFD_ODR_AG_DIM_OFF_A_DEF_VAL = 0;
  parameter int IFD_ODR_AG_DIM_OFF_B_DEF_VAL = 0;
  parameter int IFD_ODR_AG_DIM_OFF_C_DEF_VAL = 0;
  parameter int IFD_ODR_AG_DIM_OFF_D_DEF_VAL = 0;
  parameter int IFD_ODR_AG_INNER_LEN_A_DEF_VAL = 1;
  parameter int IFD_ODR_AG_INNER_LEN_B_DEF_VAL = 1;
  parameter int IFD_ODR_AG_INNER_LEN_C_DEF_VAL = 1;
  parameter int IFD_ODR_AG_INNER_LEN_D_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_LEN_A_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_LEN_B_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_LEN_C_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_LEN_D_DEF_VAL = 1;
  parameter int IFD_ODR_AG_INNER_STR_A_DEF_VAL = 1;
  parameter int IFD_ODR_AG_INNER_STR_B_DEF_VAL = 1;
  parameter int IFD_ODR_AG_INNER_STR_C_DEF_VAL = 64;
  parameter int IFD_ODR_AG_INNER_STR_D_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_STR_A_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_STR_B_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_STR_C_DEF_VAL = 1;
  parameter int IFD_ODR_AG_OUTER_STR_D_DEF_VAL = 1;
  parameter int IFD_ODR_AG_MSK_START_DEF_VAL = 0;
  parameter int IFD_ODR_AG_MSK_END_DEF_VAL = 64;
  // memory access info:
  parameter int IFD_ODR_AG_MEM_BASE_DEF_VAL = 0;
  parameter int IFD_ODR_AG_MEM_BSIZE_DEF_VAL = 0;
  parameter int IFD_ODR_AG_MEM_STRIDE_A_DEF_VAL = 64;
  parameter int IFD_ODR_AG_MEM_STRIDE_B_DEF_VAL = 64;
  parameter int IFD_ODR_AG_MEM_STRIDE_C_DEF_VAL = 64;
  parameter int IFD_ODR_AG_MEM_STRIDE_D_DEF_VAL = 64;
  parameter int IFD_ODR_AG_MEM_OFFSET_DEF_VAL = 0;
  parameter int IFD_ODR_AG_RING_BUFFER_SIZE_DEF_VAL = 0;
  parameter int IFD_ODR_AG_PAD_VAL_DEF_VAL = 0;
  parameter int IFD_ODR_AG_INTRA_PAD_VAL_DEF_VAL = 0;
  parameter int IFD_ODR_AG_PAD_MODE_EDGE_DEF_VAL = 0;
  parameter int IFD_ODR_AG_VTRSP_EN_DEF_VAL = 0;
  parameter int IFD_ODR_AG_VECT_DIM_DEF_VAL = 0;
  parameter int IFD_ODR_AG_FORMAT_DEF_VAL = 0;
  parameter int IFD_ODR_AG_DECOMP_EN_DEF_VAL = 0;

  parameter longint IFD_ODR_AG_CMD_DEF_VALS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_DIM_W_A_DEF_VAL,
    IFD_ODR_AG_DIM_W_B_DEF_VAL,
    IFD_ODR_AG_DIM_W_C_DEF_VAL,
    IFD_ODR_AG_DIM_W_D_DEF_VAL,
    IFD_ODR_AG_DIM_OFF_A_DEF_VAL,
    IFD_ODR_AG_DIM_OFF_B_DEF_VAL,
    IFD_ODR_AG_DIM_OFF_C_DEF_VAL,
    IFD_ODR_AG_DIM_OFF_D_DEF_VAL,
    IFD_ODR_AG_INNER_LEN_A_DEF_VAL,
    IFD_ODR_AG_INNER_LEN_B_DEF_VAL,
    IFD_ODR_AG_INNER_LEN_C_DEF_VAL,
    IFD_ODR_AG_INNER_LEN_D_DEF_VAL,
    IFD_ODR_AG_OUTER_LEN_A_DEF_VAL,
    IFD_ODR_AG_OUTER_LEN_B_DEF_VAL,
    IFD_ODR_AG_OUTER_LEN_C_DEF_VAL,
    IFD_ODR_AG_OUTER_LEN_D_DEF_VAL,
    IFD_ODR_AG_INNER_STR_A_DEF_VAL,
    IFD_ODR_AG_INNER_STR_B_DEF_VAL,
    IFD_ODR_AG_INNER_STR_C_DEF_VAL,
    IFD_ODR_AG_INNER_STR_D_DEF_VAL,
    IFD_ODR_AG_OUTER_STR_A_DEF_VAL,
    IFD_ODR_AG_OUTER_STR_B_DEF_VAL,
    IFD_ODR_AG_OUTER_STR_C_DEF_VAL,
    IFD_ODR_AG_OUTER_STR_D_DEF_VAL,
    IFD_ODR_AG_MSK_START_DEF_VAL,
    IFD_ODR_AG_MSK_END_DEF_VAL,
    IFD_ODR_AG_MEM_BASE_DEF_VAL,
    IFD_ODR_AG_MEM_BSIZE_DEF_VAL,
    IFD_ODR_AG_MEM_STRIDE_A_DEF_VAL,
    IFD_ODR_AG_MEM_STRIDE_B_DEF_VAL,
    IFD_ODR_AG_MEM_STRIDE_C_DEF_VAL,
    IFD_ODR_AG_MEM_STRIDE_D_DEF_VAL,
    IFD_ODR_AG_MEM_OFFSET_DEF_VAL,
    IFD_ODR_AG_RING_BUFFER_SIZE_DEF_VAL,
    IFD_ODR_AG_PAD_VAL_DEF_VAL,
    IFD_ODR_AG_INTRA_PAD_VAL_DEF_VAL,
    IFD_ODR_AG_PAD_MODE_EDGE_DEF_VAL,
    IFD_ODR_AG_VTRSP_EN_DEF_VAL,
    IFD_ODR_AG_VECT_DIM_DEF_VAL,
    IFD_ODR_AG_FORMAT_DEF_VAL,
    IFD_ODR_AG_DECOMP_EN_DEF_VAL
  };

  // DPC fields:
  parameter int  IFD_ODR_DPC_ADDR_FIELD_W = 40;
  parameter int  IFD_ODR_DPC_ADDR_DW = IFD_ODR_DP_AW;
  parameter int  IFD_ODR_DPC_MSK_DW = IFD_ODR_PWORD64_LEN;
  parameter int  IFD_ODR_DPC_PAD_VAL_DW = IFD_ODR_EL_DW;
  parameter int  IFD_ODR_DPC_INTRA_PAD_VAL_DW = IFD_ODR_EL_DW;
  parameter int  IFD_ODR_DPC_CTRL_FIELD_W = 8;
  parameter int  IFD_ODR_DPC_CTRL_DW = 5;
  // detaileint d ctrl:
  parameter int  IFD_ODR_DPC_PAD_DW = 1;
  parameter int  IFD_ODR_DPC_LAST_DW = 1;
  parameter int  IFD_ODR_DPC_VTRSP_EN_DW = 2;
  parameter int  IFD_ODR_DPC_DECOMP_EN_DW = 1;
  parameter int  IFD_ODR_DPC_FORMAT_DW = 1;

  parameter int  IFD_ODR_DPC_ADDR_LSB          = 0;
  parameter int  IFD_ODR_DPC_PAD_VAL_LSB       = IFD_ODR_DPC_ADDR_LSB + IFD_ODR_DPC_ADDR_FIELD_W;
  parameter int  IFD_ODR_DPC_INTRA_PAD_VAL_LSB = IFD_ODR_DPC_PAD_VAL_LSB + IFD_ODR_DPC_PAD_VAL_DW;
  parameter int  IFD_ODR_DPC_CTRL_LSB          = IFD_ODR_DPC_INTRA_PAD_VAL_LSB + IFD_ODR_DPC_INTRA_PAD_VAL_DW;
  parameter int  IFD_ODR_DPC_MSK_LSB           = IFD_ODR_DPC_CTRL_LSB + IFD_ODR_DPC_CTRL_FIELD_W;
  parameter int  IFD_ODR_DPC_FORMAT_LSB        = IFD_ODR_DPC_MSK_LSB + IFD_ODR_DPC_MSK_DW;

  // detaileint d ctrl:
  parameter int  IFD_ODR_DPC_LAST_LSB      = IFD_ODR_DPC_CTRL_LSB+0;
  parameter int  IFD_ODR_DPC_PAD_LSB       = IFD_ODR_DPC_CTRL_LSB+1;
  parameter int  IFD_ODR_DPC_VTRSP_EN_LSB  = IFD_ODR_DPC_CTRL_LSB+2;
  parameter int  IFD_ODR_DPC_DECOMP_EN_LSB = IFD_ODR_DPC_CTRL_LSB+4;

  parameter int IFD_ODR_AG_CMD_DW = IFD_ODR_CMDB_MAX_CMD_DW;  // last field+size
  parameter int IFD_ODR_DPC_CMD_DW = IFD_ODR_DPC_FORMAT_LSB + IFD_ODR_DPC_FORMAT_DW; //137;

  /////////////////////////////////////////////////////////////////////////////
  ////////////////////////////  COMMAND FORMATS  //////////////////////////////
  // "normal" / fall-back
  parameter int IFD_ODR_CMD_FALLBACK_FMT = 2;
  parameter int IFD_ODR_CMD_FALLBACK_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_DIM_W_A_LSB,
    IFD_ODR_AG_DIM_W_B_LSB,
    IFD_ODR_AG_DIM_W_C_LSB,
    -1  /*IFD_ODR_AG_DIM_W_D_LSB*/,
    IFD_ODR_AG_DIM_OFF_A_LSB,
    IFD_ODR_AG_DIM_OFF_B_LSB,
    IFD_ODR_AG_DIM_OFF_C_LSB,
    -1  /*IFD_ODR_AG_DIM_OFF_D_LSB*/,
    IFD_ODR_AG_INNER_LEN_A_LSB,
    IFD_ODR_AG_INNER_LEN_B_LSB,
    IFD_ODR_AG_INNER_LEN_C_LSB,
    -1  /*IFD_ODR_AG_INNER_LEN_D_LSB*/,
    IFD_ODR_AG_OUTER_LEN_A_LSB,
    IFD_ODR_AG_OUTER_LEN_B_LSB,
    IFD_ODR_AG_OUTER_LEN_C_LSB,
    -1  /*IFD_ODR_AG_OUTER_LEN_D_LSB*/,
    IFD_ODR_AG_INNER_STR_A_LSB,
    IFD_ODR_AG_INNER_STR_B_LSB,
    IFD_ODR_AG_INNER_STR_C_LSB,
    -1  /*IFD_ODR_AG_INNER_STR_D_LSB*/,
    IFD_ODR_AG_OUTER_STR_A_LSB,
    IFD_ODR_AG_OUTER_STR_B_LSB,
    IFD_ODR_AG_OUTER_STR_C_LSB,
    -1  /*IFD_ODR_AG_OUTER_STR_D_LSB*/,
    IFD_ODR_AG_MSK_START_LSB,
    IFD_ODR_AG_MSK_END_LSB,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_LSB,
    IFD_ODR_AG_MEM_BSIZE_LSB,
    IFD_ODR_AG_MEM_STRIDE_A_LSB,
    IFD_ODR_AG_MEM_STRIDE_B_LSB,
    IFD_ODR_AG_MEM_STRIDE_C_LSB,
    -1  /*IFD_ODR_AG_MEM_STRIDE_D_LSB*/,
    IFD_ODR_AG_MEM_OFFSET_LSB,
    IFD_ODR_AG_RING_BUFFER_SIZE_LSB,
    IFD_ODR_AG_PAD_VAL_LSB,
    IFD_ODR_AG_INTRA_PAD_VAL_LSB,
    IFD_ODR_AG_PAD_MODE_EDGE_LSB,
    IFD_ODR_AG_VTRSP_EN_LSB,
    IFD_ODR_AG_VECT_DIM_LSB,
    IFD_ODR_AG_FORMAT_LSB,
    -1  /*IFD_ODR_AG_DECOMP_EN_LSB*/  // no decomp in normal command
  };

  // linear:
  parameter int IFD_ODR_CMD_LINEAR_FMT = 1;
  parameter int IFD_ODR_AG_LIN_MEM_BASE_LSB = 0;
  parameter int IFD_ODR_AG_LIN_DECOMP_EN_LSB = 40;
  parameter int IFD_ODR_AG_LIN_LENGTH_LSB = 48;  // use A location for mapping
  parameter int IFD_ODR_AG_LIN_CMD_DW = 64;
  parameter int IFD_ODR_CMD_LIN_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_LIN_LENGTH_LSB  /*IFD_ODR_AG_DIM_W_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_W_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_W_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_W_D_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_OFF_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_OFF_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_OFF_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_DIM_OFF_D_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_LEN_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_LEN_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_LEN_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_LEN_D_DEF_VAL*/,
    IFD_ODR_AG_LIN_LENGTH_LSB  /*IFD_ODR_AG_OUTER_LEN_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_LEN_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_LEN_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_LEN_D_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_STR_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_STR_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_STR_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INNER_STR_D_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_STR_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_STR_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_STR_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_OUTER_STR_D_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MSK_START_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MSK_END_DEF_VAL*/,
    IFD_ODR_AG_LIN_MEM_BASE_LSB  /*IFD_ODR_AG_MEM_BASE_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MEM_BSIZE_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MEM_STRIDE_A_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MEM_STRIDE_B_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MEM_STRIDE_C_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MEM_STRIDE_D_DEF_VAL*/,
    -1  /*IFD_ODR_AG_MEM_OFFSET_DEF_VAL*/,
    -1  /*IFD_ODR_AG_RING_BUFFER_SIZE_DEF_VAL*/,
    -1  /*IFD_ODR_AG_PAD_VAL_DEF_VAL*/,
    -1  /*IFD_ODR_AG_INTRA_PAD_VAL_DEF_VAL*/,
    -1  /*IFD_ODR_AG_PAD_MODE_EDGE_DEF_VAL*/,
    -1  /*IFD_ODR_AG_VTRSP_EN_DEF_VAL*/,
    -1  /*IFD_ODR_AG_VECT_DIM_DEF_VAL*/,
    -1  /*IFD_ODR_AG_FORMAT_DEF_VAL*/,
    IFD_ODR_AG_LIN_DECOMP_EN_LSB
  };

  // loop mem instruction, as seen by cmd block
  parameter int IFD_ODR_DEFMEM_DIM_DEF_PTR_DW = 8;
  parameter int IFD_ODR_DEFMEM_LOOP_DEF_PTR_DW = 8;
  parameter int IFD_ODR_DEFMEM_NUMDIM_DW = $clog2(IFD_ODR_DEFMEM_MAX_LOOPS);
  parameter int IFD_ODR_DEFMEM_DIM_DEF_PTR_LSB = 128;
  parameter int IFD_ODR_DEFMEM_LOOP_DEF_PTR_LSB = 136;
  parameter int IFD_ODR_DEFMEM_NUMDIM_LSB = IFD_ODR_AG_SETTINGS_LSB + 0;

  // indexes in memory:
  parameter int IFD_ODR_DEFMEM_DIM_OFF_LSB = 0;
  parameter int IFD_ODR_DEFMEM_DIM_W_LSB = 16;
  parameter int IFD_ODR_DEFMEM_MEM_STRIDE_LSB = 32;
  parameter int IFD_ODR_DEFMEM_INNER_LEN_LSB = 0;
  parameter int IFD_ODR_DEFMEM_INNER_STR_LSB = 16;
  parameter int IFD_ODR_DEFMEM_OUTER_LEN_LSB = 32;
  parameter int IFD_ODR_DEFMEM_OUTER_STR_LSB = 48;

  parameter int IFD_ODR_CMD_DM_BASE_FMT = 0;
  parameter int IFD_ODR_CMD_DM_BASE_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_DM_BASE_DIM_W_A_LSB,
    IFD_ODR_DM_BASE_DIM_W_B_LSB,
    IFD_ODR_DM_BASE_DIM_W_C_LSB,
    IFD_ODR_DM_BASE_DIM_W_D_LSB,
    IFD_ODR_DM_BASE_DIM_OFF_A_LSB,
    IFD_ODR_DM_BASE_DIM_OFF_B_LSB,
    IFD_ODR_DM_BASE_DIM_OFF_C_LSB,
    IFD_ODR_DM_BASE_DIM_OFF_D_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_A_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_B_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_C_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_D_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_A_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_B_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_C_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_D_LSB,
    IFD_ODR_DM_BASE_INNER_STR_A_LSB,
    IFD_ODR_DM_BASE_INNER_STR_B_LSB,
    IFD_ODR_DM_BASE_INNER_STR_C_LSB,
    IFD_ODR_DM_BASE_INNER_STR_D_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_A_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_B_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_C_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_D_LSB,
    IFD_ODR_AG_MSK_START_LSB,
    IFD_ODR_AG_MSK_END_LSB,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_LSB,
    IFD_ODR_AG_MEM_BSIZE_LSB,
    IFD_ODR_DM_BASE_STRIDE_A_LSB,
    IFD_ODR_DM_BASE_STRIDE_B_LSB,
    IFD_ODR_DM_BASE_STRIDE_C_LSB,
    IFD_ODR_DM_BASE_STRIDE_D_LSB,
    IFD_ODR_AG_MEM_OFFSET_LSB,
    IFD_ODR_AG_RING_BUFFER_SIZE_LSB,
    IFD_ODR_AG_PAD_VAL_LSB,
    IFD_ODR_AG_INTRA_PAD_VAL_LSB,
    IFD_ODR_AG_PAD_MODE_EDGE_LSB,
    IFD_ODR_AG_VTRSP_EN_LSB,
    IFD_ODR_AG_VECT_DIM_LSB,
    IFD_ODR_AG_FORMAT_LSB,
    -1  /*IFD_ODR_AG_DECOMP_EN_LSB*/  // no decomp in extended command
  };

  // defmem ext, where dim offset is coming from the cmd and not memory
  parameter int IFD_ODR_CMD_IFD_ODR_DM_EXT_FMT = 3;
  parameter int IFD_ODR_DM_EXT_DIM_OFF_A_LSB = 192;
  parameter int IFD_ODR_DM_EXT_DIM_OFF_B_LSB = 208;
  parameter int IFD_ODR_DM_EXT_DIM_OFF_C_LSB = 224;
  parameter int IFD_ODR_DM_EXT_DIM_OFF_D_LSB = 240;

  parameter int CMD_IFD_ODR_DM_EXT_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_DM_BASE_DIM_W_A_LSB,
    IFD_ODR_DM_BASE_DIM_W_B_LSB,
    IFD_ODR_DM_BASE_DIM_W_C_LSB,
    IFD_ODR_DM_BASE_DIM_W_D_LSB,
    IFD_ODR_DM_EXT_DIM_OFF_A_LSB,
    IFD_ODR_DM_EXT_DIM_OFF_B_LSB,
    IFD_ODR_DM_EXT_DIM_OFF_C_LSB,
    IFD_ODR_DM_EXT_DIM_OFF_D_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_A_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_B_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_C_LSB,
    IFD_ODR_DM_BASE_INNER_LEN_D_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_A_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_B_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_C_LSB,
    IFD_ODR_DM_BASE_OUTER_LEN_D_LSB,
    IFD_ODR_DM_BASE_INNER_STR_A_LSB,
    IFD_ODR_DM_BASE_INNER_STR_B_LSB,
    IFD_ODR_DM_BASE_INNER_STR_C_LSB,
    IFD_ODR_DM_BASE_INNER_STR_D_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_A_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_B_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_C_LSB,
    IFD_ODR_DM_BASE_OUTER_STR_D_LSB,
    IFD_ODR_AG_MSK_START_LSB,
    IFD_ODR_AG_MSK_END_LSB,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_LSB,
    IFD_ODR_AG_MEM_BSIZE_LSB,
    IFD_ODR_DM_BASE_STRIDE_A_LSB,
    IFD_ODR_DM_BASE_STRIDE_B_LSB,
    IFD_ODR_DM_BASE_STRIDE_C_LSB,
    IFD_ODR_DM_BASE_STRIDE_D_LSB,
    IFD_ODR_AG_MEM_OFFSET_LSB,
    IFD_ODR_AG_RING_BUFFER_SIZE_LSB,
    IFD_ODR_AG_PAD_VAL_LSB,
    IFD_ODR_AG_INTRA_PAD_VAL_LSB,
    IFD_ODR_AG_PAD_MODE_EDGE_LSB,
    IFD_ODR_AG_VTRSP_EN_LSB,
    IFD_ODR_AG_VECT_DIM_LSB,
    IFD_ODR_AG_FORMAT_LSB,
    -1  /*IFD_ODR_AG_DECOMP_EN_LSB*/  // no decomp in extended command
  };

  // extended "normal" / fall-back, only set those that differ:
  parameter int IFD_ODR_CMD_FALLBACK_EXT_FMT = 4;
  // CMD Field LSB idx's:
  parameter int IFD_ODR_FB_EXT_DIM_W_D_LSB = 400;
  parameter int IFD_ODR_FB_EXT_DIM_OFF_D_LSB = 384;

  parameter int IFD_ODR_FB_EXT_INNER_LEN_A_LSB = 448;
  parameter int IFD_ODR_FB_EXT_INNER_LEN_B_LSB = 464;
  parameter int IFD_ODR_FB_EXT_INNER_LEN_C_LSB = 480;
  parameter int IFD_ODR_FB_EXT_INNER_LEN_D_LSB = 496;
  parameter int IFD_ODR_FB_EXT_OUTER_LEN_A_LSB = 512;
  parameter int IFD_ODR_FB_EXT_OUTER_LEN_B_LSB = 528;
  parameter int IFD_ODR_FB_EXT_OUTER_LEN_C_LSB = 544;
  parameter int IFD_ODR_FB_EXT_OUTER_LEN_D_LSB = 560;
  parameter int IFD_ODR_FB_EXT_INNER_STR_A_LSB = 576;
  parameter int IFD_ODR_FB_EXT_OUTER_STR_A_LSB = 584;
  parameter int IFD_ODR_FB_EXT_INNER_STR_B_LSB = 592;
  parameter int IFD_ODR_FB_EXT_OUTER_STR_B_LSB = 600;
  parameter int IFD_ODR_FB_EXT_INNER_STR_C_LSB = 608;
  parameter int IFD_ODR_FB_EXT_OUTER_STR_C_LSB = 616;
  parameter int IFD_ODR_FB_EXT_INNER_STR_D_LSB = 624;
  parameter int IFD_ODR_FB_EXT_OUTER_STR_D_LSB = 632;

  // memory access info:
  parameter int IFD_ODR_FB_EXT_MEM_STRIDE_D_LSB = 416;

  parameter int IFD_ODR_CMD_FALLBACK_EXT_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_DIM_W_A_LSB,
    IFD_ODR_AG_DIM_W_B_LSB,
    IFD_ODR_AG_DIM_W_C_LSB,
    IFD_ODR_FB_EXT_DIM_W_D_LSB,
    IFD_ODR_AG_DIM_OFF_A_LSB,
    IFD_ODR_AG_DIM_OFF_B_LSB,
    IFD_ODR_AG_DIM_OFF_C_LSB,
    IFD_ODR_FB_EXT_DIM_OFF_D_LSB,
    IFD_ODR_FB_EXT_INNER_LEN_A_LSB,
    IFD_ODR_FB_EXT_INNER_LEN_B_LSB,
    IFD_ODR_FB_EXT_INNER_LEN_C_LSB,
    IFD_ODR_FB_EXT_INNER_LEN_D_LSB,
    IFD_ODR_FB_EXT_OUTER_LEN_A_LSB,
    IFD_ODR_FB_EXT_OUTER_LEN_B_LSB,
    IFD_ODR_FB_EXT_OUTER_LEN_C_LSB,
    IFD_ODR_FB_EXT_OUTER_LEN_D_LSB,
    IFD_ODR_FB_EXT_INNER_STR_A_LSB,
    IFD_ODR_FB_EXT_INNER_STR_B_LSB,
    IFD_ODR_FB_EXT_INNER_STR_C_LSB,
    IFD_ODR_FB_EXT_INNER_STR_D_LSB,
    IFD_ODR_FB_EXT_OUTER_STR_A_LSB,
    IFD_ODR_FB_EXT_OUTER_STR_B_LSB,
    IFD_ODR_FB_EXT_OUTER_STR_C_LSB,
    IFD_ODR_FB_EXT_OUTER_STR_D_LSB,
    IFD_ODR_AG_MSK_START_LSB,
    IFD_ODR_AG_MSK_END_LSB,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_LSB,
    IFD_ODR_AG_MEM_BSIZE_LSB,
    IFD_ODR_AG_MEM_STRIDE_A_LSB,
    IFD_ODR_AG_MEM_STRIDE_B_LSB,
    IFD_ODR_AG_MEM_STRIDE_C_LSB,
    IFD_ODR_FB_EXT_MEM_STRIDE_D_LSB,
    IFD_ODR_AG_MEM_OFFSET_LSB,
    IFD_ODR_AG_RING_BUFFER_SIZE_LSB,
    IFD_ODR_AG_PAD_VAL_LSB,
    IFD_ODR_AG_INTRA_PAD_VAL_LSB,
    IFD_ODR_AG_PAD_MODE_EDGE_LSB,
    IFD_ODR_AG_VTRSP_EN_LSB,
    IFD_ODR_AG_VECT_DIM_LSB,
    IFD_ODR_AG_FORMAT_LSB,
    -1  /*IFD_ODR_FB_EXT_DECOMP_EN_LSB*/  // no decomp in extended command
  };

  // full AG command:
  parameter int CMD_EXT_FIELD_LSBS[IFD_ODR_AG_CMD_NR_FIELDS] = {
    IFD_ODR_AG_DIM_W_A_LSB,
    IFD_ODR_AG_DIM_W_B_LSB,
    IFD_ODR_AG_DIM_W_C_LSB,
    IFD_ODR_AG_DIM_W_D_LSB,
    IFD_ODR_AG_DIM_OFF_A_LSB,
    IFD_ODR_AG_DIM_OFF_B_LSB,
    IFD_ODR_AG_DIM_OFF_C_LSB,
    IFD_ODR_AG_DIM_OFF_D_LSB,
    IFD_ODR_AG_INNER_LEN_A_LSB,
    IFD_ODR_AG_INNER_LEN_B_LSB,
    IFD_ODR_AG_INNER_LEN_C_LSB,
    IFD_ODR_AG_INNER_LEN_D_LSB,
    IFD_ODR_AG_OUTER_LEN_A_LSB,
    IFD_ODR_AG_OUTER_LEN_B_LSB,
    IFD_ODR_AG_OUTER_LEN_C_LSB,
    IFD_ODR_AG_OUTER_LEN_D_LSB,
    IFD_ODR_AG_INNER_STR_A_LSB,
    IFD_ODR_AG_INNER_STR_B_LSB,
    IFD_ODR_AG_INNER_STR_C_LSB,
    IFD_ODR_AG_INNER_STR_D_LSB,
    IFD_ODR_AG_OUTER_STR_A_LSB,
    IFD_ODR_AG_OUTER_STR_B_LSB,
    IFD_ODR_AG_OUTER_STR_C_LSB,
    IFD_ODR_AG_OUTER_STR_D_LSB,
    IFD_ODR_AG_MSK_START_LSB,
    IFD_ODR_AG_MSK_END_LSB,
    // memory access info:
    IFD_ODR_AG_MEM_BASE_LSB,
    IFD_ODR_AG_MEM_BSIZE_LSB,
    IFD_ODR_AG_MEM_STRIDE_A_LSB,
    IFD_ODR_AG_MEM_STRIDE_B_LSB,
    IFD_ODR_AG_MEM_STRIDE_C_LSB,
    IFD_ODR_AG_MEM_STRIDE_D_LSB,
    IFD_ODR_AG_MEM_OFFSET_LSB,
    IFD_ODR_AG_RING_BUFFER_SIZE_LSB,
    IFD_ODR_AG_PAD_VAL_LSB,
    IFD_ODR_AG_INTRA_PAD_VAL_LSB,
    IFD_ODR_AG_PAD_MODE_EDGE_LSB,
    IFD_ODR_AG_VTRSP_EN_LSB,
    IFD_ODR_AG_VECT_DIM_LSB,
    IFD_ODR_AG_FORMAT_LSB,
    IFD_ODR_AG_DECOMP_EN_LSB
  };

  parameter longint NORM_CMD_DEF_VALS[IFD_ODR_AG_CMD_NR_FIELDS] = IFD_ODR_AG_CMD_DEF_VALS;
  parameter longint LIN_CMD_DEF_VALS[IFD_ODR_AG_CMD_NR_FIELDS] = IFD_ODR_AG_CMD_DEF_VALS;
  parameter longint EXT_CMD_DEF_VALS[IFD_ODR_AG_CMD_NR_FIELDS] = IFD_ODR_AG_CMD_DEF_VALS;

  parameter int CMD_NR_FORMATS = 5;
  parameter int CMD_FMT_DW = $clog2(CMD_NR_FORMATS);

  typedef int int_fields_t[IFD_ODR_AG_CMD_NR_FIELDS];
  typedef int int_fmts_t[CMD_NR_FORMATS];
  typedef longint lint_fields_t[IFD_ODR_AG_CMD_NR_FIELDS];
  typedef int_fields_t int_fields_fmt_t[CMD_NR_FORMATS];
  typedef lint_fields_t lint_fields_fmt_t[CMD_NR_FORMATS];

  function automatic int_fmts_t fill_format_nr_bytes();
    int_fmts_t ret_val;
    ret_val[IFD_ODR_CMD_DM_BASE_FMT] = 3 * 8;  /*defmem base*/
    ret_val[IFD_ODR_CMD_LINEAR_FMT] = 1 * 8;  /*linear*/
    ret_val[IFD_ODR_CMD_FALLBACK_FMT] = 8 * 8;  /*norm*/
    ret_val[IFD_ODR_CMD_IFD_ODR_DM_EXT_FMT] = 4 * 8;  /*defmem ext*/
    ret_val[IFD_ODR_CMD_FALLBACK_EXT_FMT] = 10 * 8;  /*norm ext*/
    return ret_val;
  endfunction

  function automatic lint_fields_fmt_t fill_def_array();
    lint_fields_fmt_t ret_val;
    ret_val[IFD_ODR_CMD_DM_BASE_FMT] = EXT_CMD_DEF_VALS;
    ret_val[IFD_ODR_CMD_LINEAR_FMT] = LIN_CMD_DEF_VALS;
    ret_val[IFD_ODR_CMD_FALLBACK_FMT] = NORM_CMD_DEF_VALS;
    ret_val[IFD_ODR_CMD_IFD_ODR_DM_EXT_FMT] = EXT_CMD_DEF_VALS;
    ret_val[IFD_ODR_CMD_FALLBACK_EXT_FMT] = NORM_CMD_DEF_VALS;
    return ret_val;
  endfunction

  function automatic int_fields_fmt_t fill_idx_array();
    int_fields_fmt_t ret_val;
    ret_val[IFD_ODR_CMD_DM_BASE_FMT] = IFD_ODR_CMD_DM_BASE_FIELD_LSBS;
    ret_val[IFD_ODR_CMD_LINEAR_FMT] = IFD_ODR_CMD_LIN_FIELD_LSBS;
    ret_val[IFD_ODR_CMD_FALLBACK_FMT] = IFD_ODR_CMD_FALLBACK_FIELD_LSBS;
    ret_val[IFD_ODR_CMD_IFD_ODR_DM_EXT_FMT] = CMD_IFD_ODR_DM_EXT_FIELD_LSBS;
    ret_val[IFD_ODR_CMD_FALLBACK_EXT_FMT] = IFD_ODR_CMD_FALLBACK_EXT_FIELD_LSBS;
    return ret_val;
  endfunction

  parameter int_fmts_t IFD_ODR_CMDB_FORMAT_NR_BYTES = fill_format_nr_bytes();
  parameter lint_fields_fmt_t IFD_ODR_CMD_FIELD_DEF_VALS = fill_def_array();
  parameter int_fields_fmt_t IFD_ODR_CMD_FORMAT_IDX = fill_idx_array();
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////

  parameter int IFD_ODR_BP_CMD_FIFO_DEPTH = 4;

  parameter int IFD_ODR_PAD_MODE_PAD = 0;
  parameter int IFD_ODR_PAD_MODE_EDGE = 1;

  parameter int IFD_ODR_INT_COORD_DW = 17;
  parameter int IFD_ODR_INT_ADDR_DW = IFD_ODR_DP_AW;
  parameter int IFD_ODR_LAT_COORD__ADDR = 2;
  parameter int IFD_ODR_LAT_COORD__2_OUT = 2 + IFD_ODR_AG_RING_BUFFER_FLOPS;
  parameter int IFD_ODR_TOT_LATENCY = IFD_ODR_LAT_COORD__ADDR + IFD_ODR_LAT_COORD__2_OUT;

///////////////////////////////////////////////////////////////////////////////
//                               INT16 CASTING                               //
///////////////////////////////////////////////////////////////////////////////

  /*    Parameters and Macros     */

  // Number of state for IFD int16 casting FSM
  parameter int unsigned  IFD_ODR_NUM_STATE_IFD   = 2;
  // State register width for IFD int16 casting FSM
  parameter int unsigned  IFD_ODR_STATE_REG_W_IFD = $clog2(IFD_ODR_NUM_STATE_IFD);
  // Number of state for ODR int8 casting FSM
  parameter int unsigned  IFD_ODR_NUM_STATE_ODR   = 2;
  // State register width for ODR int8 casting FSM
  parameter int unsigned  IFD_ODR_STATE_REG_W_ODR = $clog2(IFD_ODR_NUM_STATE_ODR);
  // Signed int8 maximum value
  parameter int signed    IFD_ODR_INT8_MAX_VAL    = 2**(IFD_ODR_EL8_DW - 1) - 1;
  // Signed int8 minimum value
  parameter int signed    IFD_ODR_INT8_MIN_VAL    = -(2**(IFD_ODR_EL8_DW - 1));

  /*    Type Definitions      */

  // IFD cast state names enumeration
  typedef enum logic [IFD_ODR_STATE_REG_W_IFD : 0] {
      ST_PASSTH_IFD = 'd0,
      ST_CAST_IFD   = 'd1
  } state_cast_ifd_e;

  // ODR cast state names enumeration
  typedef enum logic [IFD_ODR_STATE_REG_W_ODR : 0] {
      ST_PASSTH_ODR = 'd0,
      ST_CAST_ODR   = 'd1
  } state_cast_odr_e;

  // Int8 type definition
  typedef logic signed  [IFD_ODR_EL8_DW - 1 : 0]          int8_t;
  // Int16 type definition
  typedef logic signed  [IFD_ODR_EL_DW - 1 : 0]           int16_t;
  // PWORD64 length type definition
  typedef logic         [IFD_ODR_PWORD64_LEN - 1 : 0]     pw64_len_t;
  // PWORD32 length type definition
  typedef logic         [IFD_ODR_PWORD32_LEN - 1 : 0]     pw32_len_t;
  // PWORD64i8 type definition
  typedef int8_t        [IFD_ODR_PWORD64_LEN - 1 : 0]     pword64i8_t;
  // Halfd PWORD64i8 type definition
  typedef int8_t        [IFD_ODR_PWORD64_LEN / 2 - 1 : 0] half_pword64i8_t;
  // PWORD32i16 type definition
  typedef int16_t       [IFD_ODR_PWORD32_LEN - 1 : 0]     pword32i16_t;

  /*      Functions       */
  // Int8 to int16 conversion sign extention function
  function automatic pword32i16_t cast_int16(half_pword64i8_t i_half_pword64i8);
    for(int idx = 0; idx < IFD_ODR_PWORD32_LEN; idx++) begin
        cast_int16[idx] = i_half_pword64i8[idx];
    end
  endfunction

  // 32-bit mask to 64-bit mask conversion for byte by byte pword32i16 masking
  function automatic pw64_len_t msk_conv(pw32_len_t pw32_msk);
    for(int idx = 0; idx < IFD_ODR_PWORD32_LEN; idx++) begin
      msk_conv[2*idx +: 2] = {2{pw32_msk[idx]}};
    end
  endfunction

  // Int16 to int8 casting with saturation
  function automatic half_pword64i8_t cast_int8(pword32i16_t i_pword32i16);
    for(int idx = 0; idx < IFD_ODR_PWORD32_LEN; idx++) begin
      if(i_pword32i16[idx] > IFD_ODR_INT8_MAX_VAL)
        cast_int8[idx] = IFD_ODR_INT8_MAX_VAL;
      else if(i_pword32i16[idx] < IFD_ODR_INT8_MIN_VAL)
        cast_int8[idx] = IFD_ODR_INT8_MIN_VAL;
      else
        cast_int8[idx] = i_pword32i16[idx];
    end
  endfunction

endpackage

`endif  // _IFD_ODR_PKG_SV_
