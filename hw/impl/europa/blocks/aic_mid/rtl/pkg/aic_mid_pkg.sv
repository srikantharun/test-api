// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>


/// Package for MVM DPU
///
package aic_mid_pkg;
  import c2c_monitor_wrapper_pkg::*;
  import dwm_throttle_ctrl_unit_pkg::*;
  import dwm_pkg::*;


  parameter int unsigned NUM_AXI_ENDPOINTS = 4;
  parameter int unsigned NUM_IRQS = 6; // MVM, IAU, DPU, CSR + 2xTU
  parameter int unsigned MID_NR_ENDPOINT_SETS = 4; // MVM EXE, MVM PRG, IAU and DPU

  typedef enum logic[cc_math_pkg::index_width(NUM_IRQS)-1:0] {
    TU_critical_irq = 'd5,
    TU_warning_irq  = 'd4,
    MID_irq = 'd3,
    Dpu_irq = 'd2,
    Iau_irq = 'd1,
    Mvm_irq = 'd0
  } irq_select_e;

  typedef enum logic[cc_math_pkg::index_width(NUM_AXI_ENDPOINTS)-1:0] {
    EndPointCSR = 'd3,
    EndPointDpu = 'd2,
    EndPointIau = 'd1,
    EndPointMvm = 'd0
  } axi_select_e;

  typedef enum logic[cc_math_pkg::index_width(MID_NR_ENDPOINT_SETS)-1:0] {
    EndPointTSDpu    = 'd3,
    EndPointTSIau    = 'd2,
    EndPointTSMvmPrg = 'd1,
    EndPointTSMvmExe = 'd0
  } ts_select_e;

  // Regions:
  import aic_addr_map_pkg::*;
  parameter int MID_NR_REGIONS = 3 * MID_NR_ENDPOINT_SETS + 1;
  parameter int MID_REGION_SLAVE_ID[MID_NR_REGIONS] = {
    32'd0, 32'd0, 32'd0, // MVM EXE
    32'd0, 32'd0, 32'd0, // MVM PRG
    32'd1, 32'd1, 32'd1, // IAU
    32'd2, 32'd2, 32'd2, // DPU
    32'd3                // CSR
  };
  parameter longint MID_REGION_ST_ADDR[MID_NR_REGIONS] = {
    AIC_LOC_M_MVM_REGION_ST_ADDR[0], AIC_LOC_M_MVM_REGION_ST_ADDR[1], AIC_LOC_M_MVM_REGION_ST_ADDR[2],
    AIC_LOC_M_MVM_REGION_ST_ADDR[3], AIC_LOC_M_MVM_REGION_ST_ADDR[4], AIC_LOC_M_MVM_REGION_ST_ADDR[5],
    AIC_LOC_M_IAU_REGION_ST_ADDR[0], AIC_LOC_M_IAU_REGION_ST_ADDR[1], AIC_LOC_M_IAU_REGION_ST_ADDR[2],
    AIC_LOC_M_DPU_REGION_ST_ADDR[0], AIC_LOC_M_DPU_REGION_ST_ADDR[1], AIC_LOC_M_DPU_REGION_ST_ADDR[2],
    AIC_LOC_CFG_CSR_MID_PART_ST_ADDR
  };
  parameter longint MID_REGION_END_ADDR[MID_NR_REGIONS] = {
    AIC_LOC_M_MVM_REGION_END_ADDR[0], AIC_LOC_M_MVM_REGION_END_ADDR[1], AIC_LOC_M_MVM_REGION_END_ADDR[2],
    AIC_LOC_M_MVM_REGION_END_ADDR[3], AIC_LOC_M_MVM_REGION_END_ADDR[4], AIC_LOC_M_MVM_REGION_END_ADDR[5],
    AIC_LOC_M_IAU_REGION_END_ADDR[0], AIC_LOC_M_IAU_REGION_END_ADDR[1], AIC_LOC_M_IAU_REGION_END_ADDR[2],
    AIC_LOC_M_DPU_REGION_END_ADDR[0], AIC_LOC_M_DPU_REGION_END_ADDR[1], AIC_LOC_M_DPU_REGION_END_ADDR[2],
    AIC_LOC_CFG_CSR_MID_PART_END_ADDR
  };

  /////////////////////////////////////
  // AXI type and struct definitions //
  /////////////////////////////////////

  typedef logic [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH      -1:0] axi_id_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] axi_addr_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH      -1:0] axi_ext_addr_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH      -1:0] axi_data_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH     -1:0] axi_strb_t;

  ///////////////////////////////////////////////////
  // Block specific FIFO and Spill register config //
  ///////////////////////////////////////////////////

  parameter bit          MvmIauSpillRegBypass = 1'b0;
  parameter int unsigned IauDpuFifoDepth       = 4;

  ////////////////////////////
  // Throttle Unit packages //
  ////////////////////////////
  typedef logic [5:0] nop_inj_rate_t;

  typedef struct packed {
    nop_inj_rate_t         static_settings;
    nop_inj_rate_t   [2:0] throttle_value;
    throttle_mode_e  [2:0] throttle_mode;
    logic            [2:0] throttle_en;
    logic            [2:0] sw_overwrite;
    dctu_incr_decr_t [2:0] throttle_incr_time;
    dctu_incr_decr_t [2:0] throttle_decr_time;
    dctu_prescale_t  [2:0] throttle_prescale;
  } inj_nop_rate_cfg_t;

  typedef logic [7:0] util_data_t;

  typedef struct packed {
    util_data_t      [2:0] throttle_value;
    throttle_mode_e  [2:0] throttle_mode;
    logic            [2:0] throttle_en;
    logic            [2:0] sw_overwrite;
    dctu_incr_decr_t [2:0] throttle_incr_time;
    dctu_incr_decr_t [2:0] throttle_decr_time;
    dctu_prescale_t  [2:0] throttle_prescale;
  } util_cfg_t;

  // Obs
  typedef struct packed {
    util_data_t sampled_avg_util;
    util_data_t util_limit;
    logic       util_limit_en;
  } tu_obs_struct_t;

  typedef union packed {
    tu_obs_struct_t as_struct;
    logic [$bits(tu_obs_struct_t)-1:0] as_bus;
  } tu_obs_union_t;

  parameter bit ULTRA_FAST_IDX = 0;
  parameter bit FAST_IDX = 1;
  parameter bit IMC_IDX = 0;
  parameter bit CORE_IDX = 1;

  parameter int unsigned NOP_INJ_ULTRA_FAST_IDX = 2;
  parameter int unsigned NOP_INJ_FAST_IDX = 1;
  parameter int unsigned NOP_INJ_AIC_IDX = 0;

  parameter int unsigned UTIL_ULTRA_FAST_IDX = 2;
  parameter int unsigned UTIL_FAST_IDX = 1;
  parameter int unsigned UTIL_AIC_IDX = 0;

  parameter int unsigned THROTTLE_DISENGAGE_AIC_IDX = 0;
  parameter int unsigned THROTTLE_DISENGAGE_THERMAL_IDX = 1;
  parameter int unsigned THROTTLE_DISENGAGE_ULTRA_FAST_IDX = 2;
  parameter int unsigned THROTTLE_DISENGAGE_FAST_IDX = 3;

endpackage
