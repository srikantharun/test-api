// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Europa specific implemeation constants and type definitions
///
package aic_did_pkg;

  ////////////////////////////////
  // AXI Endpoint configuration //
  ////////////////////////////////
  parameter int unsigned NUM_AXI_ENDPOINTS = 3;

  typedef enum logic[cc_math_pkg::index_width(NUM_AXI_ENDPOINTS)-1:0] {
    EndPointDwpu = 'd0,
    EndPointIau  = 'd1,
    EndPointDpu  = 'd2
  } axi_select_e;

  // Regions:
  import aic_addr_map_pkg::*;
  parameter int DID_NR_ENDPOINT_SETS = 3; // DWPU, IAU and DPU
  parameter int DID_NR_REGIONS = 3 * DID_NR_ENDPOINT_SETS;
  parameter int DID_REGION_SLAVE_ID[DID_NR_REGIONS] = {
    32'd0, 32'd0, 32'd0, // DWPU
    32'd1, 32'd1, 32'd1, // IAU
    32'd2, 32'd2, 32'd2  // DPU
  };
  parameter longint DID_REGION_ST_ADDR[DID_NR_REGIONS] = {
    AIC_LOC_D_DWPU_REGION_ST_ADDR[0], AIC_LOC_D_DWPU_REGION_ST_ADDR[1], AIC_LOC_D_DWPU_REGION_ST_ADDR[2],
    AIC_LOC_D_IAU_REGION_ST_ADDR[0],  AIC_LOC_D_IAU_REGION_ST_ADDR[1],  AIC_LOC_D_IAU_REGION_ST_ADDR[2],
    AIC_LOC_D_DPU_REGION_ST_ADDR[0],  AIC_LOC_D_DPU_REGION_ST_ADDR[1],  AIC_LOC_D_DPU_REGION_ST_ADDR[2]
  };
  parameter longint DID_REGION_END_ADDR[DID_NR_REGIONS] = {
    AIC_LOC_D_DWPU_REGION_END_ADDR[0], AIC_LOC_D_DWPU_REGION_END_ADDR[1], AIC_LOC_D_DWPU_REGION_END_ADDR[2],
    AIC_LOC_D_IAU_REGION_END_ADDR[0],  AIC_LOC_D_IAU_REGION_END_ADDR[1],  AIC_LOC_D_IAU_REGION_END_ADDR[2],
    AIC_LOC_D_DPU_REGION_END_ADDR[0],  AIC_LOC_D_DPU_REGION_END_ADDR[1],  AIC_LOC_D_DPU_REGION_END_ADDR[2]
  };

  /////////////////////////////////////
  // AXI type and struct definitions //
  /////////////////////////////////////

  typedef logic [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH      -1:0] axi_id_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] axi_addr_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH      -1:0] axi_data_t;
  typedef logic [aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH     -1:0] axi_strb_t;

  ///////////////////////////////////////////////////
  // Block specific FIFO and Spill register config //
  ///////////////////////////////////////////////////

  parameter bit          DwpuIauSpillRegBypass = 1'b1;
  parameter int unsigned IauDpuFifoDepth       = 4;


endpackage
