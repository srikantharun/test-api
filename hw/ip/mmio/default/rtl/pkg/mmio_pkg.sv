// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MMIO package
// Owner: Spyridoula Koumousi <koumousi.spyridoula@axelera.ai>

`ifndef MMIO_PACKAGE_SV
`define MMIO_PACKAGE_SV

package mmio_pkg;
  // DMC MMIO interface values
  parameter int unsigned MMIO_DMC_DATA_WIDTH = 512;
  parameter int unsigned MMIO_DMC_ADDR_WIDTH = 22;
  parameter int unsigned MMIO_DMC_WBE_WIDTH = (MMIO_DMC_DATA_WIDTH + 7) / 8;
  // RVV MMIO interface values
  parameter int unsigned MMIO_RVV_DATA_WIDTH = 128;
  parameter int unsigned MMIO_RVV_ADDR_WIDTH = 22;
  parameter int unsigned MMIO_RVV_WBE_WIDTH = (MMIO_RVV_DATA_WIDTH + 7) / 8;

  /////////////////////////////////////////////
  ////// MMIO for DMC

    //////////////////////////
    // request payloads
  typedef struct packed {
    logic [MMIO_DMC_ADDR_WIDTH-1:0] addr;
    logic                           we;
    logic [MMIO_DMC_WBE_WIDTH-1:0]  wbe;
    logic [MMIO_DMC_DATA_WIDTH-1:0] data;
  } mmio_dmc_full_req_payload_t;

  typedef struct packed {
    logic [MMIO_DMC_ADDR_WIDTH-1:0] addr;
    logic [MMIO_DMC_WBE_WIDTH-1:0]  wbe;
    logic [MMIO_DMC_DATA_WIDTH-1:0] data;
  } mmio_dmc_wo_req_payload_t;

  typedef struct packed {
    logic [MMIO_DMC_ADDR_WIDTH-1:0] addr;
  } mmio_dmc_ro_req_payload_t;

    //////////////////////////
    // request
  typedef struct packed {
    mmio_dmc_full_req_payload_t payload;
    logic                       valid;
    logic                       rsp_ready;
  } mmio_dmc_full_req_t;

  typedef struct packed {
    mmio_dmc_wo_req_payload_t payload;
    logic                     valid;
    logic                     rsp_ready;
  } mmio_dmc_wo_req_t;

  typedef struct packed {
    mmio_dmc_ro_req_payload_t payload;
    logic                     valid;
    logic                     rsp_ready;
  } mmio_dmc_ro_req_t;


    //////////////////////////
    // response payloads
  typedef struct packed {
    logic [MMIO_DMC_DATA_WIDTH-1:0] data;
    logic                           error;
  } mmio_dmc_full_rsp_payload_t;
  typedef mmio_dmc_full_rsp_payload_t mmio_dmc_ro_rsp_payload_t;
  typedef struct packed {
    logic [MMIO_DMC_DATA_WIDTH-1:0] data;
  } mmio_dmc_slim_rsp_payload_t;

  typedef struct packed {
    logic                       error;
  } mmio_dmc_wo_rsp_payload_t;

    //////////////////////////
    // response
  typedef struct packed {
    mmio_dmc_full_rsp_payload_t payload;
    logic                       ack;
    logic                       ready;
  } mmio_dmc_full_rsp_t;
  typedef mmio_dmc_full_rsp_t mmio_dmc_ro_rsp_t;
  typedef struct packed {
    mmio_dmc_slim_rsp_payload_t payload;
    logic                       ack;
  } mmio_dmc_slim_rsp_t;

  typedef struct packed {
    mmio_dmc_wo_rsp_payload_t payload;
    logic                     ack;
    logic                     ready;
  } mmio_dmc_wo_rsp_t;
  ////////////////////////////////////////////////////

  /////////////////////////////////////////////
  ////// MMIO for RVV

    //////////////////////////
    // request payloads
  typedef struct packed {
    logic [MMIO_RVV_ADDR_WIDTH-1:0] addr;
    logic                           we;
    logic [MMIO_RVV_WBE_WIDTH-1:0]  wbe;
    logic [MMIO_RVV_DATA_WIDTH-1:0] data;
  } mmio_rvv_req_payload_t;

    //////////////////////////
    // request
  typedef struct packed {
    mmio_rvv_req_payload_t payload;
    logic                  valid;
    logic                  rsp_ready;
  } mmio_rvv_req_t;

    //////////////////////////
    // response payloads
  typedef struct packed {
    logic [MMIO_RVV_DATA_WIDTH-1:0] data;
    logic                           error;
  } mmio_rvv_rsp_payload_t;
  typedef struct packed {
    logic [MMIO_RVV_DATA_WIDTH-1:0] data;
  } mmio_rvv_slim_rsp_payload_t;

    //////////////////////////
    // response
  typedef struct packed {
    mmio_rvv_rsp_payload_t payload;
    logic                  ack;
    logic                  ready;
  } mmio_rvv_rsp_t;
  typedef struct packed {
    mmio_rvv_slim_rsp_payload_t payload;
    logic                       ack;
  } mmio_rvv_slim_rsp_t;
  ////////////////////////////////////////////////////
endpackage
`endif  //MMIO_PACKAGE_SV
