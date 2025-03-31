// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IFD ODR Address Generator Package
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

package dmc_addr_gen_ref_model_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dmc_addr_gen_agent_pkg::*;

  typedef struct {
    int unsigned length;
    bit used;
  } stream_info_t;

  //Defines
  parameter int unsigned AIC_DMC_PWORD_SIZE = aic_common_pkg::AIC_PWORD_SIZE; // number of elements in PWORD
  parameter int unsigned RING_BUFFER_SIZE_GRANULARITY = 64 * AIC_DMC_PWORD_SIZE;
  parameter int unsigned RING_BUFFER_MAX_SIZE = 2**22; // 4MiB (22b)
  parameter int unsigned ODR_ADDR_WIDTH = 36;
  parameter int unsigned ODR_STREAM_LEN = 512;

  typedef bit[ODR_ADDR_WIDTH-1:0] odr_stream_addr_t;
  typedef bit[ODR_STREAM_LEN-1:0] odr_stream_data_t;
  typedef bit[AIC_DMC_PWORD_SIZE/2-1:0]   odr_stream_mask_t;
  typedef struct packed {
    odr_stream_addr_t addr;
    odr_stream_data_t data;
  } odr_stream_mem_t;
  typedef int int8_data_arr_t[ODR_STREAM_LEN/8];

  parameter odr_stream_data_t ICDF_MEMORY_DEFAULT_VALUE = 512'haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;

  `include "dmc_addr_gen_ref_model.svh"
endpackage
