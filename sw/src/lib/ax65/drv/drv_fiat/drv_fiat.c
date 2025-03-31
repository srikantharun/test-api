// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

//--------------------------------------------------
// INCLUDES
//--------------------------------------------------

#include "drv_fiat.h"

#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>

#include "util.h"
#include "logging.h"
#include "string.h"
#include "uvm_ipc/uvm_sw_ipc.h"

//--------------------------------------------------
// DATA
//--------------------------------------------------

extern const target_core_list_t test_target_core_list;

extern const data_blob_list_t test_data_blob_list;

//--------------------------------------------------
// LOCAL FUNCTIONS
//--------------------------------------------------

//--------------------------------------------------
// GLOBAL FUNCTION DEFINITIONS
//--------------------------------------------------

#ifndef DRV_FIAT_MEMCMP
#define DRV_FIAT_MEMCMP UVM
#endif

__attribute__((weak)) void verify_data_blobs(const data_blob_t data_blobs[], uint32_t count) {
  for (uint32_t data_blob_idx = 0; data_blob_idx < count; data_blob_idx++) {
    const data_blob_t* data_blob = &data_blobs[data_blob_idx];
    if (data_blob->type == DATA_BLOB_TYPE_VERIFY) {
      const uint64_t* address = (uint64_t*) data_blob->address;
      const uint64_t* preload_location = (uint64_t*) data_blob->preload_location;

      LOG_INFO("Comparing at %p vs %p...", address, preload_location);

#if DRV_FIAT_MEMCMP == UVM
      CHECK_TRUE(uvm_sw_ipc_memcmp(address, preload_location, data_blob->size) == 0, "uvm_sw_ipc_memcmp failed");
#elif DRV_FIAT_MEMCMP == CPU
      CHECK_TRUE(memcmp(address, preload_location, data_blob->size) == 0, "uvm_sw_ipc_memcmp failed");
#elif DRV_FIAT_MEMCMP == VERBOSE
      for (uint32_t data_idx = 0; data_idx < data_blob->size / sizeof(uint64_t); data_idx++) {
        CHECK_EQUAL_HEX(preload_location[data_idx], address[data_idx]);
      }
#endif
    }
  }
}

__attribute__((weak)) void execute_atex(void) {
  for (uint32_t core_idx = 0; core_idx < test_target_core_list.count; core_idx++) {
    start_core(test_target_core_list.target_cores[core_idx]);
  }
  for (uint32_t core_idx = 0; core_idx < test_target_core_list.count; core_idx++) {
    CHECK_TRUE(wait_core(test_target_core_list.target_cores[core_idx]) == TEST_SUCCESS);
  }
}

__attribute__((weak)) void setup(void) {}

__attribute__((weak)) void teardown(void) {}

__attribute__((weak)) void test_atex(void) {
  LOG_INFO("Setup...");
  setup();
  LOG_INFO("Setup complete.");

  LOG_INFO("Executing ATEX...");
  execute_atex();
  LOG_INFO("Execution completed.");

  LOG_INFO("Verifying data blobs...");
  verify_data_blobs(test_data_blob_list.data_blobs, test_data_blob_list.count);
  LOG_INFO("Verification completed.");

  LOG_INFO("Teardown...");
  teardown();
  LOG_INFO("Teardown complete.");
}
