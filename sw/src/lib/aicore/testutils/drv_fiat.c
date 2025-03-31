// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

//--------------------------------------------------
// INCLUDES
//--------------------------------------------------

#include "drv_fiat.h"

#include "util.h"
#include "testutils.h"
#include "logging.h"
#include "string.h"
#include "uvm_ipc/uvm_sw_ipc.h"

#include "task_handler.h"
#include "datapath.h"

//--------------------------------------------------
// DATA
//--------------------------------------------------

extern const task_list_t test_task_list;
extern const mempool_list_t test_mempool_list;
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

// comparing non-numeric macro values is hard; see https://stackoverflow.com/a/45450646
#define _CONCAT_IMPL(x, y) x ## y
#define _CONCAT(x, y) _CONCAT_IMPL(x, y)
#define _DRV_FIAT_MEMCMP _CONCAT(_DRV_FIAT_MEMCMP_, DRV_FIAT_MEMCMP)
// numeric values for the individual macros
#define _DRV_FIAT_MEMCMP_NONE 1
#define _DRV_FIAT_MEMCMP_UVM 2
#define _DRV_FIAT_MEMCMP_CPU 3
#define _DRV_FIAT_MEMCMP_VERBOSE 4

__attribute__((weak)) void verify_data_blobs(const data_blob_t data_blobs[], uint32_t count) {
  for (uint32_t data_blob_idx = 0; data_blob_idx < count; data_blob_idx++) {
    const data_blob_t* data_blob = &data_blobs[data_blob_idx];
    if (data_blob->type == DATA_BLOB_TYPE_VERIFY) {
      const uint64_t* address = (uint64_t*) data_blob->address;
      const uint64_t* preload_location = (uint64_t*) data_blob->preload_location;

      LOG_INFO("Comparing at %p vs %p...", address, preload_location);

#if _DRV_FIAT_MEMCMP == _DRV_FIAT_MEMCMP_UVM
      CHECK_TRUE(uvm_sw_ipc_memcmp(address, preload_location, data_blob->size) == 0, "uvm_sw_ipc_memcmp failed");
#elif _DRV_FIAT_MEMCMP == _DRV_FIAT_MEMCMP_CPU
      CHECK_TRUE(memcmp(address, preload_location, data_blob->size) == 0, "memcmp failed");
#elif _DRV_FIAT_MEMCMP == _DRV_FIAT_MEMCMP_VERBOSE
      for (uint32_t data_idx = 0; data_idx < data_blob->size / sizeof(uint64_t); data_idx++) {
        CHECK_EQUAL_HEX(preload_location[data_idx], address[data_idx]);
      }
#endif
    }
  }
}

__attribute__((weak)) void setup(void) {}

__attribute__((weak)) void teardown(void) {}

__attribute__((weak)) void initialize_drivers(void) {
  LOG_INFO("Initializing task handler...");
  task_handler_init();

  LOG_INFO("Initializing memory pools...");
  mempool_init(test_mempool_list.mempools, test_mempool_list.count);

  LOG_INFO("Initializing datapath...");
  datapath_init();

  LOG_INFO("Enabling execution...");
  datapath_enable_execution();
}

__attribute__((weak)) void deinitialize_drivers(void) {
  LOG_INFO("Disabling execution...");
  datapath_disable_execution();
}

__attribute__((weak)) int run_tasks(const task_handler_task_t * const tasks[], uint32_t count) {
  LOG_INFO("Dispatching tasks to task handler...");
  return task_handler_run_tasks(tasks, count);
}

__attribute__((weak)) int run_packed_tasks(uintptr_t packed_tasks_ptr, size_t packed_tasks_size) {
  LOG_INFO("Dispatching packed tasks to task handler...");
  return task_handler_run_packed_tasks(packed_tasks_ptr, packed_tasks_size);
}

__attribute__((weak)) int run_stream(const task_handler_packed_tasks_stream_t* stream, uintptr_t buffer, size_t buffer_size) {
  LOG_INFO("Dispatching stream to task handler...");
  return task_handler_stream_packed_tasks(stream, buffer, buffer_size);
}

__attribute__((weak)) void test_atex(void) {
  LOG_INFO("Setup...");
  setup();
  LOG_INFO("Setup complete.");

  LOG_INFO("Initializing drivers...");
  initialize_drivers();
  LOG_INFO("Successfully initialized drivers.");

  LOG_INFO("Running tasks...");
  if (run_tasks(test_task_list.tasks, test_task_list.count)) return;
  LOG_INFO("Tasks completed.");

  LOG_INFO("Deinitializing drivers...");
  deinitialize_drivers();
  LOG_INFO("Successfully deinitialized drivers.");

  LOG_INFO("Verifying data blobs...");
  verify_data_blobs(test_data_blob_list.data_blobs, test_data_blob_list.count);
  LOG_INFO("Verification completed.");

  LOG_INFO("Teardown...");
  teardown();
  LOG_INFO("Teardown complete.");
}
