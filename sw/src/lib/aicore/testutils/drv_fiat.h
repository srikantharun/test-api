#pragma once

//--------------------------------------------------
// INCLUDES
//--------------------------------------------------

#include <stddef.h>
#include <stdint.h>

#include "task_handler.h"

//--------------------------------------------------
// DEFINITIONS
//--------------------------------------------------

//--------------------------------------------------
// TYPES
//--------------------------------------------------

typedef enum {
  DATA_BLOB_TYPE_PRELOAD,
  DATA_BLOB_TYPE_VERIFY,
} data_blob_type_t;

typedef struct {
  data_blob_type_t type;
  uint32_t size;
  uintptr_t address;
  uintptr_t preload_location;
} data_blob_t;

typedef struct {
  uint32_t count;
  const data_blob_t *data_blobs;
} data_blob_list_t;

typedef struct {
  uint32_t count;
  const task_handler_task_t * const *tasks;
} task_list_t;

typedef struct {
  uint32_t count;
  const mempool_t *mempools;
} mempool_list_t;

//--------------------------------------------------
// DATA
//--------------------------------------------------

//--------------------------------------------------
// FUNCTION PROTOTYPES
//--------------------------------------------------

void setup(void);
void teardown(void);

void verify_data_blobs(const data_blob_t data_blobs[], uint32_t count);

void initialize_drivers(void);
void deinitialize_drivers(void);

int run_tasks(const task_handler_task_t * const tasks[], uint32_t count);
int run_packed_tasks(uintptr_t packed_tasks_ptr, size_t packed_tasks_size);
int run_stream(const task_handler_packed_tasks_stream_t* stream, uintptr_t buffer, size_t buffer_size);

void test_atex(void);
