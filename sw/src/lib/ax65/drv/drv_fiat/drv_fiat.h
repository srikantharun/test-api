#pragma once

//--------------------------------------------------
// INCLUDES
//--------------------------------------------------

#include <stddef.h>
#include <stdint.h>

#include <platform.h>

//--------------------------------------------------
// DEFINITIONS
//--------------------------------------------------

//--------------------------------------------------
// TYPES
//--------------------------------------------------

typedef struct {
  uint32_t count;
  const HART_ID *target_cores;
} target_core_list_t;

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

//--------------------------------------------------
// DATA
//--------------------------------------------------

//--------------------------------------------------
// FUNCTION PROTOTYPES
//--------------------------------------------------

void setup(void);
void teardown(void);

void verify_data_blobs(const data_blob_t data_blobs[], uint32_t count);
void execute_atex(void);

void test_atex(void);
