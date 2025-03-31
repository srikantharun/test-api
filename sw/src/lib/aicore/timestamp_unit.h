// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

#ifndef __TIMESTAMP_UNIT_H__
#define __TIMESTAMP_UNIT_H__

//==================================================
// INCLUDES
//==================================================

//==================================================
// MACROS
//==================================================

//==================================================
// DEFINITIONS
//==================================================

//==================================================
// TYPES
//==================================================

typedef enum {
  TIMESTAMP_UNIT_STATUS_OK = 0,
  TIMESTAMP_UNIT_STATUS_ERROR,
} timestamp_unit_status_t;

//==================================================
// GLOBAL FUNCTION PROTOTYPES
//==================================================

timestamp_unit_status_t timestamp_unit_init(void);


timestamp_unit_status_t timestamp_unit_start(void);
timestamp_unit_status_t timestamp_unit_reset(void);
timestamp_unit_status_t timestamp_unit_stop(void);

timestamp_unit_status_t timestamp_unit_get_counters(void):

timestamp_unit_status_t trace_print_counters(void):

#endif  // __TIMESTAMP_UNIT_H__
