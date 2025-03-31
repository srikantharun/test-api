// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

#ifndef __DATAPATH_H__
#define __DATAPATH_H__

//==================================================
// INCLUDES
//==================================================

#include <stdbool.h>
#include <stdint.h>

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
  DATAPATH_STATUS_OK = 0,
  DATAPATH_STATUS_ERROR,
} datapath_status_t;

//==================================================
// GLOBAL FUNCTION PROTOTYPES
//==================================================

datapath_status_t datapath_init(void);

datapath_status_t datapath_enable_execution(void);
datapath_status_t datapath_disable_execution(void);
datapath_status_t datapath_poll_idle(void);

datapath_status_t datapath_clear_instructions(void);

#endif  // __DATAPATH_H__
