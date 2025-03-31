// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

#ifndef __TOKEN_MANAGER_H__
#define __TOKEN_MANAGER_H__

//==================================================
// INCLUDES
//==================================================

#include <stdbool.h>
#include <stdint.h>

#include "module.h"

//==================================================
// MACROS
//==================================================

//==================================================
// DEFINITIONS
//==================================================

// token_mode
#define TOKEN_MANAGER_TOKEN_MODE_PRODUCE                                         (0)
#define TOKEN_MANAGER_TOKEN_MODE_CONSUME                                         (1)

//==================================================
// TYPES
//==================================================

typedef enum {
  TOKEN_MANAGER_STATUS_OK = 0,
  TOKEN_MANAGER_STATUS_ERROR,
} token_manager_status_t;

//==================================================
// GLOBAL FUNCTION PROTOTYPES
//==================================================

token_manager_status_t token_manager_init(void);

token_manager_status_t token_manager_reset(void);

token_manager_status_t token_manager_produce_tokens(module_id_t module_id, uint8_t tokens);
token_manager_status_t token_manager_consume_tokens(module_id_t module_id, uint8_t tokens);

token_manager_status_t token_manager_produce_multiple_tokens(const uint8_t tokens[MODULE_COUNT]);
token_manager_status_t token_manager_consume_multiple_tokens(const uint8_t tokens[MODULE_COUNT]);

#endif  // __TOKEN_MANAGER_H__
