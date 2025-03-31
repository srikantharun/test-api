// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

#ifndef __DWPU_H__
#define __DWPU_H__

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

// Module IDs
#define DWPU_ID_D_DWPU                             (MODULE_ID_D_DWPU)

// Command Formats
#define DWPU_COMMAND_FORMAT_ID_LOOP_M1_N0                         (0)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M1_N1                         (1)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M1_N2                         (2)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M2_N0                         (3)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M2_N1                         (4)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M2_N2                         (5)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M3_N0                         (6)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M3_N1                         (7)
#define DWPU_COMMAND_FORMAT_ID_LOOP_M3_N2                         (8)
#define DWPU_COMMAND_FORMAT_ID_BYPASS                             (9)

//==================================================
// TYPES
//==================================================

//--------------------------------------------------
// Commands
//--------------------------------------------------

// TODO(schmuck): this should be overwritten with the actual token endpoints
typedef module_command_header_t dwpu_command_header_t;

// Formats
//--------------------------------------------------

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
  } payload;
} dwpu_command_format_loop_m1_n0_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t nested_0_start : 16;
    uint64_t nested_0_length : 16;
    uint64_t nested_0_iter : 24;
    uint64_t nested_0_map_main : 8;
  } payload;
} dwpu_command_format_loop_m1_n1_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t nested_0_start : 16;
    uint64_t nested_0_length : 16;
    uint64_t nested_0_iter : 24;
    uint64_t nested_0_map_main : 8;
    uint64_t nested_1_start : 16;
    uint64_t nested_1_length : 16;
    uint64_t nested_1_iter : 24;
    uint64_t nested_1_map_main : 8;
  } payload;
} dwpu_command_format_loop_m1_n2_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t main_1_start : 16;
    uint64_t main_1_length : 16;
    uint64_t main_1_iter : 24;
    uint64_t __reserved_8__ : 8;
  } payload;
} dwpu_command_format_loop_m2_n0_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t main_1_start : 16;
    uint64_t main_1_length : 16;
    uint64_t main_1_iter : 24;
    uint64_t __reserved_8__ : 8;
    uint64_t nested_0_start : 16;
    uint64_t nested_0_length : 16;
    uint64_t nested_0_iter : 24;
    uint64_t nested_0_map_main : 8;
  } payload;
} dwpu_command_format_loop_m2_n1_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t main_1_start : 16;
    uint64_t main_1_length : 16;
    uint64_t main_1_iter : 24;
    uint64_t __reserved_8__ : 8;
    uint64_t nested_0_start : 16;
    uint64_t nested_0_length : 16;
    uint64_t nested_0_iter : 24;
    uint64_t nested_0_map_main : 8;
    uint64_t nested_1_start : 16;
    uint64_t nested_1_length : 16;
    uint64_t nested_1_iter : 24;
    uint64_t nested_1_map_main : 8;
  } payload;
} dwpu_command_format_loop_m2_n2_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t main_1_start : 16;
    uint64_t main_1_length : 16;
    uint64_t main_1_iter : 24;
    uint64_t __reserved_8__ : 8;
    uint64_t main_2_start : 16;
    uint64_t main_2_length : 16;
    uint64_t main_2_iter : 24;
    uint64_t __reserved_12__ : 8;
  } payload;
} dwpu_command_format_loop_m3_n0_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t main_1_start : 16;
    uint64_t main_1_length : 16;
    uint64_t main_1_iter : 24;
    uint64_t __reserved_8__ : 8;
    uint64_t main_2_start : 16;
    uint64_t main_2_length : 16;
    uint64_t main_2_iter : 24;
    uint64_t __reserved_12__ : 8;
    uint64_t nested_0_start : 16;
    uint64_t nested_0_length : 16;
    uint64_t nested_0_iter : 24;
    uint64_t nested_0_map_main : 8;
  } payload;
} dwpu_command_format_loop_m3_n1_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    uint64_t main_0_start : 16;
    uint64_t main_0_length : 16;
    uint64_t main_0_iter : 24;
    uint64_t w_offset : 6;
    uint64_t __reserved_4__ : 2;
    uint64_t main_1_start : 16;
    uint64_t main_1_length : 16;
    uint64_t main_1_iter : 24;
    uint64_t __reserved_8__ : 8;
    uint64_t main_2_start : 16;
    uint64_t main_2_length : 16;
    uint64_t main_2_iter : 24;
    uint64_t __reserved_12__ : 8;
    uint64_t nested_0_start : 16;
    uint64_t nested_0_length : 16;
    uint64_t nested_0_iter : 24;
    uint64_t nested_0_map_main : 8;
    uint64_t nested_1_start : 16;
    uint64_t nested_1_length : 16;
    uint64_t nested_1_iter : 24;
    uint64_t nested_1_map_main : 8;
  } payload;
} dwpu_command_format_loop_m3_n2_t;

typedef struct {
  dwpu_command_header_t header;
  struct {
    // No fields
  } payload;
} dwpu_command_format_bypass_t;

// Command Union
//--------------------------------------------------

typedef union {
  module_command_t _command;
  dwpu_command_format_loop_m1_n0_t loop_m1_n0;
  dwpu_command_format_loop_m1_n1_t loop_m1_n1;
  dwpu_command_format_loop_m1_n2_t loop_m1_n2;
  dwpu_command_format_loop_m2_n0_t loop_m2_n0;
  dwpu_command_format_loop_m2_n1_t loop_m2_n1;
  dwpu_command_format_loop_m2_n2_t loop_m2_n2;
  dwpu_command_format_loop_m3_n0_t loop_m3_n0;
  dwpu_command_format_loop_m3_n1_t loop_m3_n1;
  dwpu_command_format_loop_m3_n2_t loop_m3_n2;
  dwpu_command_format_bypass_t bypass;
} dwpu_command_t;

//--------------------------------------------------
// Instructions
//--------------------------------------------------

// Instructions
//--------------------------------------------------

typedef struct {
  uint64_t opcode : 2;
  uint64_t op_exe : 1;
  uint64_t shift_sp : 1;
  uint64_t shift_wb : 1;
  uint64_t last_push : 1;
  uint64_t __reserved_5__ : 2;
  // TODO(schmuck): array fields don't work yet!
  uint64_t __reserved_7__ : 2;
  // TODO(schmuck): array fields don't work yet!
  uint64_t __reserved_9__ : 1;
} dwpu_instruction_t;

//--------------------------------------------------
// Interface
//--------------------------------------------------

typedef module_id_t dwpu_id_t;

typedef enum {
  DWPU_STATUS_OK = 0,
  DWPU_STATUS_ERROR,
} dwpu_status_t;

//==================================================
// GLOBAL FUNCTION PROTOTYPES
//==================================================

dwpu_status_t dwpu_init(void);

dwpu_status_t dwpu_enable_execution(dwpu_id_t dwpu_id);
dwpu_status_t dwpu_disable_execution(dwpu_id_t dwpu_id);
dwpu_status_t dwpu_poll_idle(dwpu_id_t dwpu_id);

dwpu_status_t dwpu_load_command(dwpu_id_t dwpu_id, dwpu_command_t* command);
dwpu_status_t dwpu_load_instructions(dwpu_id_t dwpu_id, dwpu_instruction_t instructions[], uint16_t count, uint16_t offset);

#endif  // __DWPU_H__
