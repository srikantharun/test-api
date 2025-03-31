// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

//==================================================
// INCLUDES
//==================================================

#include "mvmprg.h"

#include "module.h"

//==================================================
// MACROS
//==================================================

//==================================================
// DEFINITIONS
//==================================================

//==================================================
// TYPES
//==================================================

//--------------------------------------------------
// CSRs
//--------------------------------------------------

// Registers
//--------------------------------------------------

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t exec_en : 1;
  uint64_t ptr_rst : 1;
  uint64_t __reserved_2__ : 62;
} csr_register_cmdblk_ctrl_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t state : 2;
  uint64_t wait_token : 1;
  uint64_t __reserved_2__ : 5;
  uint64_t in_word_ptr : 8;
  uint64_t fifo_cnt : 8;
  uint64_t outst_cmds : 8;
  uint64_t pending_tokens : 16;
  uint64_t __reserved_7__ : 16;
} csr_register_cmdblk_status_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t signed_weights : 1;
  uint64_t __reserved_1__ : 63;
} csr_register_dp_ctrl_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t __reserved_0__ : 4;
  uint64_t in1_vld : 1;
  uint64_t in1_rdy : 1;
  uint64_t in1_lst : 1;
  uint64_t in1_stl : 1;
  uint64_t __reserved_5__ : 12;
  uint64_t dpcmd1_vld : 1;
  uint64_t dpcmd1_rdy : 1;
  uint64_t dpcmd1_lst : 1;
  uint64_t dpcmd1_stl : 1;
  uint64_t __reserved_10__ : 8;
  uint64_t imc_acc_prg_rdy : 1;
  uint64_t imc_acc_prg_vld : 1;
  uint64_t imc_acc_prg_row : 9;
  uint64_t imc_acc_prg_wset : 2;
  uint64_t __reserved_15__ : 19;
} csr_register_dp_status_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t __reserved_0__ : 4;
  uint64_t in1_vld : 1;
  uint64_t in1_rdy : 1;
  uint64_t in1_lst : 1;
  uint64_t __reserved_4__ : 13;
  uint64_t dpcmd1_vld : 1;
  uint64_t dpcmd1_rdy : 1;
  uint64_t dpcmd1_lst : 1;
  uint64_t __reserved_8__ : 41;
} csr_register_dbg_observe_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t row_counter : 9;
  uint64_t __reserved_1__ : 7;
  uint64_t col_counter_pw : 3;
  uint64_t __reserved_3__ : 13;
  uint64_t prog_write_ena : 16;
  uint64_t prog_row : 9;
  uint64_t prog_wset : 4;
  uint64_t fsm_state : 1;
  uint64_t __reserved_8__ : 2;
} csr_register_cmdgen_status_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t block_id : 8;
  uint64_t ai_core_id : 8;
  uint64_t hw_revision : 8;
  uint64_t __reserved_3__ : 40;
} csr_register_dbg_id_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t cmd_fifo_depth : 8;
  uint64_t __reserved_1__ : 56;
} csr_register_hw_capability_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t busy_state_en : 1;
  uint64_t idle_state_en : 1;
  uint64_t io_stall_en : 1;
  uint64_t token_stall_en : 1;
  uint64_t __reserved_4__ : 60;
} csr_register_perf_ctrl_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t busy_state_cnt : 32;
  uint64_t idle_state_cnt : 32;
} csr_register_perf_state_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t io_stall_cnt : 32;
  uint64_t token_stall_cnt : 32;
} csr_register_perf_stall_t;

// CSR
//--------------------------------------------------

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  csr_register_cmdblk_ctrl_t cmdblk_ctrl;
  csr_register_cmdblk_status_t cmdblk_status;
  uint64_t __reserved_2__;
  uint64_t __reserved_3__;
  csr_register_dp_ctrl_t dp_ctrl;
  csr_register_dp_status_t dp_status;
  csr_register_dbg_observe_t dbg_observe;
  csr_register_cmdgen_status_t cmdgen_status;
  uint64_t __reserved_8__;
  csr_register_dbg_id_t dbg_id;
  csr_register_hw_capability_t hw_capability;
  csr_register_perf_ctrl_t perf_ctrl;
  csr_register_perf_state_t perf_state;
  csr_register_perf_stall_t perf_stall;
} csr_t;

//==================================================
// DATA
//==================================================

//==================================================
// LOCAL FUNCTION DECLARATIONS
//==================================================

//==================================================
// LOCAL FUNCTION DEFINITIONS
//==================================================

//==================================================
// GLOBAL FUNCTION DEFINITIONS
//==================================================

inline mvmprg_status_t mvmprg_init(void) {
  return (mvmprg_status_t) module_init();
}

inline mvmprg_status_t mvmprg_enable_execution(mvmprg_id_t mvmprg_id) {
  return (mvmprg_status_t) module_enable_execution((module_id_t) mvmprg_id);
}

inline mvmprg_status_t mvmprg_disable_execution(mvmprg_id_t mvmprg_id) {
  return (mvmprg_status_t) module_disable_execution((module_id_t) mvmprg_id);
}

inline mvmprg_status_t mvmprg_poll_idle(mvmprg_id_t mvmprg_id) {
  return (mvmprg_status_t) module_poll_idle((module_id_t) mvmprg_id);
}

inline mvmprg_status_t mvmprg_load_command(mvmprg_id_t mvmprg_id, mvmprg_command_t* command) {
  return (mvmprg_status_t) module_load_command((module_id_t) mvmprg_id, (module_command_t*) command);
}
