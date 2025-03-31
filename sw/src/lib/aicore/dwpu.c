// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

//==================================================
// INCLUDES
//==================================================

#include "dwpu.h"

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
  uint64_t err_act_stream_in : 1;
  uint64_t err_act_stream_out : 1;
  uint64_t err_illegal_format : 1;
  uint64_t err_empty_program : 1;
  uint64_t err_main_0_length : 1;
  uint64_t err_main_1_length : 1;
  uint64_t err_main_2_length : 1;
  uint64_t err_nested_0_length : 1;
  uint64_t err_nested_1_length : 1;
  uint64_t err_nested_0_mapping : 1;
  uint64_t err_nested_1_mapping : 1;
  uint64_t err_nested_0_segfault : 1;
  uint64_t err_nested_1_segfault : 1;
  uint64_t err_nested_order : 1;
  uint64_t err_nested_nesting : 1;
  uint64_t err_nested_overlap : 1;
  uint64_t cmdblk_cmd_dropped : 1;
  uint64_t __reserved_17__ : 15;
  uint64_t dbg_sw_interrupt : 1;
  uint64_t __reserved_19__ : 31;
} csr_register_irq_en_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t err_act_stream_in : 1;
  uint64_t err_act_stream_out : 1;
  uint64_t err_illegal_format : 1;
  uint64_t err_empty_program : 1;
  uint64_t err_main_0_length : 1;
  uint64_t err_main_1_length : 1;
  uint64_t err_main_2_length : 1;
  uint64_t err_nested_0_length : 1;
  uint64_t err_nested_1_length : 1;
  uint64_t err_nested_0_mapping : 1;
  uint64_t err_nested_1_mapping : 1;
  uint64_t err_nested_0_segfault : 1;
  uint64_t err_nested_1_segfault : 1;
  uint64_t err_nested_order : 1;
  uint64_t err_nested_nesting : 1;
  uint64_t err_nested_overlap : 1;
  uint64_t cmdblk_cmd_dropped : 1;
  uint64_t __reserved_17__ : 15;
  uint64_t dbg_sw_interrupt : 1;
  uint64_t __reserved_19__ : 31;
} csr_register_irq_status_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t weights_sgn : 1;
  uint64_t image_sgn : 1;
  uint64_t skip_illegal_prog : 1;
  uint64_t __reserved_3__ : 29;
  uint64_t dbg_sw_irq : 1;
  uint64_t __reserved_5__ : 31;
} csr_register_dp_ctrl_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t in0_vld : 1;
  uint64_t in0_rdy : 1;
  uint64_t in0_lst : 1;
  uint64_t in0_stl : 1;
  uint64_t __reserved_4__ : 4;
  uint64_t out_vld : 1;
  uint64_t out_rdy : 1;
  uint64_t out_lst : 1;
  uint64_t out_stl : 1;
  uint64_t __reserved_9__ : 4;
  uint64_t dpcmd0_vld : 1;
  uint64_t dpcmd0_rdy : 1;
  uint64_t dpcmd0_lst : 1;
  uint64_t dpcmd0_stl : 1;
  uint64_t __reserved_14__ : 12;
  uint64_t current_op : 2;
  uint64_t op_mode : 1;
  uint64_t pipe_flushed : 1;
  uint64_t __reserved_18__ : 12;
  uint64_t ch_in_lst : 1;
  uint64_t ch_in_rdy : 1;
  uint64_t ch_in_vld : 1;
  uint64_t ch_out_lst : 1;
  uint64_t ch_out_rdy : 1;
  uint64_t ch_out_vld : 1;
  uint64_t __reserved_25__ : 10;
} csr_register_dp_status_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t in0_vld : 1;
  uint64_t in0_rdy : 1;
  uint64_t in0_lst : 1;
  uint64_t __reserved_3__ : 5;
  uint64_t out_vld : 1;
  uint64_t out_rdy : 1;
  uint64_t out_lst : 1;
  uint64_t __reserved_7__ : 5;
  uint64_t dpcmd0_vld : 1;
  uint64_t dpcmd0_rdy : 1;
  uint64_t dpcmd0_lst : 1;
  uint64_t __reserved_11__ : 45;
} csr_register_dbg_observe_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t main_index : 8;
  uint64_t overall_last : 1;
  uint64_t __reserved_2__ : 55;
} csr_register_cmdgen_status_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t scratch : 64;
} csr_register_dbg_scratch_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t block_id : 8;
  uint64_t ai_core_id : 8;
  uint64_t hw_revision : 8;
  uint64_t __reserved_3__ : 40;
} csr_register_dbg_id_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t cmd_fifo_depth : 8;
  uint64_t __reserved_1__ : 8;
  uint64_t instr_mem_depth : 16;
  uint64_t __reserved_3__ : 32;
} csr_register_hw_capability_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t busy_state_en : 1;
  uint64_t idle_state_en : 1;
  uint64_t io_stall_en : 1;
  uint64_t token_stall_en : 1;
  uint64_t in0_stall_en : 1;
  uint64_t __reserved_5__ : 1;
  uint64_t out_stall_en : 1;
  uint64_t __reserved_7__ : 57;
} csr_register_perf_ctrl_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t busy_state_cnt : 32;
  uint64_t idle_state_cnt : 32;
} csr_register_perf_state_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t io_stall_cnt : 32;
  uint64_t token_stall_cnt : 32;
} csr_register_perf_stall_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t in0_stall_cnt : 32;
  uint64_t __reserved_1__ : 32;
} csr_register_perf_stall_in_t;

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  uint64_t out_stall_cnt : 32;
  uint64_t __reserved_1__ : 32;
} csr_register_perf_stall_out_t;

// CSR
//--------------------------------------------------

typedef __attribute__((aligned(sizeof(uint64_t)))) struct {
  csr_register_cmdblk_ctrl_t cmdblk_ctrl;
  csr_register_cmdblk_status_t cmdblk_status;
  csr_register_irq_en_t irq_en;
  csr_register_irq_status_t irq_status;
  csr_register_dp_ctrl_t dp_ctrl;
  csr_register_dp_status_t dp_status;
  csr_register_dbg_observe_t dbg_observe;
  csr_register_cmdgen_status_t cmdgen_status;
  csr_register_dbg_scratch_t dbg_scratch;
  csr_register_dbg_id_t dbg_id;
  csr_register_hw_capability_t hw_capability;
  csr_register_perf_ctrl_t perf_ctrl;
  csr_register_perf_state_t perf_state;
  csr_register_perf_stall_t perf_stall;
  csr_register_perf_stall_in_t perf_stall_in;
  csr_register_perf_stall_out_t perf_stall_out;
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

inline dwpu_status_t dwpu_init(void) {
  return (dwpu_status_t) module_init();
}

inline dwpu_status_t dwpu_enable_execution(dwpu_id_t dwpu_id) {
  return (dwpu_status_t) module_enable_execution((module_id_t) dwpu_id);
}

inline dwpu_status_t dwpu_disable_execution(dwpu_id_t dwpu_id) {
  return (dwpu_status_t) module_disable_execution((module_id_t) dwpu_id);
}

inline dwpu_status_t dwpu_poll_idle(dwpu_id_t dwpu_id) {
  return (dwpu_status_t) module_poll_idle((module_id_t) dwpu_id);
}

inline dwpu_status_t dwpu_load_command(dwpu_id_t dwpu_id, dwpu_command_t* command) {
  return (dwpu_status_t) module_load_command((module_id_t) dwpu_id, (module_command_t*) command);
}

inline dwpu_status_t dwpu_load_instructions(dwpu_id_t dwpu_id, dwpu_instruction_t instructions[], uint16_t count, uint16_t offset) {
  return (dwpu_status_t) module_load_instructions((module_id_t) dwpu_id, (void*) instructions, count, offset);
}
