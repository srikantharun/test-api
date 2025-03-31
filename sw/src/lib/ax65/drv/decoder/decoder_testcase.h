// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
// Description: C implementation of the Allegro decoder integration testbench
#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

enum decoder_testcase_instruction_type {
  DECODER_TESTCASE_INSTRUCTION_WRITE,
  DECODER_TESTCASE_INSTRUCTION_START_FRAME,
  DECODER_TESTCASE_INSTRUCTION_IRQ,
  DECODER_TESTCASE_INSTRUCTION_END_FRAME,
};

struct decoder_testcase_instruction {
  enum decoder_testcase_instruction_type type;
  // for WRITE
  uintptr_t address;
  uint32_t data;
  // for START_FRAME
  const char *frame_process;
  size_t frame_idx;
  // for IRQ
  uintptr_t irq_address;
  size_t irq_bit;
};

struct decoder_testcase_buffer {
  // identification
  const char *frame_process;
  size_t frame_idx;
  // contents
  void *data;
  size_t size;
  size_t full_size;
  uintptr_t load_address;
};

struct decoder_testcase {
  struct decoder_testcase_instruction *instructions;
  size_t instructions_length;
  struct decoder_testcase_buffer *in_buffers;
  size_t in_buffers_length;
  struct decoder_testcase_buffer *ref_buffers;
  size_t ref_buffers_length;
};

bool decoder_testcase_execute(struct decoder_testcase *testcase);
