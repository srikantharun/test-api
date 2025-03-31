/*
 * Copyright (c) 2012-2021 Andes Technology Corporation
 * All rights reserved.
 *
 */

#pragma once

#include <memorymap.h>
#include <util.h>
#include <asm.h>

#ifdef __cplusplus
extern "C" {
#endif

/* PLIC Feature Flags */
#define NDS_PLIC_FEATURE_PREEMPT (1 << 0)
#define NDS_PLIC_FEATURE_VECTORED (1 << 1)

/* Priority Register - 32 bits per source */
#define PLIC_PRIORITY_OFFSET (0x00000000UL)
#define PLIC_PRIORITY_SHIFT_PER_SOURCE 2

/* Pending Register - 1 bit per source */
#define PLIC_PENDING_OFFSET (0x00001000UL)
#define PLIC_PENDING_SHIFT_PER_SOURCE 0

/* Enable Register - 0x80 per target */
#define PLIC_ENABLE_OFFSET (0x00002000UL)
#define PLIC_ENABLE_SHIFT_PER_TARGET 7

/* Priority Threshold Register - 0x1000 per target */
#define PLIC_THRESHOLD_OFFSET (0x00200000UL)
#define PLIC_THRESHOLD_SHIFT_PER_TARGET 12

/* Claim Register - 0x1000 per target */
#define PLIC_CLAIM_OFFSET (0x00200004UL)
#define PLIC_CLAIM_SHIFT_PER_TARGET 12

__attribute__((noreturn)) void abort();

__attribute__((always_inline)) static inline unsigned long get_plic_base() {
  unsigned int hart_id = r_mhartid();

  if (hart_id <= APU_CORE_5){
    return APU_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_0){
    return AICORE_0_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_1){
    return AICORE_1_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_2){
    return AICORE_2_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_3){
    return AICORE_3_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_4){
    return AICORE_4_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_5){
    return AICORE_5_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_6){
    return AICORE_6_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else if (hart_id == AI_CORE_7){
    return AICORE_7_CONFIGURATION_PERIPHERALS_PLIC_BASE;
  }
  else {
    abort();
  }
}

__attribute__((always_inline)) static inline volatile unsigned int* get_plic_reg(
    unsigned long byte_offset) {
  return (volatile unsigned int*)(get_plic_base() + byte_offset);
}

__attribute__((always_inline)) static inline void __nds__plic_set_feature(unsigned int feature) {
  volatile unsigned int* feature_ptr = get_plic_reg(0);
  *feature_ptr = feature;
}

__attribute__((always_inline)) static inline void __nds__plic_set_threshold(
    unsigned int threshold) {
  volatile unsigned int* threshold_ptr = get_plic_reg(PLIC_THRESHOLD_OFFSET);
  *threshold_ptr = threshold;
}

__attribute__((always_inline)) static inline void __nds__plic_set_priority(unsigned int source,
                                                                           unsigned int priority) {
  volatile unsigned int* priority_ptr =
      get_plic_reg(PLIC_PRIORITY_OFFSET + (source << PLIC_PRIORITY_SHIFT_PER_SOURCE));
  *priority_ptr = priority;
}

__attribute__((always_inline)) static inline void __nds__plic_set_pending(unsigned int source) {
  volatile unsigned int* current_ptr = get_plic_reg(PLIC_PENDING_OFFSET + ((source >> 5) << 2));
  *current_ptr = (1 << (source & 0x1F));
}

__attribute__((always_inline)) static inline void __nds__plic_enable_interrupt(
    unsigned int source) {
  volatile unsigned int* current_ptr = get_plic_reg(PLIC_ENABLE_OFFSET + ((source >> 5) << 2));
  unsigned int current = *current_ptr;
  current = current | (1 << (source & 0x1F));
  *current_ptr = current;
}

__attribute__((always_inline)) static inline void __nds__plic_disable_interrupt(
    unsigned int source) {
  volatile unsigned int* current_ptr = get_plic_reg(PLIC_ENABLE_OFFSET + ((source >> 5) << 2));
  unsigned int current = *current_ptr;
  current = current & ~((1 << (source & 0x1F)));
  *current_ptr = current;
}

__attribute__((always_inline)) static inline unsigned int __nds__plic_claim_interrupt(void) {
  volatile unsigned int* claim_addr = get_plic_reg(PLIC_CLAIM_OFFSET);
  return *claim_addr;
}

__attribute__((always_inline)) static inline void __nds__plic_complete_interrupt(
    unsigned int source) {
  volatile unsigned int* claim_addr = get_plic_reg(PLIC_CLAIM_OFFSET);
  *claim_addr = source;
}

#ifdef APU_SW_PLIC_BASE

__attribute__((always_inline)) static inline void __nds__plic_sw_set_threshold(
    unsigned int threshold) {
  unsigned int hart_id = r_mhartid();
  volatile unsigned int* threshold_ptr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_THRESHOLD_OFFSET +
                               (hart_id << PLIC_THRESHOLD_SHIFT_PER_TARGET));
  *threshold_ptr = threshold;
}

__attribute__((always_inline)) static inline void __nds__plic_sw_set_priority(
    unsigned int source, unsigned int priority) {
  volatile unsigned int* priority_ptr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_PRIORITY_OFFSET +
                               (source << PLIC_PRIORITY_SHIFT_PER_SOURCE));
  *priority_ptr = priority;
}

__attribute__((always_inline)) static inline void __nds__plic_sw_set_pending(unsigned int source) {
  volatile unsigned int* current_ptr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_PENDING_OFFSET +
      ((source >> 5) << 2));
  *current_ptr = (1 << (source & 0x1F));
}

__attribute__((always_inline)) static inline void __nds__plic_sw_enable_interrupt(
    unsigned int source) {
  unsigned int hart_id = r_mhartid();
  volatile unsigned int* current_ptr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_ENABLE_OFFSET +
                               (hart_id << PLIC_ENABLE_SHIFT_PER_TARGET) + ((source >> 5) << 2));
  unsigned int current = *current_ptr;
  current = current | (1 << (source & 0x1F));
  *current_ptr = current;
}

__attribute__((always_inline)) static inline void __nds__plic_sw_disable_interrupt(
    unsigned int source) {
  unsigned int hart_id = r_mhartid();
  volatile unsigned int* current_ptr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_ENABLE_OFFSET +
                               (hart_id << PLIC_ENABLE_SHIFT_PER_TARGET) + ((source >> 5) << 2));
  unsigned int current = *current_ptr;
  current = current & ~((1 << (source & 0x1F)));
  *current_ptr = current;
}

__attribute__((always_inline)) static inline unsigned int __nds__plic_sw_claim_interrupt(void) {
  unsigned int hart_id = r_mhartid();
  volatile unsigned int* claim_addr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_CLAIM_OFFSET +
                               (hart_id << PLIC_CLAIM_SHIFT_PER_TARGET));
  return *claim_addr;
}

__attribute__((always_inline)) static inline void __nds__plic_sw_complete_interrupt(
    unsigned int source) {
  unsigned int hart_id = r_mhartid();
  volatile unsigned int* claim_addr =
      (volatile unsigned int*)(APU_SW_PLIC_BASE + PLIC_CLAIM_OFFSET +
                               (hart_id << PLIC_CLAIM_SHIFT_PER_TARGET));
  *claim_addr = source;
}

#endif  // APU_SW_PLIC_BASE

#ifdef __cplusplus
}
#endif
