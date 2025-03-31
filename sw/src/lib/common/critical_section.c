// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <critical_section.h>
#include <stdint.h>
#include <encoding.h>

static __thread atomic_uint_fast16_t nesting_level = 0;
static __thread uint64_t key = 0;

/*
 * use atomic instruction csrrc to lock global irq
 * csrrc: atomic read and clear bits in CSR register
 */
unsigned int arch_irq_lock(void)
{
	unsigned int key;

	__asm__ volatile ("csrrc %0, mstatus, %1"
			  : "=r" (key)
			  : "rK" (MSTATUS_MIE)
			  : "memory");

	return key;
}

/*
 * use atomic instruction csrs to unlock global irq
 * csrs: atomic set bits in CSR register
 */
void arch_irq_unlock(unsigned int key)
{
	__asm__ volatile ("csrs mstatus, %0"
			  :
			  : "r" (key & MSTATUS_MIE)
			  : "memory");
}

void enter_critical_section(atomic_flag* lock_ptr) {
  // if-statement for nested critical sections.
  if (atomic_fetch_add(&nesting_level, 1) == 0) {
      key = arch_irq_lock();
  }
  atomic_lock_acquire(lock_ptr);
}

void exit_critical_section(atomic_flag* lock_ptr) {
  atomic_lock_release(lock_ptr);
  // re-enabled interrupts only when exiting the outermost critical section.
  if (atomic_fetch_sub(&nesting_level, 1) == 1) {
      arch_irq_unlock(key);
  }
}

