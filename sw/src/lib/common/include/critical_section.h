#pragma once

#include <stdint.h>
#include <atomics.h>

// Enter the critical section
void enter_critical_section(atomic_flag* lock_ptr);
// Exit the critical section
void exit_critical_section(atomic_flag* lock_ptr);
// Disable interrupts
unsigned int arch_irq_lock();
// Enable interrupts
void arch_irq_unlock(unsigned int key);

