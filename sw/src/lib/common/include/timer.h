#pragma once

#include <stdint.h>
#include <encoding.h>

/* Core frequency is 90MHz */
#define CORE_FREQUENCY_MHz 90

#define MSEC_TO_USEC 1000

/**
 * @brief Delays execution for a specified number of microseconds.
 *
 * This function creates a busy-wait loop, delaying execution for at least
 * the specified number of microseconds.
 *
 * @param usec The delay time in microseconds.
 *
 * Example:
 *        udelay(40000000) // 40 seconds delay
 */
void udelay(uint64_t usec);

/**
 * @brief The time_us function provides the current time in microseconds since the
 *        system started. It leverages the RISC-V mcycle register.
 *
 * @return The number of microseconds elapsed since the system was powered on.
 *
 * Example:
 *        uint64_t start_time = time_us();
 *        // Code to measure the duration of
 *        uint64_t end_time = time_us();
 */
long time_us(void);

/*
 * @brief Returns the number of milliseconds elapsed since @p base
 *
 * @param base the epoch timestamp to use as reference
 *
 * @returns the number of milliseconds elapsed
 */
unsigned int get_timer(unsigned int base);


/*
 * @brief Returns the number of passed cycle
 *
 * @returns the currecnt cycle counter
 */
void cycledelay(uint64_t cycles);

/*
 * @brief Returns the current cycle counter
 *
 * @param the cycle count to compare against
 *
 * @returns the currecnt cycle counter
 */
static inline unsigned long read_cycles() {
  unsigned long cycles;
  asm volatile("rdcycle %0" : "=r"(cycles));
  return cycles;
}
