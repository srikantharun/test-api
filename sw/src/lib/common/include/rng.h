// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

/**
 * Description: Function to generate pseudo random values
 */

#pragma once

#include <stdint.h>

/* xorshift random 64b number generator*/
uint64_t xorshift64(uint64_t *state);

/* Provide random offset within provided bounds and aligned to 64B */
uint64_t get_random_offset(uint64_t seed, uint64_t offset_max);
