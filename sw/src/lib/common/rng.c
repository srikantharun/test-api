// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <rng.h>


uint64_t xorshift64(uint64_t *state) {
  uint64_t x = *state;
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  return *state = x;
}

uint64_t get_random_offset(uint64_t seed, uint64_t offset_max) {
  xorshift64(&seed);
  // Keep in bounds
  seed %= offset_max;
  // Align to 64 Bytes
  seed >>= 6;
  seed <<= 6;
  return seed;
}
