#ifndef TEST_L1_DEFINES_H
#define TEST_L1_DEFINES_H

#include <stdint.h>

#define MINIBANK_ADDR_WIDTH 12 // bits
#define NB_L1_SUBBANKS 4
#define NB_L1_MINIBANKS 16
#define L1_MINIBANK_SIZE 4096     // Nb of 128-bit words in a single minibank
#define L1_MINIBANK_WORD_WIDTH 16 // bytes

// Return the address of a 128bit word at a specific offset with a minibank
// within a subbank
uintptr_t get_addr(uint64_t sb_idx, uint64_t mb_idx, uint64_t minibank_offset);

#endif
