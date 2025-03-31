#include <memorymap.h>
#include <stdint.h>
#include <test_aicore_l1_access/aicore/test_l1_common.h>
#include <testutils.h>

uintptr_t get_addr(uint64_t sb_idx, uint64_t mb_idx, uint64_t minibank_offset) {
  ASSERT(sb_idx < NB_L1_SUBBANKS);
  ASSERT(mb_idx < NB_L1_MINIBANKS);
  ASSERT(minibank_offset < L1_MINIBANK_SIZE);

  uintptr_t l1_base_address = AICORE_0_L1_BASE + AICORE_0_SIZE * (r_mhartid()-AI_CORE_0);

  uintptr_t address = l1_base_address +
                      (L1_MINIBANK_WORD_WIDTH * NB_L1_SUBBANKS *
                       NB_L1_MINIBANKS * minibank_offset) +
                      (mb_idx * NB_L1_SUBBANKS * L1_MINIBANK_WORD_WIDTH) +
                      (sb_idx * L1_MINIBANK_WORD_WIDTH);
  return address;
}
