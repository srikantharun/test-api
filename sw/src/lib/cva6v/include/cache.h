#pragma once

#include <cva6_csr.h>
#include <encoding.h>

static inline void icache_enable() {
  write_csr(CVA6_ICACHE, 0b1);
}

static inline void icache_disable() {
  write_csr(CVA6_ICACHE, 0b0);
}

static inline void dcache_enable() {
  write_csr(CVA6_DCACHE, 0b1);
}

static inline void dcache_disable() {
  write_csr(CVA6_DCACHE, 0b0);
}
