#pragma once

#define SV_TASK_DECL(periph_name)                                              \
  extern "C" int periph_name##_read(const svBitVecVal *addr,                   \
                                    svBitVecVal *data, int len, char *resp);   \
  extern "C" int periph_name##_write(                                          \
      const svBitVecVal *addr, const svBitVecVal *data, int len, char *resp);
