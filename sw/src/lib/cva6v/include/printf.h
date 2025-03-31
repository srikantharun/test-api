#pragma once

#include <stdint.h>
#include <string.h>
#include <printf_common.h>

#define CVA6V_PRINTF_FLOAT(value) ((uintptr_t)&(value))

int _printf(uint32_t arg_cnt, const char *fmt, ...);
