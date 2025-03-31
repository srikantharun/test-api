#pragma once

#include <stdint.h>
#include <string.h>
#include <printf_common.h>

int _printf(uint32_t arg_cnt, const char *fmt, ...);
int _putchar(int ch);
void _init_printf();
