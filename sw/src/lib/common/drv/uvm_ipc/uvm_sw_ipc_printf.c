#include "uvm_sw_ipc.h"

int _printf(uint32_t arg_cnt, const char *fmt, ...)
{
  va_list args;
  va_start(args, fmt);

  uvm_sw_ipc_printf_va_list(arg_cnt, fmt, args);

  va_end(args);

  return 0;
}

