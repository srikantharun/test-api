#include "printf.h"

#ifdef SYSTEM_TOP
extern printf_t multicore_printf;
#else
printf_t multicore_printf;
#endif

int __attribute__((weak)) _putchar(int ch)
{
  UNUSED(ch);
  return 0;
}

int __attribute__((weak)) _printf(uint32_t arg_cnt, const char *fmt, ...)
{
  // If APU is not reading any buffers, return directly.
  if(!multicore_printf.status) {
    return 0;
  }

  UNUSED(arg_cnt);

  va_list ap;
  va_start(ap, fmt);

  reentrant_lock_acquire(&(multicore_printf.lock));
  while(multicore_printf.status != PRINTF_IDLE) {};
  multicore_printf.status = PRINTF_FILLING;

  vsprintf((char *)multicore_printf.buf, fmt, ap);

  multicore_printf.status = PRINTF_EXITED;
  reentrant_lock_release(&(multicore_printf.lock));

  va_end(ap);
  return 0; // incorrect return value, but who cares, anyway?
}
