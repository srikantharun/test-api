#include <printf.h>
#include <limits.h>
#include <util.h>
#include <reentrant_lock.h>

reentrant_lock_t printf_lock_apu = REENTRANT_LOCK_INIT;
printf_t multicore_printf;

int __attribute__((weak)) _putchar(int ch)
{
  UNUSED(ch);
  return 0;
}

void __attribute__((weak)) _init_printf()
{
  return;
}

int __attribute__((weak)) _printf(uint32_t arg_cnt, const char *fmt, ...)
{
  UNUSED(arg_cnt);

  va_list ap;
  va_start(ap, fmt);

  reentrant_lock_acquire(&printf_lock_apu);
  vprintfmt((void (*)(int, void **))_putchar, 0, fmt, ap);
  reentrant_lock_release(&printf_lock_apu);

  va_end(ap);
  return 0; // incorrect return value, but who cares, anyway?
}
