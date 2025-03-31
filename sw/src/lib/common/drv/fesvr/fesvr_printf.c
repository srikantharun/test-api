#include "fesvr_syscalls.h"
#include "printf.h"

int _putchar(int ch)
{
  static __thread char buf[64] __attribute__((aligned(64)));
  static __thread int buflen = 0;

  buf[buflen++] = ch;

  if (ch == '\n' || buflen == sizeof(buf))
  {
    fesvr_syscall(SYS_write, 1, (uintptr_t)buf, buflen);
    buflen = 0;
  }

  return 0;
}

int _printf(uint32_t arg_cnt, const char *fmt, ...)
{
  UNUSED(arg_cnt);

  va_list ap;
  va_start(ap, fmt);

  vprintfmt((void (*)(int, void **))_putchar, 0, fmt, ap);

  va_end(ap);
  return 0; // incorrect return value, but who cares, anyway?
}
