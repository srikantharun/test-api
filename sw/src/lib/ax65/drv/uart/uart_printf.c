#include <clk/drv_clk.h>
#include <platform.h>
#include "drv_uart.h"

void _init_printf()
{
    init_uart(CLK_SOC_PERIPH_Hz, UART_DEFAULT_BAUD_RATE);
    // send newline
    _putchar('\r');
    _putchar('\n');
}

int _putchar(int ch)
{
  static __thread char buf[64] __attribute__((aligned(64)));
  static __thread int buflen = 0;
  static __thread int bufoffset = 0;

  buf[bufoffset + buflen++] = (char)ch;

  if (ch == '\n' || buflen == 8)
  {
    put_buf(buf + bufoffset, buflen);

    buflen = 0;
    bufoffset = (bufoffset + 8) % 64;
  }

  return (unsigned char) ch;
}
