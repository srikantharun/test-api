#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include "string.h"
#include <util.h>

void *memcpy(void *dest, const void *src, size_t len)
{
  if ((((uintptr_t)dest | (uintptr_t)src | len) & (sizeof(uintptr_t) - 1)) == 0)
  {
    const uintptr_t *s = src;
    uintptr_t *d = dest;
    uintptr_t *end = dest + len;
    while (d + 8 < end)
    {
      uintptr_t reg[8] = {s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]};
      d[0] = reg[0];
      d[1] = reg[1];
      d[2] = reg[2];
      d[3] = reg[3];
      d[4] = reg[4];
      d[5] = reg[5];
      d[6] = reg[6];
      d[7] = reg[7];
      d += 8;
      s += 8;
    }
    while (d < end)
      *d++ = *s++;
  }
  else
  {
    const char *s = src;
    char *d = dest;
    while (d < (char *)(dest + len))
      *d++ = *s++;
  }
  return dest;
}

void *memset(void *dest, int byte, size_t len)
{
  if ((((uintptr_t)dest | len) & (sizeof(uintptr_t) - 1)) == 0)
  {
    uintptr_t word = byte & 0xFF;
    word |= word << 8;
    word |= word << 16;
    word |= word << 16 << 16;

    uintptr_t *d = dest;
    while (d < (uintptr_t *)(dest + len))
      *d++ = word;
  }
  else
  {
    char *d = dest;
    while (d < (char *)(dest + len))
      *d++ = byte;
  }
  return dest;
}

int memcmp(const void *s1, const void *s2, size_t n) {
  const uint8_t* p1 = (const uint8_t*)s1;
  const uint8_t* p2 = (const uint8_t*)s2;

  while (n-- != 0) {
    if (*p1 != *p2) {
      return *p1 - *p2;
    }
    p1++;
    p2++;
  }

  return 0;
}

static inline void printnum(void (*putch)(int, void **), void **putdat,
                            unsigned long long num, unsigned base, int width, int padc)
{
  unsigned digs[sizeof(num) * CHAR_BIT];
  int pos = 0;

  while (1)
  {
    digs[pos++] = num % base;
    if (num < base)
      break;
    num /= base;
  }

  while (width-- > pos)
    putch(padc, putdat);

  while (pos-- > 0)
    putch(digs[pos] + (digs[pos] >= 10 ? 'a' - 10 : '0'), putdat);
}

static unsigned long long getuint(va_list *ap, int lflag)
{
  if (lflag >= 2)
    return va_arg(*ap, unsigned long long);
  else if (lflag)
    return va_arg(*ap, unsigned long);
  else
    return va_arg(*ap, unsigned int);
}

static long long getint(va_list *ap, int lflag)
{
  if (lflag >= 2)
    return va_arg(*ap, long long);
  else if (lflag)
    return va_arg(*ap, long);
  else
    return va_arg(*ap, int);
}

void vprintfmt(void (*putch)(int, void **), void **putdat, const char *fmt, va_list ap)
{
  register const char *p;
  const char *last_fmt;
  register int ch;
  unsigned long long num;
  int base, lflag, width, precision, altflag;
  char padc;

  UNUSED(altflag);

  while (1)
  {
    while ((ch = *(unsigned char *)fmt) != '%')
    {
      if (ch == '\0')
        return;
      fmt++;
      putch(ch, putdat);
    }
    fmt++;

    // Process a %-escape sequence
    last_fmt = fmt;
    padc = ' ';
    width = -1;
    precision = -1;
    lflag = 0;
    altflag = 0;
  reswitch:
    switch (ch = *(unsigned char *)fmt++)
    {

    // flag to pad on the right
    case '-':
      padc = '-';
      goto reswitch;

    // flag to pad with 0's instead of spaces
    case '0':
      padc = '0';
      goto reswitch;

    // width field
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      for (precision = 0;; ++fmt)
      {
        precision = precision * 10 + ch - '0';
        ch = *fmt;
        if (ch < '0' || ch > '9')
          break;
      }
      goto process_precision;

    case '*':
      precision = va_arg(ap, int);
      goto process_precision;

    case '.':
      if (width < 0)
        width = 0;
      goto reswitch;

    case '#':
      altflag = 1;
      goto reswitch;

    process_precision:
      if (width < 0)
        width = precision, precision = -1;
      goto reswitch;

    // long flag (doubled for long long)
    case 'l':
      lflag++;
      goto reswitch;

    // character
    case 'c':
      putch(va_arg(ap, int), putdat);
      break;

    // string
    case 's':
      if ((p = va_arg(ap, char *)) == NULL)
        p = "(null)";
      if (width > 0 && padc != '-')
        for (width -= strnlen(p, precision); width > 0; width--)
          putch(padc, putdat);
      for (; (ch = *p) != '\0' && (precision < 0 || --precision >= 0); width--)
      {
        putch(ch, putdat);
        p++;
      }
      for (; width > 0; width--)
        putch(' ', putdat);
      break;

    // (signed) decimal
    case 'd':
      num = getint(&ap, lflag);
      if ((long long)num < 0)
      {
        putch('-', putdat);
        num = -(long long)num;
      }
      base = 10;
      goto signed_number;

    // unsigned decimal
    case 'u':
      base = 10;
      goto unsigned_number;

    // (unsigned) octal
    case 'o':
      // should do something with padding so it's always 3 octits
      base = 8;
      goto unsigned_number;

    // pointer
    _Static_assert(sizeof(long) == sizeof(void *), "");
    case 'p':
      lflag = 1;
      putch('0', putdat);
      putch('x', putdat);
      /* fall through to 'x' */

    // (unsigned) hexadecimal
    case 'x':
      base = 16;
    unsigned_number:
      num = getuint(&ap, lflag);
    signed_number:
      printnum(putch, putdat, num, base, width, padc);
      break;

    // escaped '%' character
    case '%':
      putch(ch, putdat);
      break;

    case 'f':{
      float f;
      int is_negative = 0;
      int integer_part = 0;
      int fractional_part = 0;

      if (__riscv_flen == 64) {
        // Correct implementation as used on the APU
        double d = va_arg(ap, double);
        f = (float)d;

      } else {
        // Doubles are not supported for CVA6 - use custom hack.
        uintptr_t f_ptr = va_arg(ap, uintptr_t);
        f = *(float *)f_ptr;
      }

      // Handle negative numbers
      if (f < 0) {
          f = -f;
          is_negative = 1;
      }

      // Get the integer part
      integer_part = (int)f;

      // Calculate the fractional part and round it up to get three decimal places
      fractional_part = (int)((f-(float)integer_part)*1000 + (float)0.5);

      int num_width = 0;
      if (integer_part == 0) {
          num_width = 1; // Width of 0 is 1
      } else {
          int temp = integer_part;
          while (temp) {
              num_width++;
              temp /= 10;
          }
      }

      // Adjust the total width
      // The total length includes: integer part width + 1 (for '.') + 3 (for fractional part) + 1 (if negative)
      int total_width = num_width + 1 + 3 + (is_negative ? 1 : 0);

      // Print leading spaces for padding
      while (width > total_width) {
          putch(' ', putdat);
          width--;
      }

      // Print negative sign if float is negative
      if (is_negative) {
          putch('-', putdat);
      }

      // Print the integer part
      printnum(putch, putdat, integer_part, 10, 0, ' ');

      // Print the decimal point
      putch('.', putdat);

      // Print the fractional part with leading zeros if necessary
      printnum(putch, putdat, fractional_part, 10, 3, '0');

      break;
    }
    // unrecognized escape sequence - just print it literally
    default:
      putch('%', putdat);
      fmt = last_fmt;
      break;
    }
  }
}


static void sprintf_putch(int ch, void **data)
{
  char **pstr = (char **)data;
  **pstr = ch;
  (*pstr)++;
}

int vsprintf(char *str, const char *fmt, va_list ap)
{
    char *str0 = str;
    vprintfmt(sprintf_putch, (void **)&str, fmt, ap);
    *str = '\0';  // Null-terminate the string
    return str - str0;  // Return the length of the string written
}

int sprintf(char *str, const char *fmt, ...)
{
  va_list ap;
  char *str0 = str;
  va_start(ap, fmt);


  vprintfmt(sprintf_putch, (void **)&str, fmt, ap);
  *str = 0;

  va_end(ap);
  return str - str0;
}

size_t strlen(const char *s)
{
  const char *p = s;
  while (*p)
    p++;
  return p - s;
}

size_t strnlen(const char *s, size_t n)
{
  const char *p = s;
  while (n-- && *p)
    p++;
  return p - s;
}

int strcmp(const char *s1, const char *s2)
{
  unsigned char c1, c2;

  do
  {
    c1 = *s1++;
    c2 = *s2++;
  } while (c1 != 0 && c1 == c2);

  return c1 - c2;
}

int strncmp(const char *s1, const char *s2, size_t n)
{
  unsigned char c1, c2;

  for(size_t i = 0; i < n; i++)
  {
    c1 = *s1++;
    c2 = *s2++;
    if (c1 == 0 || c1 != c2)
      return c1 - c2;
  }

  return 0;
}

char *strcpy(char *dest, const char *src)
{
  char *d = dest;
  while ((*d++ = *src++))
    ;
  return dest;
}

char *strrchr(const char *str, int c) {
  char *match = 0;
  do {
    if (*str == c)
      match = (char*) str;
  } while (*str++);
  return match;
}

long atol(const char *str)
{
  long res = 0;
  int sign = 0;

  while (*str == ' ')
    str++;

  if (*str == '-' || *str == '+')
  {
    sign = *str == '-';
    str++;
  }

  while (*str)
  {
    res *= 10;
    res += *str++ - '0';
  }

  return sign ? -res : res;
}
