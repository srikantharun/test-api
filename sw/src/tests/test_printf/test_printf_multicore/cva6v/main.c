#include <asm.h>
#include <multicore.h>
#include <printf.h>
#include <platform.h>
#include <testutils.h>

volatile extern printf_t multicore_printf;

int main() {
  printf("Hi from CVA6V from hartid #%d! (using printf)\n", r_mhartid());
  printf("Bye from #%d.\n", r_mhartid());

  /* END TEST */
  return TEST_SUCCESS;
}
