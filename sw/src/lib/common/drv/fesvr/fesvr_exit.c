#include <stdint.h>
#include <stddef.h>

extern volatile uint64_t tohost;
extern volatile uint64_t fromhost;

void __attribute__((noreturn)) exit(int code)
{
  /* Ensure the exit code is not sign-extended to 64 bits. */
  uint64_t code_extended = (unsigned int)code;

  __sync_synchronize();
  tohost = (code_extended << 1) | 1;
  __sync_synchronize();

  while (1) {
   // reduce activity in the CPU: less power used, faster simulation
    asm("wfi");
  }
}
