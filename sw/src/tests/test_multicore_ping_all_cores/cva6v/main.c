#include <asm.h>
#include <multicore.h>
#include <printf.h>
#include <platform.h>

int main() {
  return r_mhartid();
}
