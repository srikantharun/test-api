/*
 * test_math - testing support for math functions
 *
 * This is more intented to sanity-check the build flow, ensuring support
 * for mathemtical functions. It is not intended to verify the hardware's
 * functionality.
 */

#include <math.h>
#include <util.h>

int main() {
  // Make variables volatile to disallow compile-time optimization.
  volatile double x, y;
  x = 1.2345;
  y = sin(x);
  UNUSED(y);
  return 0;
}
