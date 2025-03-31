#include <printf.h>
#include <testutils.h>
#include <memorymap.h>

int main() {
    float f = 12.3456;

    printf("Printing float from CVA6V f=%f\r\n", CVA6V_PRINTF_FLOAT(f));

    return TEST_SUCCESS;
}
