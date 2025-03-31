#include <printf.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>

int main() {
    char buf[128];

    testcase_init();

#if HW_DEFINES_APU_CORE_NUMBER != 1
    // Print single float from CVA6V
    enable_simple_multicore_printf(APU_CORE_5);
    start_core(PVE_0_CLUSTER_0_CORE_0);
    CHECK_TRUE(wait_core(PVE_0_CLUSTER_0_CORE_0) == TEST_SUCCESS);
    disable_simple_multicore_printf(APU_CORE_5);
#endif

    printf("Testing positive floats...\n");
    sprintf(buf, "%10f", 1234.000);
    CHECK_TRUE(strcmp(buf, "  1234.000") == 0, "positive float with no fractional part");
    sprintf(buf, "%10f", 1234.564);
    CHECK_TRUE(strcmp(buf, "  1234.564") == 0, "positive float with fractional part");
    sprintf(buf, "%10f", 1234.52364);
    CHECK_TRUE(strcmp(buf, "  1234.524") == 0, "positive float with more precision");


    printf("Testing negative floats...\n");
    sprintf(buf, "%11f", -1234.000);
    CHECK_TRUE(strcmp(buf, "  -1234.000") == 0, "negative float with no fractional part");
    sprintf(buf, "%11f", -1234.564);
    CHECK_TRUE(strcmp(buf, "  -1234.564") == 0, "negative float with fractional part");
    sprintf(buf, "%11f", -1234.52364);
    CHECK_TRUE(strcmp(buf, "  -1234.524") == 0, "negative float with more precision");


    printf("Testing edge cases...\n");
    sprintf(buf, "%9f", 0.000);
    CHECK_TRUE(strcmp(buf, "    0.000") == 0, "smallest positive float");
    sprintf(buf, "%9f", 0.001);
    CHECK_TRUE(strcmp(buf, "    0.001") == 0, "smallest positive float close to zero");
    sprintf(buf, "%9f", -0.001);
    CHECK_TRUE(strcmp(buf, "   -0.001") == 0, "smallest negative float close to zero");


    printf("Testing very large numbers...\n");
    sprintf(buf, "%20f", 1.234567e+6);
    CHECK_TRUE(strcmp(buf, "         1234567.000") == 0, "large positive float");
    sprintf(buf, "%20f", -1.234567e+6);
    CHECK_TRUE(strcmp(buf, "        -1234567.000") == 0, "large negative float");


    printf("Testing very small numbers...\n");
    sprintf(buf, "%7f", 1.234567e-6);
    CHECK_TRUE(strcmp(buf, "  0.000") == 0, "small positive float");
    sprintf(buf, "%7f", -1.234567e-6);
    CHECK_TRUE(strcmp(buf, " -0.000") == 0, "small negative float");

    return testcase_finalize();
}
