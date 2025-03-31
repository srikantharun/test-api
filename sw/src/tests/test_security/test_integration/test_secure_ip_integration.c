// femtoRoTIntegration.cpp : Defines the entry point for the console application.
//

#include <printf.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <memorymap.h>
#include "include/secure_ip.h"
#include "include/secure_ip_hal.h"
#include "include/test_secure_ip_hw.h"
#include "include/test_secure_ip_cb.h"
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>


/**
Macro to standardize how tests are shown in logs
*/
#define PRINT_TEST_NAME(function_name) \
     printf( "%s: ", #function_name)

/**
Macro to standardize calls to HW tests
*/
#define TEST(function_name)                     \
    PRINT_TEST_NAME(function_name);             \
    status = function_name();                   \
    if (status) {                               \
        printf( "\n%s: FAIL (status %0d)\n", #function_name, status);   \
        error_count++;                          \
    }                                            \
    else {                                      \
        printf( "PASS\n");   \
    }


/**
Entry point

\return Number of errors (0 in case of success)
*/

int main()
{
    /* HW interfaces tests */
    int test_kse3_if_release_ena = 0;
    int test_kse3_if_integration_ena = 0;
    int test_kse3_if_nagra_tb_ena = 0;

    /* Applicative tests */
    int test_kse3_aes_ena = 0;
    int test_kse3_sha2_ena = 0;
    int test_kse3_modarith_ena = 0;
    int test_kse3_sponge_ena = 0;
    int test_kse3_sha3_ena = 0;

    int test_hw_interface = 0;
    int test_cryptobox = 0;

    log_open("kse3_integration.log");

    test_kse3_if_release_ena = 1;
    test_kse3_if_integration_ena = 1;    // Signoff-romcode do not support this test
    test_kse3_if_nagra_tb_ena = 1;        // Signoff-romcode do not support this test

    test_kse3_aes_ena = 1;
    test_kse3_sha2_ena = 1;
    test_kse3_modarith_ena = 1;
    test_kse3_sponge_ena = 1;
    test_kse3_sha3_ena = 1;

    //disable blocks that are not used
    if(HW_DEFINES_PVE_0_CORE_NUMBER>0) pctl_disable_pve_0();
    if(HW_DEFINES_PVE_0_CORE_NUMBER>0) pctl_disable_pve_1();
    for(uint32_t aic=AI_CORE_0; aic<AI_CORE_0+HW_DEFINES_AICORE_MODULE_NUMBER; aic++) {
        pctl_disable_aicore(aic);
    }
    pctl_disable_module(DECODER_MODULE);

    // is there an hw interface test enable
    test_hw_interface = test_kse3_if_release_ena | test_kse3_if_integration_ena | test_kse3_if_nagra_tb_ena;

    // is there an applicative test enable
    test_cryptobox = test_kse3_aes_ena | test_kse3_sha2_ena | test_kse3_modarith_ena | test_kse3_sponge_ena | test_kse3_sha3_ena;


    printf("Start KSE3 test application\n");
    printf("---------------------------\n");

    int error_count = 0;
    int status;

    if (secure_ip_open()) {
        printf("ERROR openning KSE3 communication channel. Aborting\n");
        error_count++;
        goto error_quit;
    }

    /* Resetting Secure_IP */
    printf("Resetting KSE3:...");
    reset();
    printf("Done\n");

    /* Display some informations regarding the testbench */
    printf("\n");
    printf("KSE3 IP TestBench Details:\n");
    printf("- TB Expected OTP: Blank\n");
    printf( "\n");

    if (test_hw_interface) {

        printf("---------------------------\n");
        printf("Hardware interface tests:\n");
        printf("---------------------------\n");

        /* These functions can be run on release ROMcode, on any testbench */
        if (test_kse3_if_release_ena) {
            TEST(test_kse3_csr_rst);
            TEST(test_kse3_csr_access);
            TEST(test_kse3_ram_access);
            TEST(test_kse3_irq);
        }

        /* These functions requires an integragtion ROMcode implementing extra commands */
        if (test_kse3_if_integration_ena) {
            TEST(test_kse3_aor_0_7);
            TEST(test_kse3_aor_8_15);
            TEST(test_kse3_otp_write);
            TEST(test_kse3_otp_read);
            TEST(test_kse3_irom);
            TEST(test_kse3_dram_begin);
            TEST(test_kse3_dram_middle);
            TEST(test_kse3_dram_end);
            TEST(test_kse3_iram_begin);
            TEST(test_kse3_iram_middle);
            TEST(test_kse3_iram_end);
            TEST(test_kse3_iram_exec);
            TEST(test_kse3_ens);
        }

        /* Stop here if interface issues detected */
        if (error_count) {
            printf("\nAborting test sequence because some %d interface test(s) failed\n.", error_count);
            goto error_quit;
        }
    }

    /* Display some informations regarding the testbench */
    printf( "\n");
    printf("KSE3 Details:\n");
    printf("- HW_ID:    0x%08x\n", read_reg32(ADDR_HW_ID));
    printf("- NAGRA_ID: 0x%08x\n", read_reg32(ADDR_NAGRA_ID));
    printf( "\n");

    if (test_cryptobox) {

        /* Stop here if we failed to put the Secure_IP in good state for applicative tests */
        if (error_count) {
            printf("Aborting test sequence because applicative initialization failed.\n");
            goto error_quit;
        }

        printf("\n-----------------\n" \
            "Internal IPs test:\n" \
            "-----------------\n");

        TEST(test_kse3_cpu);
        TEST(test_kse3_cb_seed);

        if (test_kse3_aes_ena) {
            TEST(test_kse3_cb_aes);
        }
        if (test_kse3_sha2_ena) {
            TEST(test_kse3_cb_sha2);
        }
        if (test_kse3_modarith_ena) {
            TEST(test_kse3_cb_modarith);
        }
        if (test_kse3_sponge_ena) {
            TEST(test_kse3_cb_sponge_basic);
            TEST(test_kse3_cb_sponge_aead);
        }
        if (test_kse3_sha3_ena) {
            TEST(test_kse3_cb_sha3);
        }
    }

error_quit:

    secure_ip_close();

    if (error_count) {
        printf("SUMMARY: %d error(s) detected\n", error_count);
    }
    else {
        printf("SUMMARY: All tests are successful\n");
    }

    log_close();

    return error_count;
}


