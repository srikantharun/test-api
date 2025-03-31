// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
#include <testutils.h>
#include <decoder/decoder.h>
#include "pctl_utils.h"

int main() {
    testcase_init();

    pctl_enable_module(DECODER_MODULE);

    printf("*** test_decoder_reg_reset\r\n");

    // No MCU firmware load required as we are only reading/writing
    // configuration registers that should work without a running MCU.

    printf("reset and start timer\r\n");
    DECODER_REG_TOP->timer_control = 0b01;
    CHECK_EQUAL_INT(0b01, DECODER_REG_TOP->timer_control, "Timer control readback.");

    // check timer status (0b01 == running)
    CHECK_EQUAL_INT(0b01, DECODER_REG_TOP->timer_status, "Timer failed to run.");

    // check timer value (non-zero)
    CHECK_TRUE(DECODER_REG_TOP->timer_value > 0, "Timer value is zero.");

    printf("soft-reset the IP\r\n");
    DECODER_REG_TOP->ip_soft_reset_control = 0x1;

    // check timer registers have been reset
    CHECK_EQUAL_INT(0x0, DECODER_REG_TOP->timer_control, "Timer control register failed to reset.");
    CHECK_EQUAL_INT(0x0, DECODER_REG_TOP->timer_status, "Timer status register failed to reset.");
    CHECK_EQUAL_INT(0x0, DECODER_REG_TOP->timer_value, "Timer value register failed to reset.");

    return testcase_finalize();
}
