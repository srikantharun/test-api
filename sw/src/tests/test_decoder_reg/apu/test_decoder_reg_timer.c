// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
#include <testutils.h>
#include <timer.h>
#include <decoder/decoder.h>
#include "pctl_utils.h"

int main() {
    testcase_init();

    pctl_enable_module(DECODER_MODULE);

    printf("*** test_decoder_reg_timer\r\n");

    // No MCU firmware load required as we are only reading/writing
    // configuration registers that should work without a running MCU.

    // This test uses the timer (REG_TOP_012-REG_TOP_014) to check whether
    // read/write interaction with the decoder IP's registers is possible.

    printf("reset and start timer\r\n");
    DECODER_REG_TOP->timer_control = 0b01;
    CHECK_EQUAL_INT(0b01, DECODER_REG_TOP->timer_control, "Timer control readback.");

    // check timer status (0b01 == running)
    CHECK_EQUAL_INT(0b01, DECODER_REG_TOP->timer_status, "Timer failed to run.");

    // check timer value is increasing
    uint32_t first_timer_value = DECODER_REG_TOP->timer_value;
    uint32_t second_timer_value = DECODER_REG_TOP->timer_value;
    CHECK_TRUE(second_timer_value > first_timer_value, "Timer value failed to increase.");

    printf("pause timer\r\n");
    DECODER_REG_TOP->timer_control = 0b10;
    CHECK_EQUAL_INT(0b10, DECODER_REG_TOP->timer_control, "Timer control readback.");

    // check timer status (0b10 == paused)
    CHECK_EQUAL_INT(0b10, DECODER_REG_TOP->timer_status, "Timer failed to pause.");

    // check timer value is stable
    first_timer_value = DECODER_REG_TOP->timer_value;
    udelay(1);
    second_timer_value = DECODER_REG_TOP->timer_value;
    CHECK_TRUE(first_timer_value == second_timer_value, "Timer failed to paused - timer value is unstable.");

    printf("restart timer\r\n");
    DECODER_REG_TOP->timer_control = 0b11;
    CHECK_EQUAL_INT(0b11, DECODER_REG_TOP->timer_control, "Timer control readback.");

    // check timer status (0b01 == running)
    CHECK_EQUAL_INT(0b01, DECODER_REG_TOP->timer_status, "Timer failed to restart.");

    // check timer value is increasing
    first_timer_value = DECODER_REG_TOP->timer_value;
    second_timer_value = DECODER_REG_TOP->timer_value;
    CHECK_TRUE(second_timer_value > first_timer_value, "Timer value failed to increase.");

    printf("reset and stop timer\r\n");
    DECODER_REG_TOP->timer_control = 0b00;
    CHECK_EQUAL_INT(0b00, DECODER_REG_TOP->timer_control, "Timer control readback.");

    // check timer status (0b00 == idle)
    CHECK_EQUAL_INT(0b00, DECODER_REG_TOP->timer_status, "Timer state is differs form idle state.");

    // check timer value
    CHECK_EQUAL_INT(0x0, DECODER_REG_TOP->timer_value, "Timer value failed to reset.");

    return testcase_finalize();
}
