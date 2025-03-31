// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
#include <printf.h>
#include <testutils.h>
#include "pctl_utils.h"
#include <dw_timer/drv_dw_timer.h>
#include <timer.h>

// testbench emulation
#include <decoder/decoder_testcase.h>
// testcase data
extern struct decoder_testcase testcase;

void timer0_irq_handler() {
  timerDisable(0);
  timerClearIsr(0);

  printf("timer 0 irq triggered\n");
}


int main() {
    testcase_init();

    pctl_enable_module(DECODER_MODULE);

    CHECK_TRUE(decoder_testcase_execute(&testcase), "testcase execution failed");

    return testcase_finalize();
}
