// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <testutils.h>

#ifdef UART

#include <platform.h>
#include <encoding.h>
#include <stdbool.h>
#include <critical_section.h>
#include <printf.h>
#include <uart/drv_uart.h>
#include <interrupt.h>

static volatile bool uart_triggered = false;

void verify_interrupt(unsigned int irq_source) {
  if (irq_source == IRQ_SOC_PERIPH_UART_SOURCE) {
    uart_triggered = true;
  }
}

/**
 * Test UART interrupt handling.
 * This test enables UART interrupts and sends character 'A'.
 * If the interrupt is correctly handled and the flag is set, the test passes.
 *
 * Returns:
 *    TEST_SUCCESS if the interrupt was triggered;
 *    TEST_FAILURE otherwise.
 */
int test_uart_irq() {
  char send_ch;

  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  setup_irq_uart();  // Setup UART interrupt

  /* Enable interrupts in general. */
  arch_irq_unlock(key);

  /* Write character */
  send_ch = 'A';
  writeSerial(send_ch);

  /* \n */
  send_ch = 0x0A;
  writeSerial(send_ch);

  return (uart_triggered ? TEST_SUCCESS : TEST_FAILURE);
}

/**
 * Test basic UART send and receive functionality.
 * This test sends characters from 'A' to 'G' and for each, expects the same
 * character to be sent back manually through terminal.
 *
 * Returns:
 *    TEST_SUCCESS if all characters are received back correctly;
 *    TEST_FAILURE otherwise.
 */
int test_uart() {
  char send_ch;

  /* Write characters and read response */
  for (char i = 'A'; i <= 'G'; i++) {
      send_ch = i;
      writeSerial(send_ch);

      /* Wait for manual response */
      char input_ch;
      input_ch = readSerial();

      if (send_ch != input_ch) {
          return TEST_FAILURE;
      }
  }

  /* \n */
  send_ch = 0x0A;
  writeSerial(send_ch);

  return TEST_SUCCESS;
}

int main() {
  /*
  * NOTICE: all printfs are disabled in this test as they lead to weird behaviour
  *         since the uart is tested here. If any prints are done in the start
  *         procedure that test might brake
  */
  testcase_init();

  /* START TEST */
  CHECK_TRUE(test_uart() == TEST_SUCCESS, "MANUAL FAILED\n");
  CHECK_TRUE(test_uart_irq() == TEST_SUCCESS, "INTERRUPT FAILED\n");
  /* END TEST */

  return testcase_finalize();
}

#else

int main(){
  printf("[TEST FAILED] The UART test ran with the incorrect flavor configuration.\n");
  return TEST_FAILURE;
}
#endif /* UART */
