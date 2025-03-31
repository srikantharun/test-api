// UART tests
//
// test_uart_txrx:
//
// 1. Configure UART to 115200 baud, 8 bits, parity even, no stop bit
// 2. Enable RX data available IRQ
// 3. Start a full-duplex transfer of 16 bytes
// 4. Wait for UVM to signal the end of the transfer
// 5. Dequeue data logged by UVM and compare it to data sent/received

#include <printf.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <uart/drv_uart.h>
#include <uvm_ipc/uvm_sw_ipc.h>

#define UART_FIFO_DEPTH 16

const char tx_char[UART_FIFO_DEPTH] = {0xca, 0xfe, 0xde, 0xca, 0xde, 0xad,
                                       0xbe, 0xef, 0xf0, 0x0d, 0xba, 0xbe,
                                       0xd0, 0xd0, 0xca, 0xca};

const char *wire_uart_int = "spike_top_tb.th.uart_int";

void test_uart_txrx() {
  uint64_t uvm_tx_data;
  uint64_t uvm_rx_data;
  char rx_data;

  init_uart(100000000, 115200);
  setup_irq_uart();
  printf("Initialized UART \n");

  // Indicate to UVM how many chars we which to send
  uvm_sw_ipc_push_data(0u, UART_FIFO_DEPTH);
  uvm_sw_ipc_gen_event(0u);

  // Send transaction
  for (int i = 0; i < UART_FIFO_DEPTH; i++) {
    writeSerial(tx_char[i]);
  }

  // Wait for transfer to complete
  uvm_sw_ipc_wait_event(0u);

  printf("Transfer done!\n");

  // Read data received and verify that it matches
  for (int i = 0; i < UART_FIFO_DEPTH; i++) {
    uint64_t int_value = uvm_sw_ipc_hdl_read(wire_uart_int);

    // There is a 14-byte interrupt theshold.
    // A soon as the FIFO drops below this level, interrupt is cleared
    if ((UART_FIFO_DEPTH - i) >= 14)
      CHECK_EQUAL_INT(1u, int_value);
    else {
      CHECK_EQUAL_INT(0u, int_value);
    }

    rx_data = readSerial();

    ASSERT(uvm_sw_ipc_pull_data(0u, &uvm_tx_data));
    ASSERT(uvm_sw_ipc_pull_data(1u, &uvm_rx_data));

    CHECK_EQUAL_HEX((uint64_t)tx_char[i], uvm_rx_data);
    CHECK_EQUAL_HEX(uvm_tx_data, (uint64_t)rx_data);
  }
}

int main() {
  testcase_init();
  test_uart_txrx();

  return testcase_finalize();
}
