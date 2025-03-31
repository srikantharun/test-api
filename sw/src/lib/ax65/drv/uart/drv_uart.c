#include "drv_uart.h"
#include <encoding.h>
#include <interrupt.h>
#include <memorymap.h>
#include <platform.h>
#include <std/std_bit.h>

// Get a uint32_t bit
#define UART_LSR_TEMT STD_BIT32(6) // Indicates whether UART FIFO is empty
#define UART_LSR_DR 0X01 // Indicates whether receiver FIFO contains data
#define UART_IER_DISABLE_ISR 0x00 // Disable all interrupts
#define UART_IER_PTIME                                                         \
  STD_BIT32(7) // THRE Interrupt is not implemented in Triton chip
#define UART_IER_EDSSI STD_BIT32(3) // Modem Status Interrupt
#define UART_IER_ELSI STD_BIT32(2)  // Receiver Line Status Interrupt
#define UART_IER_ETBEI STD_BIT32(1) // Transmit Holding Register Empty Interrupt
#define UART_IER_ERBFI STD_BIT32(0) // Received Data Available
#define UART_IER_ENABLE_ALL_ISR                                                \
  (UART_IER_EDSSI | UART_IER_ELSI | UART_IER_ETBEI | UART_IER_ERBFI)

#define UART_LCR_DLAB_ENABLE STD_BIT32(7) // Enable DLAB (set baud rate divisor)
#define UART_LCR_DEFAULT_MODE 0x03        // 8 bits, no parity, one stop bit
#define UART_IIR_IID 0xF                  // Interrup ID field
#define UART_FCR_FIFO_DEFAULT                                                  \
  0xC7 // Enable FIFO, clear them, with 14-byte threshold
#define UART_FCR_XFIFOR STD_BIT32(2)   // Trasnmit FIFO reset (write 1 to clear)
#define UART_MCR_AUTOFLOW_ENABLE 0x20  // Enable autoflow control
#define UART_MCR_AUTOFLOW_DISABLE 0x00 // Disable autoflow control
#define UART_USR_BUSY 0x1              // Busy field

typedef struct {
  volatile uint32_t RBR_THR_DLL;   // 0x000
  volatile uint32_t IER_DLH;       // 0x004
  volatile uint32_t IIR_FCR;       // 0x008
  volatile uint32_t LCR;           // 0x00c
  volatile uint32_t MCR;           // 0x010
  volatile uint32_t LSR;           // 0x014
  volatile uint32_t MSR;           // 0x018
  volatile uint32_t reserved1[24]; // 0x01c
  volatile uint32_t USR;           // 0x07c
} HalUartReg;

//! the pointer to the PVT register file
#define pUART ((HalUartReg *)(SOC_PERIPH_UART_BASE))

static int isTransmitEmpty() { return pUART->LSR & UART_LSR_TEMT; }

static int isDataReceptionReady() { return pUART->LSR & UART_LSR_DR; }

// Overrides the default uart handler
void uart_irq_handler(void) {
  uint8_t iid = pUART->IIR_FCR & UART_IIR_IID;
  if (iid == 0x7) { // busy detect handler
    UNUSED(pUART->USR);
  }
  if (iid == 0xc) { // character timeout handler
    // Read some data to unset the interrupt
    UNUSED(readSerial());
  }
}

void setup_irq_uart(void) {
#ifndef NO_INTERRUPTS
  HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_UART_SOURCE, IRQ_PRIORITY_DEFAULT);
  HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_UART_SOURCE);
#endif

  while (pUART->USR & UART_USR_BUSY) { /*busy loop until UART is idle*/
  }
  pUART->LCR &= ~UART_LCR_DLAB_ENABLE; // Clear DLAB
  pUART->IER_DLH = UART_IER_ERBFI;

#ifndef NO_INTERRUPTS
  /* Enable external interrupts */
  HAL_MEIP_ENABLE();
#endif
}

void writeSerial(char a) {
  while (!isTransmitEmpty()) {
  };
  // Write to THR reg. Precond: DLAB bit (LCR[7]) is cleared
  pUART->RBR_THR_DLL = a;
}

char readSerial() {
  while (!isDataReceptionReady()) {
  };
  // Read from RBR reg. Precond: DLAB bit (LCR[7]) is cleared
  return pUART->RBR_THR_DLL;
}

void init_uart(uint32_t freq, uint32_t baud) {
  // round to nearest integer to get minimal baud error
  uint32_t divisor = (freq + (baud << 3)) / (baud << 4);

#ifndef PLATFORM_QEMU
  /*busy loop until UART is idle*/
  while (pUART->USR & UART_USR_BUSY) {
    // do a mask into the UART_FCR_FIFO_DEFAULT with transmit fifo bit equal
    // to 0 to transmit everything with this we maintain the default
    // configurations and flush only the RX fifo to make sure that we don't
    // get stuck in the busy loop
    pUART->IIR_FCR = (UART_FCR_FIFO_DEFAULT & (~UART_FCR_XFIFOR));
  }
#endif // PLATFORM_QEMU

  pUART->IER_DLH = UART_IER_DISABLE_ISR;
  pUART->LCR = UART_LCR_DLAB_ENABLE;
  pUART->RBR_THR_DLL = divisor;           // divisor (lo byte)
  pUART->IER_DLH = (divisor >> 8) & 0xFF; // divisor (hi byte)
  pUART->LCR = UART_LCR_DEFAULT_MODE;     // 8 bits, no parity, one stop bit
  pUART->IIR_FCR =
      UART_FCR_FIFO_DEFAULT; // Enable FIFO, clear them, with 14-byte threshold
  pUART->MCR = UART_MCR_AUTOFLOW_DISABLE;
}

void put_buf(const char *str, const uint32_t buflen) {
  for (uint32_t i = 0; i < buflen; i++) {
    writeSerial((uint8_t)str[i]);
  }
}
