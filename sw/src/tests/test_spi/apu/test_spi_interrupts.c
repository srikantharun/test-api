#include <encoding.h>
#include <nds_csr.h>
#include <platform.h>
#include <printf.h>
#include <spi/spi.h>
#include <stdbool.h>
#include <testutils.h>
#include <timer.h>
#include <critical_section.h>
#include <interrupt.h>
#include <memorymap.h>
#include <logging.h>

static volatile bool interrupt_triggered = false;
static uint32_t expected_interrupt = 0u;

static const struct dm_spi_ops *ops = &drv_spi0_ops;
static struct dw_spi_priv priv;

/* Handler to verify if the interrupt was triggered */
void verify_interrupt(unsigned int irq_source) {
  u32 irq_status;

  if (irq_source != IRQ_SOC_PERIPH_SPI_SOURCE) {
    return;
  }

  irq_status = spiGetInterruptStatus(&priv);

  LOG_DEBUG("IRQ triggered=%u\n", irq_status);

  if (irq_status & expected_interrupt) {
    interrupt_triggered = true;
  }

  if (irq_status & SPI_TXE) {
    // Mask interrupt to not get caught up in an interrupt loop.
    // It's impossible to clear out the TXE interrupt.
    spiDisableIsr(&priv, SPI_TXE);
  }

  if (irq_status & SPI_RXF) {
    // clear the interrupt by reading 4 bytes form the RX buffer
    (void)spiReadRxBuf(&priv);
    (void)spiReadRxBuf(&priv);
  }
}

static int testSPI_isr_RXU() {
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  interrupt_triggered = false;
  expected_interrupt = SPI_RXU;

  spiEnableIsr(&priv, SPI_RXU);
  spiUnprotectedRead(&priv);

  arch_irq_unlock(key);

  // Wait for the interrupt to trigger
  udelay(15);
  spiDisableIsr(&priv, SPI_RXU);

  return interrupt_triggered ? TEST_SUCCESS : TEST_FAILURE;
}

static int testSPI_isr_TXE() {
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  interrupt_triggered = false;
  expected_interrupt = SPI_TXE;

  spiEnableIsr(&priv, SPI_TXE);
  spiTxEmpty(&priv);

  arch_irq_unlock(key);

  // Wait for the interrupt to trigger
  udelay(15);
  spiDisableIsr(&priv, SPI_TXE);

  return interrupt_triggered ? TEST_SUCCESS : TEST_FAILURE;
}

static int testSPI_isr_TXO() {
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  interrupt_triggered = false;
  expected_interrupt = SPI_TXO;

  spiEnableIsr(&priv, SPI_TXO);

  spiTxOverflow(&priv);

  arch_irq_unlock(key);

  // Wait for the interrupt to trigger
  udelay(15);
  spiDisableIsr(&priv, SPI_TXO);

  return interrupt_triggered ? TEST_SUCCESS : TEST_FAILURE;
}

static int testSPI_isr_RXF() {
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  interrupt_triggered = false;
  expected_interrupt = SPI_RXF;

  spiEnableIsr(&priv, SPI_RXF);
  spiFillRxBuffer(&priv, 4);

  arch_irq_unlock(key);

  // Wait for the interrupt to trigger
  udelay(15);
  spiDisableIsr(&priv, SPI_RXF);

  return interrupt_triggered ? TEST_SUCCESS : TEST_FAILURE;
}

static int testSPI_isr_RXO() {
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  interrupt_triggered = false;
  expected_interrupt = SPI_RXO;

  spiEnableIsr(&priv, SPI_RXO);
  spiFillRxBuffer(&priv, 16);

  arch_irq_unlock(key);

  // Wait for the interrupt to trigger
  udelay(15);
  spiDisableIsr(&priv, SPI_RXO);

  return interrupt_triggered ? TEST_SUCCESS : TEST_FAILURE;
}

int main() {
  int ret;

  testcase_init();

  ops->probe(&priv);
  spiDisableIsr(&priv,
                (SPI_TXE | SPI_TXO | SPI_RXU | SPI_RXO | SPI_RXF | SPI_MSTI));
  HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_SPI_SOURCE);
  HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_SPI_SOURCE, IRQ_PRIORITY_DEFAULT);

  /* START TEST */
  printf("Starting testSPI_isr_TXE\n");
  ret = testSPI_isr_TXE();
  CHECK_TRUE(ret == TEST_SUCCESS);

  printf("Starting testSPI_isr_TXO\n");
  ret = testSPI_isr_TXO();
  CHECK_TRUE(ret == TEST_SUCCESS);

  printf("Starting testSPI_isr_RXU\n");
  ret = testSPI_isr_RXU();
  CHECK_TRUE(ret == TEST_SUCCESS);

  printf("Starting testSPI_isr_RXO\n");
  ret = testSPI_isr_RXO();
  CHECK_TRUE(ret == TEST_SUCCESS);

  printf("Starting testSPI_isr_RXF\n");
  ret = testSPI_isr_RXF();
  CHECK_TRUE(ret == TEST_SUCCESS);

  HAL_INTERRUPT_DISABLE(IRQ_SOC_PERIPH_SPI_SOURCE);

  /* END TEST */
  return testcase_finalize();
}
