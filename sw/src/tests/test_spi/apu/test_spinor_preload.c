#include <spi/spi.h>
#include <spi-nor/spi-nor.h>
#include <testutils.h>

#define FLASH_BITBANG 1

/* Test to check SPI's read operation */
int test_spinor_preload(){

  /* grab a ref to the spi driver */
  const struct dm_spi_ops *ops = &drv_spi0_ops;
  struct dw_spi_priv priv;
  CHECK_TRUE(ops->probe(&priv) >= 0); // set speed and mode

  struct spi_nor nor;
  // Set up spi_nor for testing. Primarily, nor->ops holds driver ops. nor->priv and nor->bitbang, unused here,
  // might be useful in the future. This function prepaares the driver for NOR flash communication via ops.
  spi_nor_setup_peripheral(ops, &priv, &nor, FLASH_BITBANG);

  // Read the JEDEC ID
  uint8_t id[SPI_NOR_MAX_ID_LEN];
  int tmp = spi_nor_read_reg(&nor, SPINOR_OP_RDID, id, SPI_NOR_MAX_ID_LEN);

  if(tmp < 0) {
    printf("Error %d reading JEDEC ID\n", tmp);
    return TEST_FAILURE;
  }

  // Verify JEDEC ID values
  CHECK_EQUAL_HEX(0x01, id[0]);
  CHECK_EQUAL_HEX(0x02, id[1]);
  CHECK_EQUAL_HEX(0x20, id[2]);

  // Read backdoor injected data into adress 0x0000002
  uint8_t data[4];
  uint32_t start_address = 0x0000002;
  int ret = spi_nor_read_reg_from_address(&nor, SPINOR_OP_READ, data, 4, start_address);

  if(ret < 0){
    printf("Error reading data");
    return TEST_FAILURE;
  }

  // Verify the injected data values
  CHECK_EQUAL_HEX(0xaa, data[0]);
  CHECK_EQUAL_HEX(0xbb, data[1]);
  CHECK_EQUAL_HEX(0xcc, data[2]);
  CHECK_EQUAL_HEX(0xdd, data[3]);

  return 0;
}
int main (void) {
  testcase_init();

  CHECK_TRUE(TEST_SUCCESS == test_spinor_preload());

  return testcase_finalize();
}
