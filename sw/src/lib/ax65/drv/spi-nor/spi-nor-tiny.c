// SPDX-License-Identifier: GPL-2.0
/*
 * Based on m25p80.c, by Mike Lavender (mike@steroidmicros.com), with
 * influence from lart.c (Abraham Van Der Merwe) and mtd_dataflash.c
 *
 * Copyright (C) 2005, Intec Automation Inc.
 * Copyright (C) 2014, Freescale Semiconductor, Inc.
 *
 * Synced from Linux v4.19
 */
#include "spi-nor.h"
#include <platform.h>

/* Define max times to check status register before we give up. */

/*
 * For everything but full-chip erase; probably could be much smaller, but kept
 * around for safety for now
 */

#define HZ					CONFIG_SYS_HZ

#define DEFAULT_READY_WAIT_JIFFIES		(40UL * HZ)

/**
 * spi_mem_exec_op() - Execute a memory operation
 * @slave: the SPI device
 * @op: the memory operation to execute
 *
 * Executes a memory operation.
 *
 * This function first checks that @op is supported and then tries to execute
 * it.
 *
 * Return: 0 in case of success, a negative error code otherwise.
 */

static int spi_mem_exec_op(struct spi_nor *nor, const struct spi_mem_op *op) 
{
    const struct dm_spi_ops *ops = nor->ops;

    if (ops->mem_ops && ops->mem_ops->exec_op) {
        int ret = ops->mem_ops->exec_op(nor->priv, op);
        if (ret == 0 || ret == -ENOTSUPP) {
            return ret;
        }
        return ret;  // Return the error code directly
    }

    return 0;  // Return success if no memory-specific ops available
}

static int spi_nor_read_write_reg(struct spi_nor *nor, struct spi_mem_op
		*op, void *buf)
{
	if (op->data.dir == SPI_MEM_DATA_IN)
		op->data.buf.in = buf;
	else
		op->data.buf.out = buf;
	return spi_mem_exec_op(nor, op);
}

int spi_nor_read_reg(struct spi_nor *nor, uint8_t code, uint8_t *val, int len)
{
	struct spi_mem_op op = SPI_MEM_OP(SPI_MEM_OP_CMD(code, 1),
					  SPI_MEM_OP_NO_ADDR,
					  SPI_MEM_OP_NO_DUMMY,
					  SPI_MEM_OP_DATA_IN(len, NULL, 1));
	int ret;

	ret = spi_nor_read_write_reg(nor, &op, val);

	return ret;
}

int spi_nor_read_reg_from_address(struct spi_nor *nor, uint8_t code, uint8_t *val, int len, uint32_t start_address)
{
    struct spi_mem_op op = SPI_MEM_OP(SPI_MEM_OP_CMD(code, 1),
                                      SPI_MEM_OP_ADDR(3, start_address, 3), // Specify the start address
                                      SPI_MEM_OP_NO_DUMMY,
                                      SPI_MEM_OP_DATA_IN(len, NULL, 1));
    int ret;

    ret = spi_nor_read_write_reg(nor, &op, val);

    return ret;
}

void spi_nor_setup_peripheral(const struct dm_spi_ops *ops, struct dw_spi_priv *priv, struct spi_nor *nor, bool bitbang)
{
	nor->priv = priv;
	nor->ops = ops;
	nor->bitbang = bitbang;
}
