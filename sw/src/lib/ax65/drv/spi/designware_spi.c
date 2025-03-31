// SPDX-License-Identifier: GPL-2.0
/*
 * Designware master SPI core controller driver
 *
 * Copyright (C) 2014 Stefan Roese <sr@denx.de>
 * Copyright (C) 2020 Sean Anderson <seanga2@gmail.com>
 *
 * Very loosely based on the Linux driver:
 * drivers/spi/spi-dw.c, which is:
 * Copyright (c) 2009, Intel Corporation.
 */

#include "spi.h"
#include <stddef.h>
#include <memorymap.h>
#include <stdbool.h>
#include <uboot-includes.h>
#include <plmt/drv_plmt.h>

/* Bit fields in CTRLR0 */
/*
 * Only present when SSI_MAX_XFER_SIZE=16. This is the default, and the only
 * option before version 3.23a.
 */
#define CTRLR0_DFS_MASK			GENMASK(3, 0)

#define CTRLR0_FRF_MASK			GENMASK(5, 4)
#define CTRLR0_FRF_SPI			0x0
#define CTRLR0_FRF_SSP			0x1
#define CTRLR0_FRF_MICROWIRE		0x2
#define CTRLR0_FRF_RESV			0x3

#define CTRLR0_MODE_MASK		GENMASK(7, 6)
#define CTRLR0_MODE_SCPH		0x1
#define CTRLR0_MODE_SCPOL		0x2

#define CTRLR0_TMOD_MASK		GENMASK(9, 8)
#define	CTRLR0_TMOD_TR			0x0		/* xmit & recv */
#define CTRLR0_TMOD_TO			0x1		/* xmit only */
#define CTRLR0_TMOD_RO			0x2		/* recv only */
#define CTRLR0_TMOD_EPROMREAD		0x3		/* eeprom read mode */

#define CTRLR0_SLVOE_OFFSET		10
#define CTRLR0_SRL_OFFSET		11
#define CTRLR0_CFS_MASK			GENMASK(15, 12)

/* Only present when SSI_MAX_XFER_SIZE=32 */
#define CTRLR0_DFS_32_MASK		GENMASK(20, 16)

/* The next field is only present on versions after 4.00a */
#define CTRLR0_SPI_FRF_MASK		GENMASK(22, 21)
#define CTRLR0_SPI_FRF_BYTE		0x0
#define	CTRLR0_SPI_FRF_DUAL		0x1
#define	CTRLR0_SPI_FRF_QUAD		0x2

/* Bit fields in CTRLR0 based on DWC_ssi_databook.pdf v1.01a */
#define DWC_SSI_CTRLR0_DFS_MASK		GENMASK(4, 0)
#define DWC_SSI_CTRLR0_FRF_MASK		GENMASK(7, 6)
#define DWC_SSI_CTRLR0_MODE_MASK	GENMASK(9, 8)
#define DWC_SSI_CTRLR0_TMOD_MASK	GENMASK(11, 10)
#define DWC_SSI_CTRLR0_SRL_OFFSET	13
#define DWC_SSI_CTRLR0_SPI_FRF_MASK	GENMASK(23, 22)

/* Bit fields in SR, 7 bits */
#define SR_MASK				GENMASK(6, 0)	/* cover 7 bits */
#define SR_BUSY				BIT(0)
#define SR_TF_NOT_FULL			BIT(1)
#define SR_TF_EMPT			BIT(2)
#define SR_RF_NOT_EMPT			BIT(3)
#define SR_RF_FULL			BIT(4)
#define SR_TX_ERR			BIT(5)
#define SR_DCOL				BIT(6)

#define RX_TIMEOUT			1000		/* timeout in ms */

static inline u32 dw_read(struct dw_spi_priv *priv, u32 offset)
{
	return __raw_readl(priv->regs + offset);
}

static inline void dw_write(struct dw_spi_priv *priv, u32 offset, u32 val)
{
	__raw_writel(val, priv->regs + offset);
}

static u32 dw_spi_dw16_update_cr0(struct dw_spi_priv *priv)
{
	return FIELD_PREP(CTRLR0_DFS_MASK, priv->bits_per_word - 1)
	     | FIELD_PREP(CTRLR0_FRF_MASK, priv->type)
	     | FIELD_PREP(CTRLR0_MODE_MASK, priv->mode)
	     | FIELD_PREP(CTRLR0_TMOD_MASK, priv->tmode);
}

static u32 dw_spi_dw32_update_cr0(struct dw_spi_priv *priv)
{
	return FIELD_PREP(CTRLR0_DFS_32_MASK, priv->bits_per_word - 1)
	     | FIELD_PREP(CTRLR0_FRF_MASK, priv->type)
	     | FIELD_PREP(CTRLR0_MODE_MASK, priv->mode)
	     | FIELD_PREP(CTRLR0_TMOD_MASK, priv->tmode);
}

static u32 dw_spi_dwc_update_cr0(struct dw_spi_priv *priv)
{
	return FIELD_PREP(DWC_SSI_CTRLR0_DFS_MASK, priv->bits_per_word - 1)
	     | FIELD_PREP(DWC_SSI_CTRLR0_FRF_MASK, priv->type)
	     | FIELD_PREP(DWC_SSI_CTRLR0_MODE_MASK, priv->mode)
	     | FIELD_PREP(DWC_SSI_CTRLR0_TMOD_MASK, priv->tmode);
}

static int dw_spi_apb_init(struct dw_spi_priv *priv)
{
	/* If we read zeros from DFS, then we need to use DFS_32 instead */
	dw_write(priv, DW_SPI_SSIENR, 0);
	dw_write(priv, DW_SPI_CTRLR0, 0xffffffff);
	if (FIELD_GET(CTRLR0_DFS_MASK, dw_read(priv, DW_SPI_CTRLR0))) {
		priv->max_xfer = 16;
		priv->update_cr0 = dw_spi_dw16_update_cr0;
	} else {
		priv->max_xfer = 32;
		priv->update_cr0 = dw_spi_dw32_update_cr0;
	}

	return 0;
}

static int dw_spi_dwc_init(struct dw_spi_priv *priv)
{
	priv->max_xfer = 32;
	priv->update_cr0 = dw_spi_dwc_update_cr0;
	return 0;
}

/* Restart the controller, disable all interrupts, clean rx fifo */
static void spi_hw_init(struct dw_spi_priv *priv)
{
	dw_write(priv, DW_SPI_SSIENR, 0);
	dw_write(priv, DW_SPI_IMR, 0xff);
	dw_write(priv, DW_SPI_SSIENR, 1);

	/*
	 * Try to detect the FIFO depth if not set by interface driver,
	 * the depth could be from 2 to 256 from HW spec
	 */
	if (!priv->fifo_len) {
		u32 fifo;

		for (fifo = 1; fifo < 256; fifo++) {
			dw_write(priv, DW_SPI_TXFTLR, fifo);
			if (fifo != dw_read(priv, DW_SPI_TXFTLR))
				break;
		}

		priv->fifo_len = (fifo == 1) ? 0 : fifo;
		dw_write(priv, DW_SPI_TXFTLR, 0);
	}
	dev_dbg("fifo_len=%d\n", priv->fifo_len);
}

typedef int (*dw_spi_init_t)(struct dw_spi_priv *priv);

static int dw_spi_set_speed(struct dw_spi_priv *priv, unsigned int speed)
{
	u16 clk_div;

	/* Disable controller before writing control registers */
	dw_write(priv, DW_SPI_SSIENR, 0);

	/* clk_div doesn't support odd number */
	clk_div = priv->bus_clk_rate / speed;
	clk_div = (clk_div + 1) & 0xfffe;
	dw_write(priv, DW_SPI_BAUDR, clk_div);

	/* Enable controller after writing control registers */
	dw_write(priv, DW_SPI_SSIENR, 1);

	priv->freq = speed;
	dev_dbg("speed=%d clk_div=%d\n", priv->freq, clk_div);

	return 0;
}

static int dw_spi_set_mode(struct dw_spi_priv *priv, unsigned int mode)
{
       /*
        * Can't set mode yet. Since this depends on if rx, tx, or
        * rx & tx is requested. So we have to defer this to the
        * real transfer function.
        */
       priv->mode = mode;
       dev_dbg("mode=%d\n", priv->mode);

       return 0;
}

static int dw_spi_probe(struct dw_spi_priv *priv)
{
	MEMSET(priv, 0, sizeof(struct dw_spi_priv));
	priv->regs = (volatile void *) SOC_PERIPH_SPI_BASE;
	priv->cs = SPI_SER;
	priv->type = CTRLR0_FRF_SPI;
	priv->tx = NULL;
	priv->rx = NULL;
	priv->bus_clk_rate = SPI_BUS_CLK_RATE;
	priv->fifo_len = 0;

	/* Currently only bits_per_word == 8 supported
	 * If 16 bits_per_word should be supported, revert rx/tx reader loops
	 * back to upstream linux/uboot driver
	 */
	priv->bits_per_word = 8;
	priv->tmode = 0; /* Tx & Rx */

	if (SPI_PLAT_APB)
		dw_spi_apb_init(priv);
	else if (SPI_PLAT_DWC)
		dw_spi_dwc_init(priv);
	else
		return -1;

	dw_spi_set_speed(priv, SPI_SPEED);

	unsigned int mode = (SPI_SCPOL ? CTRLR0_MODE_SCPOL : 0) | (SPI_SCPH ? CTRLR0_MODE_SCPH : 0);
	dw_spi_set_mode(priv, mode);

	priv->version = dw_read(priv, DW_SPI_VERSION);
	dev_dbg("ssi_version_id=%c.%c%c%c ssi_max_xfer_size=%u\n",
		priv->version >> 24, priv->version >> 16, priv->version >> 8, priv->version,
		priv->max_xfer);

	/* Basic HW init */
	spi_hw_init(priv);

	return 0;
}

/* Return the max entries we can fill into tx fifo */
static inline u32 tx_max(struct dw_spi_priv *priv)
{
	u32 tx_left, tx_room, rxtx_gap;

	tx_left = priv->tx_end - priv->tx;
	tx_room = priv->fifo_len - dw_read(priv, DW_SPI_TXFLR);

	/*
	 * Another concern is about the tx/rx mismatch, we
	 * thought about using (priv->fifo_len - rxflr - txflr) as
	 * one maximum value for tx, but it doesn't cover the
	 * data which is out of tx/rx fifo and inside the
	 * shift registers. So a control from sw point of
	 * view is taken.
	 */
	rxtx_gap = ((priv->rx_end - priv->rx) - (priv->tx_end - priv->tx));

	return min3(tx_left, tx_room, (u32)(priv->fifo_len - rxtx_gap));
}


/* Return the max entries we should read out of rx fifo */
static inline u32 rx_max(struct dw_spi_priv *priv)
{
	u32 rx_left = (priv->rx_end - priv->rx);

	return min_t(u32, rx_left, dw_read(priv, DW_SPI_RXFLR));
}

static void dw_writer(struct dw_spi_priv *priv)
{
	u32 max = tx_max(priv);
	u32 txw = 0xFFFFFFFF;

	while (max--) {
		/* Set the tx word if the transfer's original "tx" is not null */
		if (priv->tx_end - priv->len)
			txw = *(u8 *)(priv->tx);
		dw_write(priv, DW_SPI_DR, txw);
		priv->tx++;
	}
}

static void dw_reader(struct dw_spi_priv *priv)
{
	u32 max = rx_max(priv);
	u16 rxw;
	while (max--) {
		rxw = dw_read(priv, DW_SPI_DR);
		/* Care about rx if the transfer's original "rx" is not null */
		if (priv->rx_end - priv->len)
			*(u8 *)(priv->rx) = rxw;
		priv->rx++;
	}
}

static int poll_transfer(struct dw_spi_priv *priv)
{
	do {
		dw_writer(priv);
		dw_reader(priv);
	} while (priv->rx_end > priv->rx);

	return 0;
}

static int dw_spi_xfer(struct dw_spi_priv *priv, unsigned int bitlen,
		       const void *dout, void *din, unsigned long flags)
{
  UNUSED(flags);
	const u8 *tx = dout;
	u8 *rx = din;
	int ret = 0;
	u32 cr0 = 0;
	u32 val;

	/* spi core configured to do 8 bit transfers */
	if (bitlen % 8) {
		// dev_err(dev, "Non byte aligned SPI transfer.\n");
		return -1;
	}

	if (rx && tx)
		priv->tmode = CTRLR0_TMOD_TR;
	else if (rx)
		priv->tmode = CTRLR0_TMOD_RO;
	else
		/*
		 * In transmit only mode (CTRL0_TMOD_TO) input FIFO never gets
		 * any data which breaks our logic in poll_transfer() above.
		 */
		priv->tmode = CTRLR0_TMOD_TR;

	cr0 = priv->update_cr0(priv);

	priv->len = bitlen >> 3;

	priv->tx = (void *)tx;
	priv->tx_end = priv->tx + priv->len;
	priv->rx = rx;
	priv->rx_end = priv->rx + priv->len;

	/* Disable controller before writing control registers */
	dw_write(priv, DW_SPI_SSIENR, 0);

	dev_dbg("cr0=%08x rx=%p tx=%p len=%d [bytes]\n", cr0, rx, tx, priv->len);
	/* Reprogram cr0 only if changed */
	if (dw_read(priv, DW_SPI_CTRLR0) != cr0)
		dw_write(priv, DW_SPI_CTRLR0, cr0);

	/*
	 * Configure the desired SS (slave select 0...3) in the controller
	 * The DW SPI controller will activate and deactivate this CS
	 * automatically. So no cs_activate() etc is needed in this driver.
	 */
	dw_write(priv, DW_SPI_SER, 1 << priv->cs);

	/* Enable controller after writing control registers */
	dw_write(priv, DW_SPI_SSIENR, 1);

	/* Start transfer in a polling loop */
	ret = poll_transfer(priv);

	/*
	 * Wait for current transmit operation to complete.
	 * Otherwise if some data still exists in Tx FIFO it can be
	 * silently flushed, i.e. dropped on disabling of the controller,
	 * which happens when writing 0 to DW_SPI_SSIENR which happens
	 * in the beginning of new transfer.
	 */
	for (;;) {
		val = dw_read(priv, DW_SPI_SR);
		if ((val & SR_TF_EMPT) && !(val & SR_BUSY))
			break;
	}

	return ret;
}

/*
 * This function is necessary for reading SPI flash with the native CS
 * c.f. https://lkml.org/lkml/2015/12/23/132
 */
static int dw_spi_exec_op(struct dw_spi_priv *priv, const struct spi_mem_op *op)
{
	bool read = op->data.dir == SPI_MEM_DATA_IN;
	int pos, i, ret = 0;

	u8 op_len = op->cmd.nbytes + op->addr.nbytes + op->dummy.nbytes;
	u8 op_buf[op_len];
	u32 cr0;

	if (read)
		priv->tmode = CTRLR0_TMOD_EPROMREAD;
	else
		priv->tmode = CTRLR0_TMOD_TO;

	cr0 = priv->update_cr0(priv);

	dev_dbg("cr0=%08x buf=%p len=%u [bytes]\n", cr0, op->data.buf.in, op->data.nbytes);

	dw_write(priv, DW_SPI_SSIENR, 0);
	dw_write(priv, DW_SPI_CTRLR0, cr0);
	if (read)
		dw_write(priv, DW_SPI_CTRLR1, op->data.nbytes - 1);

	dw_write(priv, DW_SPI_SSIENR, 1);

	/* From spi_mem_exec_op */
	pos = 0;
	op_buf[pos++] = op->cmd.opcode;
	if (op->addr.nbytes) {
		for (i = 0; i < op->addr.nbytes; i++)
			op_buf[pos + i] = op->addr.val >>
				(8 * (op->addr.nbytes - i - 1));

		pos += op->addr.nbytes;
	}
	if (op->dummy.nbytes) {
		MEMSET(op_buf + pos, 0xff, op->dummy.nbytes);
	}

	priv->tx = &op_buf;
	priv->tx_end = priv->tx + op_len;
	priv->rx = NULL;
	priv->rx_end = NULL;

	while (priv->tx != priv->tx_end)
		dw_writer(priv);

	/*
	 * XXX: The following are tight loops! Enabling debug messages may cause
	 * them to fail because we are not reading/writing the fifo fast enough.
	 */
	if (read) {
		/* If we have gotten any data back yet */
		bool got_data = false;
		/* How many times we have looped without reading anything */
		int loops_since_read = 0;
		struct spi_mem_op *mut_op = (struct spi_mem_op *)op;

		priv->rx = op->data.buf.in;
		priv->rx_end = priv->rx + op->data.nbytes;

		dw_write(priv, DW_SPI_SER, 1 << priv->cs);
		while (priv->rx != priv->rx_end) {
			void *last_rx = priv->rx;

			dw_reader(priv);
			if (priv->rx == last_rx) {
				loops_since_read++;
				/* Thresholds are arbitrary */
				if (loops_since_read > 256)
					break;
				else if (got_data && loops_since_read > 32)
					break;
			} else {
				got_data = true;
				loops_since_read = 0;
			}
		}
		/* Update with the actual amount of data read */
		mut_op->data.nbytes -= priv->rx_end - priv->rx;
	} else {
		u32 val;

		priv->tx = op->data.buf.out;
		priv->tx_end = priv->tx + op->data.nbytes;

		/* Fill up the write fifo before starting the transfer */
		dw_writer(priv);
		dw_write(priv, DW_SPI_SER, 1 << priv->cs);
		while (priv->tx != priv->tx_end)
			dw_writer(priv);

		for (;;) {
			val = dw_read(priv, DW_SPI_SR);
			if ((val & SR_TF_EMPT) && !(val & SR_BUSY))
				break;
		}
	}

	dw_write(priv, DW_SPI_SER, 0);

	dev_dbg("%u bytes xfered\n", op->data.nbytes);
	return ret;
}

/* The size of ctrl1 limits data transfers to 64K */
static int dw_spi_adjust_op_size(struct spi_mem_op *op)
{
	op->data.nbytes = min(op->data.nbytes, (unsigned int) 0x00010000); // SZ_64K

	return 0;
}

static const struct spi_controller_mem_ops dw_spi_mem_ops = {
	.exec_op = dw_spi_exec_op,
	.adjust_op_size = dw_spi_adjust_op_size,
};

const struct dm_spi_ops drv_spi0_ops = {
	.probe          = dw_spi_probe,
	.xfer		= dw_spi_xfer,
	.mem_ops	= &dw_spi_mem_ops,
	.set_speed	= dw_spi_set_speed,
	.set_mode	= dw_spi_set_mode,
};

void spiUnprotectedRead(struct dw_spi_priv *priv) {
  dw_read(priv, DW_SPI_DR);
  return;
}

void spiTxEmpty(struct dw_spi_priv *priv) {
	/* Disbale any pending SLAVE communciton */
	dw_write(priv, DW_SPI_SSIENR, 0);
	dw_write(priv, DW_SPI_SER, 0);

    /* For testing purrpose, set TX FIFO threshold to 2 */
    dw_write(priv, DW_SPI_TXFTLR, 2);

	dw_write(priv, DW_SPI_SSIENR, 1);
	return;
}

void spiTxOverflow(struct dw_spi_priv *priv) {
	/* Disbale any pending SLAVE communciton */
	dw_write(priv, DW_SPI_SSIENR, 0);
	dw_write(priv, DW_SPI_SER, 0);

    /* For testing purrpose, set TX FIFO threshold to 2 */
    dw_write(priv, DW_SPI_TXFTLR, 2);

    dw_write(priv, DW_SPI_SSIENR, 1);

	dw_write(priv, DW_SPI_DR, 0);
	dw_write(priv, DW_SPI_DR, 1);
	dw_write(priv, DW_SPI_DR, 2);
	dw_write(priv, DW_SPI_DR, 3);
	dw_write(priv, DW_SPI_DR, 4);
	dw_write(priv, DW_SPI_DR, 5);
	dw_write(priv, DW_SPI_DR, 6);
	dw_write(priv, DW_SPI_DR, 7);
	dw_write(priv, DW_SPI_DR, 8);

	return;
}

void spiFillRxBuffer(struct dw_spi_priv *priv, int num_bytes) {
	u32 bitlen = num_bytes * 8; // send 3 bytes to trigger RX buffer full

	u8 data_out[16] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
	u8 data_in[16] = {0};
	const u8 *tx = data_out;
	u8 *rx = data_in;

	u32 cr0 = 0;

	u32 tx_sequence_len;
	u32 tx_word;


	priv->tmode = CTRLR0_TMOD_TR;
	cr0 = priv->update_cr0(priv);
	cr0 |= (1 << 11); // Enable debug loopback from TX FIFO to RX FIFO

	priv->len = bitlen >> 3;

	priv->tx = (void *)tx;
	priv->tx_end = priv->tx + priv->len;
	priv->rx = rx;
	priv->rx_end = priv->rx + priv->len;

	/* Disable controller before writing control registers */
	dw_write(priv, DW_SPI_SSIENR, 0);

    /* For testing purrpose, set the RX FICO threshold to 2 */
    dw_write(priv, DW_SPI_RXFTLR, 2);

	/* Reprogram cr0 only if changed */
	if (dw_read(priv, DW_SPI_CTRLR0) != cr0)
		dw_write(priv, DW_SPI_CTRLR0, cr0);

	/*
	 * Configure the desired SS (slave select 0...3) in the controller
	 * The DW SPI controller will activate and deactivate this CS
	 * automatically. So no cs_activate() etc is needed in this driver.
	 */
	dw_write(priv, DW_SPI_SER, 1 << priv->cs);

	/* Enable controller after writing control registers */
	dw_write(priv, DW_SPI_SSIENR, 1);

	tx_sequence_len = priv->len;
	tx_word = 0xFFFFFFFF;

	/* Start transfer in a loop */
	while (tx_sequence_len--) {
		/* Set the tx word if the transfer's original "tx" is not null */
		if (priv->tx_end - priv->len)
			tx_word = *(u8 *)(priv->tx);
		dw_write(priv, DW_SPI_DR, tx_word);
		priv->tx++;
	}

	return;
}

void spiEnableIsr(struct dw_spi_priv *priv, enum spi_interrupts intr) {
    // enable single interrupt on SPI
    u32 reg = dw_read(priv, DW_SPI_IMR);
    reg |= intr;
    dw_write(priv, DW_SPI_IMR, reg);
}

void spiDisableIsr(struct dw_spi_priv *priv, enum spi_interrupts intr) {
	dw_write(priv, DW_SPI_IMR, 0);
	u32 reg = dw_read(priv, DW_SPI_IMR);
	reg &= ~intr;
    	dw_write(priv, DW_SPI_IMR, reg);
}

// Override spi handler
void spi_irq_handler(void) {
  volatile u32* ptr = (u32*) (SOC_PERIPH_SPI_BASE + DW_SPI_ICR);
  *ptr; // clear the interrupt
}

u32 spiGetInterruptStatus(struct dw_spi_priv *priv) {
	return dw_read(priv, DW_SPI_ISR);
}

void spiSetEnable(struct dw_spi_priv *priv, bool enable) {
	u32 value = enable ? 1 : 0;
	dw_write(priv,DW_SPI_SSIENR, value);
}

u16 spiReadRxBuf(struct dw_spi_priv *priv) {
	return (u16)dw_read(priv, DW_SPI_DR);
}

