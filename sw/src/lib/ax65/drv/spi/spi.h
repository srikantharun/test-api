#pragma once

#include <uboot-includes.h>
#include <stdbool.h>
#include <std/std_bit.h>

/* include/spi.h */

/* SPI mode flags */
#define SPI_CPHA	BIT(0)	/* clock phase (1 = SPI_CLOCK_PHASE_SECOND) */
#define SPI_CPOL	BIT(1)	/* clock polarity (1 = SPI_POLARITY_HIGH) */
#define SPI_MODE_0	(0|0)			/* (original MicroWire) */
#define SPI_MODE_1	(0|SPI_CPHA)
#define SPI_MODE_2	(SPI_CPOL|0)
#define SPI_MODE_3	(SPI_CPOL|SPI_CPHA)
#define SPI_CS_HIGH	BIT(2)			/* CS active high */
#define SPI_LSB_FIRST	BIT(3)			/* per-word bits-on-wire */
#define SPI_3WIRE	BIT(4)			/* SI/SO signals shared */
#define SPI_LOOP	BIT(5)			/* loopback mode */
#define SPI_SLAVE	BIT(6)			/* slave mode */
#define SPI_PREAMBLE	BIT(7)			/* Skip preamble bytes */
#define SPI_TX_BYTE	BIT(8)			/* transmit with 1 wire byte */
#define SPI_TX_DUAL	BIT(9)			/* transmit with 2 wires */
#define SPI_TX_QUAD	BIT(10)			/* transmit with 4 wires */
#define SPI_RX_SLOW	BIT(11)			/* receive with 1 wire slow */
#define SPI_RX_DUAL	BIT(12)			/* receive with 2 wires */
#define SPI_RX_QUAD	BIT(13)			/* receive with 4 wires */
#define SPI_TX_OCTAL	BIT(14)			/* transmit with 8 wires */
#define SPI_RX_OCTAL	BIT(15)			/* receive with 8 wires */

/* Register offsets */
#define DW_SPI_CTRLR0			0x00
#define DW_SPI_CTRLR1			0x04
#define DW_SPI_SSIENR			0x08
#define DW_SPI_MWCR			0x0c
#define DW_SPI_SER			0x10
#define DW_SPI_BAUDR			0x14
#define DW_SPI_TXFTLR			0x18
#define DW_SPI_RXFTLR			0x1c
#define DW_SPI_TXFLR			0x20
#define DW_SPI_RXFLR			0x24
#define DW_SPI_SR			0x28
#define DW_SPI_IMR			0x2c
#define DW_SPI_ISR			0x30
#define DW_SPI_RISR			0x34
#define DW_SPI_TXOICR			0x38
#define DW_SPI_RXOICR			0x3c
#define DW_SPI_RXUICR			0x40
#define DW_SPI_MSTICR			0x44
#define DW_SPI_ICR			0x48
#define DW_SPI_DMACR			0x4c
#define DW_SPI_DMATDLR			0x50
#define DW_SPI_DMARDLR			0x54
#define DW_SPI_IDR			0x58
#define DW_SPI_VERSION			0x5c
#define DW_SPI_DR			0x60

/* include/spi-mem.h */
#define SPI_MEM_OP_CMD(__opcode, __buswidth)			\
	{							\
		.buswidth = __buswidth,				\
		.opcode = __opcode,				\
		.nbytes = 1,					\
	}

#define SPI_MEM_OP_ADDR(__nbytes, __val, __buswidth)		\
	{							\
		.nbytes = __nbytes,				\
		.val = __val,					\
		.buswidth = __buswidth,				\
	}

#define SPI_MEM_OP_NO_ADDR	{ }

#define SPI_MEM_OP_DUMMY(__nbytes, __buswidth)			\
	{							\
		.nbytes = __nbytes,				\
		.buswidth = __buswidth,				\
	}

#define SPI_MEM_OP_NO_DUMMY	{ }

#define SPI_MEM_OP_DATA_IN(__nbytes, __buf, __buswidth)		\
	{							\
		.dir = SPI_MEM_DATA_IN,				\
		.nbytes = __nbytes,				\
		.buf.in = __buf,				\
		.buswidth = __buswidth,				\
	}

#define SPI_MEM_OP_DATA_OUT(__nbytes, __buf, __buswidth)	\
	{							\
		.dir = SPI_MEM_DATA_OUT,			\
		.nbytes = __nbytes,				\
		.buf.out = __buf,				\
		.buswidth = __buswidth,				\
	}

#define SPI_MEM_OP_NO_DATA	{ }

/**
 * enum spi_mem_data_dir - describes the direction of a SPI memory data
 *			   transfer from the controller perspective
 * @SPI_MEM_NO_DATA: no data transferred
 * @SPI_MEM_DATA_IN: data coming from the SPI memory
 * @SPI_MEM_DATA_OUT: data sent the SPI memory
 */
enum spi_mem_data_dir {
	SPI_MEM_NO_DATA,
	SPI_MEM_DATA_IN,
	SPI_MEM_DATA_OUT,
};
 struct spi_mem_op {
	struct {
		u8 nbytes;
		u8 buswidth;
		u8 dtr : 1;
		u16 opcode;
	} cmd;

	struct {
		u8 nbytes;
		u8 buswidth;
		u8 dtr : 1;
		u64 val;
	} addr;

	struct {
		u8 nbytes;
		u8 buswidth;
		u8 dtr : 1;
	} dummy;

	struct {
		u8 buswidth;
		u8 dtr : 1;
		enum spi_mem_data_dir dir;
		unsigned int nbytes;
		/* buf.{in,out} must be DMA-able. */
		union {
			void *in;
			const void *out;
		} buf;
	} data;
};

#define SPI_MEM_OP(__cmd, __addr, __dummy, __data)		\
	{							\
		.cmd = __cmd,					\
		.addr = __addr,					\
		.dummy = __dummy,				\
		.data = __data,					\
	}

#define SPI_XFER_BEGIN		BIT(0)	/* Assert CS before transfer */
#define SPI_XFER_END		BIT(1)	/* Deassert CS after transfer */
#define SPI_XFER_ONCE		(SPI_XFER_BEGIN | SPI_XFER_END)

struct dw_spi_priv {
	/* struct clk clk; */
	/* struct reset_ctl_bulk resets; */
	/* struct gpio_desc cs_gpio;	 External chip-select gpio */

	u32 (*update_cr0)(struct dw_spi_priv *priv);

	volatile void *regs;
	unsigned long bus_clk_rate;
	unsigned int freq;		/* Default frequency */
	unsigned int mode;

	const void *tx;
	const void *tx_end;
	void *rx;
	void *rx_end;
	u32 fifo_len;			/* depth of the FIFO buffer */
	u32 max_xfer;			/* Maximum transfer size (in bits) */

	int bits_per_word;
	int len;
	u8 cs;				/* chip select pin */
	u8 tmode;			/* TR/TO/RO/EEPROM */
	u8 type;			/* SPI/SSP/MicroWire */
	int version;
};


struct spi_controller_mem_ops {
	int (*adjust_op_size)(struct spi_mem_op *op);
	int (*exec_op)(struct dw_spi_priv *priv, const struct spi_mem_op *op);
};


/**
 * struct struct dm_spi_ops - Driver model SPI operations
 * externally visible
 */
struct dm_spi_ops {
    int (*probe)(struct dw_spi_priv *priv);
	int (*xfer)(struct dw_spi_priv *priv, unsigned int bitlen, const void *dout,
		    void *din, unsigned long flags);
	const struct spi_controller_mem_ops *mem_ops;
	int (*set_speed)(struct dw_spi_priv *priv, unsigned int hz);
	int (*set_mode)(struct dw_spi_priv *priv, unsigned int mode);
};

// Const struct to access spi utilities
extern const struct dm_spi_ops drv_spi0_ops;

/**
 * enum spi_interrupts: all  types of SPI interrupts
 * /!\ Each interrupt value corresponds to mask inside the ISR register
 */
enum spi_interrupts {
	SPI_TXE = STD_BIT32(0),
	SPI_TXO = STD_BIT32(1),
	SPI_RXU = STD_BIT32(2),
	SPI_RXO = STD_BIT32(3),
	SPI_RXF = STD_BIT32(4),
	SPI_MSTI = STD_BIT32(5)
} ;

void spiSetEnable(struct dw_spi_priv *priv, bool enable);

void spiUnprotectedRead(struct dw_spi_priv *priv);
void spiTxEmpty(struct dw_spi_priv *priv);
void spiTxOverflow(struct dw_spi_priv *priv);

void spiFillRxBuffer(struct dw_spi_priv *priv, int num_bytes);
void spiEnableIsr(struct dw_spi_priv *priv, enum spi_interrupts intr);
void spiDisableIsr(struct dw_spi_priv *priv, enum spi_interrupts intr);

u32 spiGetInterruptStatus(struct dw_spi_priv *priv);
u16 spiReadRxBuf(struct dw_spi_priv *priv);
