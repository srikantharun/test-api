// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2014 Freescale Semiconductor, Inc.
 * Synced from Linux v4.19
 */

#ifndef __LINUX_MTD_SPI_NOR_H
#define __LINUX_MTD_SPI_NOR_H

#include <uboot-includes.h>
#include <spi/spi.h>
#include <stdbool.h>
#include <util.h>

/*
 * Manufacturer IDs
 *
 * The first byte returned from the flash after sending opcode SPINOR_OP_RDID.
 * Sometimes these are the same as CFI IDs, but sometimes they aren't.
 */
#define CFI_MFR_AMD		0x0001
#define CFI_MFR_AMIC		0x0037
#define CFI_MFR_ATMEL		0x001F
#define CFI_MFR_EON		0x001C
#define CFI_MFR_FUJITSU		0x0004
#define CFI_MFR_HYUNDAI		0x00AD
#define CFI_MFR_INTEL		0x0089
#define CFI_MFR_MACRONIX	0x00C2
#define CFI_MFR_NEC		0x0010
#define CFI_MFR_PMC		0x009D
#define CFI_MFR_SAMSUNG		0x00EC
#define CFI_MFR_SHARP		0x00B0
#define CFI_MFR_SST		0x00BF
#define CFI_MFR_ST		0x0020 /* STMicroelectronics */
#define CFI_MFR_MICRON		0x002C	/* Micron */
#define CFI_MFR_TOSHIBA		0x0098
#define CFI_MFR_WINBOND		0x00DA

#define SNOR_MFR_ATMEL		CFI_MFR_ATMEL
#define SNOR_MFR_GIGADEVICE	0xc8
#define SNOR_MFR_INTEL		CFI_MFR_INTEL
#define SNOR_MFR_ST		CFI_MFR_ST /* ST Micro <--> Micron */
#define SNOR_MFR_MICRON		CFI_MFR_MICRON /* ST Micro <--> Micron */
#define SNOR_MFR_ISSI		CFI_MFR_PMC
#define SNOR_MFR_MACRONIX	CFI_MFR_MACRONIX
#define SNOR_MFR_SPANSION	CFI_MFR_AMD
#define SNOR_MFR_SST		CFI_MFR_SST
#define SNOR_MFR_WINBOND	0xef /* Also used by some Spansion */
#define SNOR_MFR_CYPRESS	0x34

/*
 * Note on opcode nomenclature: some opcodes have a format like
 * SPINOR_OP_FUNCTION{4,}_x_y_z. The numbers x, y, and z stand for the number
 * of I/O lines used for the opcode, address, and data (respectively). The
 * FUNCTION has an optional suffix of '4', to represent an opcode which
 * requires a 4-byte (32-bit) address.
 */

/* Flash opcodes. */
#define SPINOR_OP_WREN		0x06	/* Write enable */
#define SPINOR_OP_RDSR		0x05	/* Read status register */
#define SPINOR_OP_WRSR		0x01	/* Write status register 1 byte */
#define SPINOR_OP_RDSR2		0x3f	/* Read status register 2 */
#define SPINOR_OP_WRSR2		0x3e	/* Write status register 2 */
#define SPINOR_OP_READ		0x03	/* Read data bytes (low frequency) */
#define SPINOR_OP_READ_FAST	0x0b	/* Read data bytes (high frequency) */
#define SPINOR_OP_READ_1_1_2	0x3b	/* Read data bytes (Dual Output SPI) */
#define SPINOR_OP_READ_1_2_2	0xbb	/* Read data bytes (Dual I/O SPI) */
#define SPINOR_OP_READ_1_1_4	0x6b	/* Read data bytes (Quad Output SPI) */
#define SPINOR_OP_READ_1_4_4	0xeb	/* Read data bytes (Quad I/O SPI) */
#define SPINOR_OP_READ_1_1_8	0x8b	/* Read data bytes (Octal Output SPI) */
#define SPINOR_OP_READ_1_8_8	0xcb	/* Read data bytes (Octal I/O SPI) */
#define SPINOR_OP_PP		0x02	/* Page program (up to 256 bytes) */
#define SPINOR_OP_PP_1_1_4	0x32	/* Quad page program */
#define SPINOR_OP_PP_1_4_4	0x38	/* Quad page program */
#define SPINOR_OP_PP_1_1_8	0x82	/* Octal page program */
#define SPINOR_OP_PP_1_8_8	0xc2	/* Octal page program */
#define SPINOR_OP_BE_4K		0x20	/* Erase 4KiB block */
#define SPINOR_OP_BE_4K_PMC	0xd7	/* Erase 4KiB block on PMC chips */
#define SPINOR_OP_BE_32K	0x52	/* Erase 32KiB block */
#define SPINOR_OP_CHIP_ERASE	0xc7	/* Erase whole flash chip */
#define SPINOR_OP_SE		0xd8	/* Sector erase (usually 64KiB) */
#define SPINOR_OP_RDID		0x9f	/* Read JEDEC ID */
#define SPINOR_OP_RDSFDP	0x5a	/* Read SFDP */
#define SPINOR_OP_RDCR		0x35	/* Read configuration register */
#define SPINOR_OP_RDFSR		0x70	/* Read flag status register */
#define SPINOR_OP_CLFSR		0x50	/* Clear flag status register */
#define SPINOR_OP_RDEAR		0xc8	/* Read Extended Address Register */
#define SPINOR_OP_WREAR		0xc5	/* Write Extended Address Register */
#define SPINOR_OP_SRSTEN	0x66	/* Software Reset Enable */
#define SPINOR_OP_SRST		0x99	/* Software Reset */

/* 4-byte address opcodes - used on Spansion and some Macronix flashes. */
#define SPINOR_OP_READ_4B	0x13	/* Read data bytes (low frequency) */
#define SPINOR_OP_READ_FAST_4B	0x0c	/* Read data bytes (high frequency) */
#define SPINOR_OP_READ_1_1_2_4B	0x3c	/* Read data bytes (Dual Output SPI) */
#define SPINOR_OP_READ_1_2_2_4B	0xbc	/* Read data bytes (Dual I/O SPI) */
#define SPINOR_OP_READ_1_1_4_4B	0x6c	/* Read data bytes (Quad Output SPI) */
#define SPINOR_OP_READ_1_4_4_4B	0xec	/* Read data bytes (Quad I/O SPI) */
#define SPINOR_OP_READ_1_1_8_4B	0x7c	/* Read data bytes (Octal Output SPI) */
#define SPINOR_OP_READ_1_8_8_4B	0xcc	/* Read data bytes (Octal I/O SPI) */
#define SPINOR_OP_PP_4B		0x12	/* Page program (up to 256 bytes) */
#define SPINOR_OP_PP_1_1_4_4B	0x34	/* Quad page program */
#define SPINOR_OP_PP_1_4_4_4B	0x3e	/* Quad page program */
#define SPINOR_OP_PP_1_1_8_4B	0x84	/* Octal page program */
#define SPINOR_OP_PP_1_8_8_4B	0x8e	/* Octal page program */
#define SPINOR_OP_BE_4K_4B	0x21	/* Erase 4KiB block */
#define SPINOR_OP_BE_32K_4B	0x5c	/* Erase 32KiB block */
#define SPINOR_OP_SE_4B		0xdc	/* Sector erase (usually 64KiB) */

/* Double Transfer Rate opcodes - defined in JEDEC JESD216B. */
#define SPINOR_OP_READ_1_1_1_DTR	0x0d
#define SPINOR_OP_READ_1_2_2_DTR	0xbd
#define SPINOR_OP_READ_1_4_4_DTR	0xed

#define SPINOR_OP_READ_1_1_1_DTR_4B	0x0e
#define SPINOR_OP_READ_1_2_2_DTR_4B	0xbe
#define SPINOR_OP_READ_1_4_4_DTR_4B	0xee

/* Used for SST flashes only. */
#define SPINOR_OP_BP		0x02	/* Byte program */
#define SPINOR_OP_WRDI		0x04	/* Write disable */
#define SPINOR_OP_AAI_WP	0xad	/* Auto address increment word program */

/* Used for SST26* flashes only. */
#define SPINOR_OP_READ_BPR	0x72	/* Read block protection register */
#define SPINOR_OP_WRITE_BPR	0x42	/* Write block protection register */

/* Used for S3AN flashes only */
#define SPINOR_OP_XSE		0x50	/* Sector erase */
#define SPINOR_OP_XPP		0x82	/* Page program */
#define SPINOR_OP_XRDSR		0xd7	/* Read status register */

#define XSR_PAGESIZE		BIT(0)	/* Page size in Po2 or Linear */
#define XSR_RDY			BIT(7)	/* Ready */

/* Used for Macronix and Winbond flashes. */
#define SPINOR_OP_EN4B		0xb7	/* Enter 4-byte mode */
#define SPINOR_OP_EX4B		0xe9	/* Exit 4-byte mode */

/* Used for Spansion flashes only. */
#define SPINOR_OP_BRWR		0x17	/* Bank register write */
#define SPINOR_OP_BRRD		0x16	/* Bank register read */
#define SPINOR_OP_CLSR		0x30	/* Clear status register 1 */
#define SPINOR_OP_EX4B_CYPRESS	0xB8	/* Exit 4-byte mode */
#define SPINOR_OP_RDAR		0x65	/* Read any register */
#define SPINOR_OP_WRAR		0x71	/* Write any register */
#define SPINOR_REG_ADDR_STR1V	0x00800000
#define SPINOR_REG_ADDR_CFR1V	0x00800002
#define SPINOR_REG_ADDR_CFR3V	0x00800004
#define CFR3V_UNHYSA		BIT(3)	/* Uniform sectors or not */
#define CFR3V_PGMBUF		BIT(4)	/* Program buffer size */

/* Used for Micron flashes only. */
#define SPINOR_OP_RD_EVCR	0x65	/* Read EVCR register */
#define SPINOR_OP_WD_EVCR	0x61	/* Write EVCR register */
#define SPINOR_OP_MT_DTR_RD	0xfd	/* Fast Read opcode in DTR mode */
#define SPINOR_OP_MT_RD_ANY_REG	0x85	/* Read volatile register */
#define SPINOR_OP_MT_WR_ANY_REG	0x81	/* Write volatile register */
#define SPINOR_REG_MT_CFR0V	0x00	/* For setting octal DTR mode */
#define SPINOR_REG_MT_CFR1V	0x01	/* For setting dummy cycles */
#define SPINOR_MT_OCT_DTR	0xe7	/* Enable Octal DTR with DQS. */

/* Status Register bits. */
#define SR_WIP			BIT(0)	/* Write in progress */
#define SR_WEL			BIT(1)	/* Write enable latch */
/* meaning of other SR_* bits may differ between vendors */
#define SR_BP0			BIT(2)	/* Block protect 0 */
#define SR_BP1			BIT(3)	/* Block protect 1 */
#define SR_BP2			BIT(4)	/* Block protect 2 */
#define SR_TB			BIT(5)	/* Top/Bottom protect */
#define SR_SRWD			BIT(7)	/* SR write protect */
/* Spansion/Cypress specific status bits */
#define SR_E_ERR		BIT(5)
#define SR_P_ERR		BIT(6)

#define SR_QUAD_EN_MX		BIT(6)	/* Macronix Quad I/O */

/* Enhanced Volatile Configuration Register bits */
#define EVCR_QUAD_EN_MICRON	BIT(7)	/* Micron Quad I/O */

/* Flag Status Register bits */
#define FSR_READY		BIT(7)	/* Device status, 0 = Busy, 1 = Ready */
#define FSR_E_ERR		BIT(5)	/* Erase operation status */
#define FSR_P_ERR		BIT(4)	/* Program operation status */
#define FSR_PT_ERR		BIT(1)	/* Protection error bit */

/* Configuration Register bits. */
#define CR_QUAD_EN_SPAN		BIT(1)	/* Spansion Quad I/O */

/* Status Register 2 bits. */
#define SR2_QUAD_EN_BIT7	BIT(7)

/* For Cypress flash. */
#define SPINOR_OP_RD_ANY_REG			0x65	/* Read any register */
#define SPINOR_OP_WR_ANY_REG			0x71	/* Write any register */
#define SPINOR_OP_S28_SE_4K			0x21
#define SPINOR_REG_CYPRESS_CFR2V		0x00800003
#define SPINOR_REG_CYPRESS_CFR2V_MEMLAT_11_24	0xb
#define SPINOR_REG_CYPRESS_CFR3V		0x00800004
#define SPINOR_REG_CYPRESS_CFR3V_PGSZ		BIT(4) /* Page size. */
#define SPINOR_REG_CYPRESS_CFR3V_UNISECT	BIT(3) /* Uniform sector mode */
#define SPINOR_REG_CYPRESS_CFR5V		0x00800006
#define SPINOR_REG_CYPRESS_CFR5V_OCT_DTR_EN	0x3
#define SPINOR_OP_CYPRESS_RD_FAST		0xee

/* Supported SPI protocols */
#define SNOR_PROTO_INST_MASK	GENMASK(23, 16)
#define SNOR_PROTO_INST_SHIFT	16
#define SNOR_PROTO_INST(_nbits)	\
	((((unsigned long)(_nbits)) << SNOR_PROTO_INST_SHIFT) & \
	 SNOR_PROTO_INST_MASK)

#define SNOR_PROTO_ADDR_MASK	GENMASK(15, 8)
#define SNOR_PROTO_ADDR_SHIFT	8
#define SNOR_PROTO_ADDR(_nbits)	\
	((((unsigned long)(_nbits)) << SNOR_PROTO_ADDR_SHIFT) & \
	 SNOR_PROTO_ADDR_MASK)

#define SNOR_PROTO_DATA_MASK	GENMASK(7, 0)
#define SNOR_PROTO_DATA_SHIFT	0
#define SNOR_PROTO_DATA(_nbits)	\
	((((unsigned long)(_nbits)) << SNOR_PROTO_DATA_SHIFT) & \
	 SNOR_PROTO_DATA_MASK)

#define SNOR_PROTO_IS_DTR	BIT(24)	/* Double Transfer Rate */

#define SNOR_PROTO_STR(_inst_nbits, _addr_nbits, _data_nbits)	\
	(SNOR_PROTO_INST(_inst_nbits) |				\
	 SNOR_PROTO_ADDR(_addr_nbits) |				\
	 SNOR_PROTO_DATA(_data_nbits))
#define SNOR_PROTO_DTR(_inst_nbits, _addr_nbits, _data_nbits)	\
	(SNOR_PROTO_IS_DTR |					\
	 SNOR_PROTO_STR(_inst_nbits, _addr_nbits, _data_nbits))

enum spi_nor_protocol {
	SNOR_PROTO_1_1_1 = SNOR_PROTO_STR(1, 1, 1),
	SNOR_PROTO_1_1_2 = SNOR_PROTO_STR(1, 1, 2),
	SNOR_PROTO_1_1_4 = SNOR_PROTO_STR(1, 1, 4),
	SNOR_PROTO_1_1_8 = SNOR_PROTO_STR(1, 1, 8),
	SNOR_PROTO_1_2_2 = SNOR_PROTO_STR(1, 2, 2),
	SNOR_PROTO_1_4_4 = SNOR_PROTO_STR(1, 4, 4),
	SNOR_PROTO_1_8_8 = SNOR_PROTO_STR(1, 8, 8),
	SNOR_PROTO_2_2_2 = SNOR_PROTO_STR(2, 2, 2),
	SNOR_PROTO_4_4_4 = SNOR_PROTO_STR(4, 4, 4),
	SNOR_PROTO_8_8_8 = SNOR_PROTO_STR(8, 8, 8),

	SNOR_PROTO_1_1_1_DTR = SNOR_PROTO_DTR(1, 1, 1),
	SNOR_PROTO_1_2_2_DTR = SNOR_PROTO_DTR(1, 2, 2),
	SNOR_PROTO_1_4_4_DTR = SNOR_PROTO_DTR(1, 4, 4),
	SNOR_PROTO_1_8_8_DTR = SNOR_PROTO_DTR(1, 8, 8),
	SNOR_PROTO_8_8_8_DTR = SNOR_PROTO_DTR(8, 8, 8),
};

#define SPI_NOR_MAX_CMD_SIZE	8
enum spi_nor_ops {
	SPI_NOR_OPS_READ = 0,
	SPI_NOR_OPS_WRITE,
	SPI_NOR_OPS_ERASE,
	SPI_NOR_OPS_LOCK,
	SPI_NOR_OPS_UNLOCK,
};

enum spi_nor_option_flags {
	SNOR_F_USE_FSR		= BIT(0),
	SNOR_F_HAS_SR_TB	= BIT(1),
	SNOR_F_NO_OP_CHIP_ERASE	= BIT(2),
	SNOR_F_S3AN_ADDR_DEFAULT = BIT(3),
	SNOR_F_READY_XSR_RDY	= BIT(4),
	SNOR_F_USE_CLSR		= BIT(5),
	SNOR_F_BROKEN_RESET	= BIT(6),
	SNOR_F_SOFT_RESET	= BIT(7),
};

struct spi_nor;

#define SPI_NOR_MAX_ID_LEN	6
#define SPI_NOR_MAX_ADDR_WIDTH	4

#define JEDEC_MFR(info)	((info)->id[0])
#define JEDEC_ID(info)		(((info)->id[1]) << 8 | ((info)->id[2]))

/**
 * struct spi_nor - Structure for defining a the SPI NOR layer
 * reduced down to required fields
 * @ops:		spi controller ops
 * @info:		spi-nor part JDEC MFR id and other info
 * @addr_width:		number of address bytes
 * @read_opcode:	the read opcode
 * @read_dummy:		the dummy needed by the read operation
 * @flags:		flag options for the current SPI-NOR (SNOR_F_*)
 * @read_proto:		the SPI protocol for read operations
 * @write_proto:	the SPI protocol for write operations
 * @reg_proto:		the SPI protocol for read_reg/write_reg/erase operations
 * @cmd_buf:		used by the write_reg
 * @priv:		spi controller private data
 * @bitbang:		read flash bytewise
 */
struct spi_nor {
	const struct dm_spi_ops *ops;
	const struct flash_info	*info;
	uint8_t			addr_width;
	uint8_t			read_opcode;
	uint8_t			read_dummy;
	enum spi_nor_protocol	read_proto;
	enum spi_nor_protocol	write_proto;
	enum spi_nor_protocol	reg_proto;
	uint32_t			flags;
	uint8_t			cmd_buf[SPI_NOR_MAX_CMD_SIZE];
	struct dw_spi_priv *priv;
	uint32_t size;
	bool bitbang;
};

/**
 * spi_nor_setup_peripheral() - scan the SPI NOR
 * @ops:        the spi peripheral ops structure
 * @priv:       the spi peripheral priv structure
 * @nor:	the spi_nor structure
 * @bitbang:    read flash bytewise instead of in bulk
 *
 * The drivers can use this function to setup the underlying peripheral
 * This allows initial communication and prepares the driver to call spi_nor_scan next
 * fills the ops{} and the priv{}.
 *
 */
void spi_nor_setup_peripheral(const struct dm_spi_ops *ops, struct dw_spi_priv *priv, struct spi_nor *nor, bool bitbang);

/**
 * spi_nor_read_reg() - Read a register from the SPI NOR.
 *
 * @nor: Pointer to the struct spi_nor representing the SPI NOR flash device.
 * @code: The opcode to send for the read register command.
 * @val: Pointer to store the read register value.
 * @len: The length of the register value to read.
 *
 * This function reads a register from the SPI NOR flash memory using the
 * specified opcode. The read register value is stored in the 'val' buffer.
 *
 * Return: 0 on success, negative error code on failure.
 */
int spi_nor_read_reg(struct spi_nor *nor, u8 code, u8 *val, int len);

/**
 * spi_nor_read_reg_from_address() - Read data from a specific address in SPI NOR.
 *
 * @nor: Pointer to the struct spi_nor representing the SPI NOR flash device.
 * @code: The opcode to send for the read command.
 * @val: Pointer to store the read data.
 * @len: Length of the data to read.
 * @start_address: Start address in SPI NOR to begin reading from.
 *
 * This function reads data from a specific address in the SPI NOR flash memory
 * using the specified opcode. The read data is stored in the 'val' buffer.
 *
 * Return: 0 on success, negative error code on failure.
 */
int spi_nor_read_reg_from_address(struct spi_nor *nor, uint8_t code, uint8_t *val, int len, uint32_t start_address);

#endif
