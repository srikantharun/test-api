/* SPDX-License-Identifier: GPL-2.0+ */
/*
 * Copyright (C) 2009 Sergey Kubushyn <ksi@koi8.net>
 * Copyright (C) 2009 - 2013 Heiko Schocher <hs@denx.de>
 * Changes for multibus/multiadapter I2C support.
 *
 * (C) Copyright 2001
 * Gerald Van Baren, Custom IDEAS, vanbaren@cideas.com.
 *
 * The original I2C interface was
 *   (C) 2000 by Paolo Scaffardi (arsenio@tin.it)
 *   AIRVENT SAM s.p.a - RIMINI(ITALY)
 * but has been changed substantially.
 */

#ifndef _I2C_H_
#define _I2C_H_

#include <uboot-includes.h>

/*
 * For now there are essentially two parts to this file - driver model
 * here at the top, and the older code below (with CONFIG_SYS_I2C_LEGACY being
 * most recent). The plan is to migrate everything to driver model.
 * The driver model structures and API are separate as they are different
 * enough as to be incompatible for compilation purposes.
 */

/** enum i2c_speed_mode - standard I2C speed modes */
enum i2c_speed_mode {
	IC_SPEED_MODE_STANDARD,
	IC_SPEED_MODE_FAST,
	IC_SPEED_MODE_FAST_PLUS,
	IC_SPEED_MODE_HIGH,
	IC_SPEED_MODE_FAST_ULTRA,

	IC_SPEED_MODE_COUNT,
};

/** enum i2c_speed_rate - standard I2C speeds in Hz */
enum i2c_speed_rate {
	I2C_SPEED_STANDARD_RATE		= 100000,
	I2C_SPEED_FAST_RATE		= 400000,
	I2C_SPEED_FAST_PLUS_RATE	= 1000000,
	I2C_SPEED_HIGH_RATE		= 3400000,
	I2C_SPEED_FAST_ULTRA_RATE	= 5000000,
};

/*
 * Not all of these flags are implemented in the U-Boot API
 */
enum dm_i2c_msg_flags {
	I2C_M_TEN		= 0x0010, /* ten-bit chip address */
	I2C_M_RD		= 0x0001, /* read data, from slave to master */
	I2C_M_STOP		= 0x8000, /* send stop after this message */
	I2C_M_NOSTART		= 0x4000, /* no start before this message */
	I2C_M_REV_DIR_ADDR	= 0x2000, /* invert polarity of R/W bit */
	I2C_M_IGNORE_NAK	= 0x1000, /* continue after NAK */
	I2C_M_NO_RD_ACK		= 0x0800, /* skip the Ack bit on reads */
	I2C_M_RECV_LEN		= 0x0400, /* length is first received byte */
};

/**
 * struct i2c_msg - an I2C message
 *
 * @addr:	Slave address
 * @flags:	Flags (see enum dm_i2c_msg_flags)
 * @len:	Length of buffer in bytes, may be 0 for a probe
 * @buf:	Buffer to send/receive, or NULL if no data
 */
struct i2c_msg {
	unsigned int addr;
	unsigned int flags;
	unsigned int len;
	u8 *buf;
};

#endif	/* _I2C_H_ */
