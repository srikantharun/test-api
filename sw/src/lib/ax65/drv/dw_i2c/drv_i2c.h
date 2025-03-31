/* SPDX-License-Identifier: GPL-2.0+ */
/*
 * (C) Copyright 2009
 * Vipin Kumar, ST Micoelectronics, vipin.kumar@st.com.
 */

#ifndef __DW_I2C_H_
#define __DW_I2C_H_

#include <uboot-includes.h>
#include "i2c.h"
#include <stdbool.h>
#include <stdint.h>

struct i2c_regs {
    u32 ic_con;       // 0x00 - I2C Control Register
    u32 ic_tar;       // 0x04 - I2C Target Address Register
    u32 ic_sar;       // 0x08 - I2C Slave Address Register
    u32 ic_hs_maddr;  // 0x0c - I2C High Speed Master Mode Code Address Register
    u32 ic_cmd_data;  // 0x10 - I2C Rx/Tx Data Buffer and Command Register

    u32 ic_ss_scl_hcnt;  // 0x14 - Standard Speed I2C Clock SCL High Count Register
    u32 ic_ss_scl_lcnt;  // 0x18 - Standard Speed I2C Clock SCL Low Count Register
    u32 ic_fs_scl_hcnt;  // 0x1c - Fast Mode or Fast Mode Plus I2C Clock SCL High Count Register
    u32 ic_fs_scl_lcnt;  // 0x20 - Fast Mode or Fast Mode Plus I2C Clock SCL Low Count Register
    u32 ic_hs_scl_hcnt;  // 0x24 - High Speed I2C Clock SCL High Count Register
    u32 ic_hs_scl_lcnt;  // 0x28 - High Speed I2C Clock SCL Low Count Register

    u32 ic_intr_stat;      // 0x2c - I2C Interrupt Status Register
    u32 ic_intr_mask;      // 0x30 - I2C Interrupt Mask Register
    u32 ic_raw_intr_stat;  // 0x34 - I2C Raw Interrupt Status Register
    u32 ic_rx_tl;          // 0x38 - I2C Receive FIFO Threshold Register
    u32 ic_tx_tl;          // 0x3c - I2C Transmit FIFO Threshold Register

    u32 ic_clr_intr;       // 0x40 - Clear Combined and Individual Interrupt Register
    u32 ic_clr_rx_under;   // 0x44 - Clear RX_UNDER Interrupt Register
    u32 ic_clr_rx_over;    // 0x48 - Clear RX_OVER Interrupt Register
    u32 ic_clr_tx_over;    // 0x4c - Clear TX_OVER Interrupt Register
    u32 ic_clr_rd_req;     // 0x50 - Clear RD_REQ Interrupt Register
    u32 ic_clr_tx_abrt;    // 0x54 - Clear TX_ABRT Interrupt Register
    u32 ic_clr_rx_done;    // 0x58 - Clear RX_DONE Interrupt Register
    u32 ic_clr_activity;   // 0x5c - Clear ACTIVITY Interrupt Register
    u32 ic_clr_stop_det;   // 0x60 - Clear STOP_DET Interrupt Register
    u32 ic_clr_start_det;  // 0x64 - Clear START_DET Interrupt Register
    u32 ic_clr_gen_call;   // 0x68 - Clear GEN_CALL Interrupt Register

    u32 ic_enable;  // 0x6c - I2C ENABLE Register
    u32 ic_status;  // 0x70 - I2C STATUS Register
    u32 ic_txflr;   // 0x74 - I2C Transmit FIFO Level Register
    u32 ic_rxflr;   // 0x78 - I2C Receive FIFO Level Register

    u32 ic_sda_hold;           // 0x7c - I2C SDA Hold Time Length Register
    u32 ic_tx_abrt_source;     // 0x80 - I2C Transmit Abort Source Register
    u32 slv_data_nak_only;     // 0x84 - Generate Slave Data NACK Register
    u32 dma_cr;                // 0x88 - DMA Control Register
    u32 dma_tdlr;              // 0x8c - DMA Transmit Data Level Register
    u32 dma_rdlr;              // 0x90 - DMA Receive Data Level Register
    u32 sda_setup;             // 0x94 - I2C SDA Setup Register
    u32 ack_general_call;      // 0x98 - I2C ACK General Call Register
    u32 ic_enable_status;      // 0x9c - I2C Enable Status Register
    u32 fs_spklen;             // 0xa0 - I2C SS, FS or FM+ spike suppression limit
    u32 hs_spklen;             // 0xa4 - I2C HS spike suppression limit register
    u32 clr_restart_det;       // 0xa8 - Clear RESTART_DET Interrupt Register
    u8 reserved[0xf4 - 0xac];  // Till 0xF0
    u32 comp_param1;           // 0xf4 - Component Parameter Register 1
    u32 comp_version;          // 0xf8 - I2C Component Version Register
    u32 comp_type;             // 0xfc - I2C Component Type Register
};

#define IC_CLK          166666666
#define NANO_TO_KILO    1000000

/* High and low times in different speed modes (in ns) */
#define MIN_SS_SCL_HIGHTIME 4000
#define MIN_SS_SCL_LOWTIME  4700
#define MIN_FS_SCL_HIGHTIME 600
#define MIN_FS_SCL_LOWTIME  1300
#define MIN_FP_SCL_HIGHTIME 260
#define MIN_FP_SCL_LOWTIME  500
#define MIN_HS_SCL_HIGHTIME 60
#define MIN_HS_SCL_LOWTIME  160

/* Worst case timeout for 1 byte is kept as 2ms */
#define CONFIG_SYS_HZ   1000
#define I2C_BYTE_TO     (CONFIG_SYS_HZ/500)
#define I2C_STOPDET_TO  (CONFIG_SYS_HZ/500)
#define I2C_BYTE_TO_BB  (I2C_BYTE_TO * 16)

/* i2c control register definitions */
#define IC_CON_SD       0x0040
#define IC_CON_RE       0x0020
#define IC_CON_10BITADDRMASTER  0x0010
#define IC_CON_10BITADDR_SLAVE  0x0008
#define IC_CON_SPD_MSK      0x0006
#define IC_CON_SPD_SS       0x0002
#define IC_CON_SPD_FS       0x0004
#define IC_CON_SPD_HS       0x0006
#define IC_CON_MM           0x0001

/* i2c target address register definitions */
#define TAR_ADDR        0x0050

/* i2c slave address register definitions */
#define IC_SLAVE_ADDR   0x0002

/* i2c data buffer and command register definitions */
#define IC_CMD          0x0100
#define IC_STOP         0x0200
#define IC_RESTART      0x0400

/* i2c interrupt status register definitions */
#define IC_ISR_ALL      0x0FFF
#define IC_GEN_CALL     0x0800
#define IC_START_DET    0x0400
#define IC_STOP_DET     0x0200
#define IC_ACTIVITY     0x0100
#define IC_RX_DONE      0x0080
#define IC_TX_ABRT      0x0040
#define IC_RD_REQ       0x0020
#define IC_TX_EMPTY     0x0010
#define IC_TX_OVER      0x0008
#define IC_RX_FULL      0x0004
#define IC_RX_OVER      0x0002
#define IC_RX_UNDER     0x0001

/* fifo threshold register definitions */
#define IC_TL0          0x00
#define IC_TL1          0x01
#define IC_TL2          0x02
#define IC_TL3          0x03
#define IC_TL4          0x04
#define IC_TL5          0x05
#define IC_TL6          0x06
#define IC_TL7          0x07
#define IC_RX_TL        IC_TL6 // Two Bytes bellow Full
#define IC_TX_TL        IC_TL2 // Two Bytes above Empty

/* i2c enable register definitions */
#define IC_ENABLE_0B    0x01
#define IC_TX_CMD_BLOCK 0x04

/* i2c status register  definitions */
#define IC_STATUS_SA    0x0040 // Slave Activity
#define IC_STATUS_MA    0x0020 // Master Activity
#define IC_STATUS_RFF   0x0010
#define IC_STATUS_RFNE  0x0008
#define IC_STATUS_TFE   0x0004
#define IC_STATUS_TFNF  0x0002
#define IC_STATUS_ACT   0x0001

#define DW_IC_COMP_PARAM_1_SPEED_MODE_HIGH (BIT(2) | BIT(3))
#define DW_IC_COMP_PARAM_1_SPEED_MODE_MASK (BIT(2) | BIT(3))

/**
 * struct dw_scl_sda_cfg - I2C timing configuration
 *
 * @ss_hcnt: Standard speed high time in ns
 * @fs_hcnt: Fast speed high time in ns
 * @hs_hcnt: High speed high time in ns
 * @ss_lcnt: Standard speed low time in ns
 * @fs_lcnt: Fast speed low time in ns
 * @hs_lcnt: High speed low time in ns
 * @sda_hold: SDA hold time
 */
struct dw_scl_sda_cfg {
    u32 ss_hcnt;
    u32 fs_hcnt;
    u32 hs_hcnt;
    u32 ss_lcnt;
    u32 fs_lcnt;
    u32 hs_lcnt;
    u32 sda_hold;
};

/**
 * struct dw_i2c_speed_config - timings to use for a particular speed
 *
 * This holds calculated values to be written to the I2C controller. Each value
 * is represented as a number of IC clock cycles.
 *
 * @scl_lcnt: Low count value for SCL
 * @scl_hcnt: High count value for SCL
 * @sda_hold: Data hold count
 * @speed_mode: Speed mode being used
 */
struct dw_i2c_speed_config {
    /* SCL high and low period count */
    u16 scl_lcnt;
    u16 scl_hcnt;
    u32 sda_hold;
    enum i2c_speed_mode speed_mode;
};

/**
 * struct dw_i2c - private information for the bus
 *
 * @regs: Registers pointer
 * @scl_sda_cfg: Deprecated information for x86 (should move to device tree)
 * @scl_rise_time_ns: Configured SCL rise time in nanoseconds
 * @scl_fall_time_ns: Configured SCL fall time in nanoseconds
 * @sda_hold_time_ns: Configured SDA hold time in nanoseconds
 * @has_spk_cnt: true if the spike-count register is present
 */
struct dw_i2c {
    volatile struct i2c_regs *regs;
    struct dw_scl_sda_cfg *scl_sda_cfg;
    u32 scl_rise_time_ns;
    u32 scl_fall_time_ns;
    u32 sda_hold_time_ns;
    bool has_spk_cnt;
    struct dw_i2c_speed_config config;
};

/**
 * struct dm_i2c_ops - driver operations for I2C uclass
 *
 * Drivers should support these operations unless otherwise noted. These
 * operations are intended to be used by uclass code, not directly from
 * other code.
 */
struct dm_i2c_ops {
    /**
     * xfer() - transfer a list of I2C messages
     *
     * @bus:    Bus to read from
     * @msg:    List of messages to transfer
     * @nmsgs:  Number of messages in the list
     * @return 0 if OK, -EREMOTEIO if the slave did not ACK a byte,
     * -ECOMM if the speed cannot be supported, -EPROTO if the chip
     * flags cannot be supported, other -ve value on some other error
     */
    int (*xfer)(struct dw_i2c *priv, struct i2c_msg *msg, int nmsgs);

    /**
     * probe_chip() - probe i2c peripheral/device
     *
     *
     * @priv: Variable to be modified to the point to the probed device/peripheral
     * @i2c_base: Base address of memory mapped registers of the device
     * @return 0 if chip was found, -EREMOTEIO if not, -ENOSYS to fall back
     * to default probem other -ve value on error
     */
    int (*probe)(struct dw_i2c *priv, volatile void *i2c_base);

    /**
     * probe_chip() - probe for the presense of a chip address
     *
     * This function is optional. If omitted, the uclass will send a zero
     * length message instead.
     *
     * @bus: Bus to probe
     * @chip_addr:  Chip address to probe
     * @chip_flags: Probe flags (enum dm_i2c_chip_flags)
     * @return 0 if chip was found, -EREMOTEIO if not, -ENOSYS to fall back
     * to default probem other -ve value on error
     */
    int (*probe_chip)(struct dw_i2c *priv, unsigned int chip_addr, unsigned int chip_flags);

    /**
     * set_bus_speed() - set the speed of a bus (optional)
     *
     * The bus speed value will be updated by the uclass if this function
     * does not return an error. This method is optional - if it is not
     * provided then the driver can read the speed from
     * dev_get_uclass_priv(bus)->speed_hz
     *
     * @bus:    Bus to adjust
     * @speed:  Requested speed in Hz
     * @return  0 if OK, -EINVAL for invalid values
     */
    int (*set_bus_speed)(struct dw_i2c *priv, unsigned int speed);

    void (*set_address)(volatile struct i2c_regs *i2c_base, unsigned int i2c_addr);
    void (*set_slave_address)(volatile struct i2c_regs *i2c_base, uint32_t i2c_addr);

    /**
     * get_bus_speed() - get the speed of a bus (optional)
     *
     * Normally this can be provided by the uclass, but if you want your
     * driver to check the bus speed by looking at the hardware, you can
     * implement that here. This method is optional. This method would
     * normally be expected to return dev_get_uclass_priv(bus)->speed_hz.
     *
     * @bus:    Bus to check
     * @return  speed of selected I2C bus in Hz, -ve on error
     */
    int (*get_bus_speed)(struct dw_i2c *priv);

    /**
     * set_flags() - set the flags for a chip (optional)
     *
     * This is generally implemented by the uclass, but drivers can
     * check the value to ensure that unsupported options are not used.
     * This method is optional. If provided, this method will always be
     * called when the flags change.
     *
     * @dev:    Chip to adjust
     * @flags:  New flags value
     * @return  0 if OK, -EINVAL if value is unsupported
     */
    int (*set_flags)(struct dw_i2c *priv, unsigned int flags);
    int (*configure)(
        volatile struct i2c_regs *i2c_base, uint32_t enable, uint32_t interrupts, uint32_t rx_tl, uint32_t tx_tl);

    /**
     * deblock() - recover a bus that is in an unknown state
     *
     * I2C is a synchronous protocol and resets of the processor in the
     * middle of an access can block the I2C Bus until a powerdown of
     * the full unit is done. This is because slaves can be stuck
     * waiting for addition bus transitions for a transaction that will
     * never complete. Resetting the I2C master does not help. The only
     * way is to force the bus through a series of transitions to make
     * sure that all slaves are done with the transaction. This method
     * performs this 'deblocking' if support by the driver.
     *
     * This method is optional.
     */
    int (*deblock)(struct dw_i2c *priv);

    void (*setup_interrupt)(struct dw_i2c *dev);
};

extern const struct dm_i2c_ops designware_i2c_ops;

/**
 * dw_i2c_gen_speed_config() - Calculate config info from requested speed
 *
 * Calculate the speed config from the given @speed_hz and return it so that
 * it can be incorporated in ACPI tables
 *
 * @dev: I2C bus to check
 * @speed_hz: Requested speed in Hz
 * @config: Returns config to use for that speed
 * Return: 0 if OK, -ve on error
 */
int dw_i2c_gen_speed_config(struct dw_i2c *priv, int speed_hz,
                struct dw_i2c_speed_config *config);

uint32_t get_int_status(struct dw_i2c *peripheral);

/**
 * set_slave_mode() - Set the I2C in slave-only mode
 *
 * @priv: I2C device to configure
 * @slave_addr: Slave address to respond to
 * Return: 0 if OK, -ve on error
 */
int set_slave_mode(struct dw_i2c* priv, uint32_t slave_addr);

#endif /* __DW_I2C_H_ */
