// SPDX-License-Identifier: GPL-2.0+
/*
 * (C) Copyright 2009
 * Vipin Kumar, ST Micoelectronics, vipin.kumar@st.com.
 */

#include "drv_i2c.h"
#include <clk/drv_clk.h>
#include <interrupt.h>
#include <log.h>
#include <memorymap.h>
#include <platform.h>
#include <stdint.h>
#include <testutils.h>
#include <timer.h>

#define pI2C0 ((volatile struct i2c_regs *)(SOC_PERIPH_I2C_0_BASE))
#define pI2C1 ((volatile struct i2c_regs *)(SOC_PERIPH_I2C_1_BASE))

/*
 * This assigned unique hex value is constant and is derived from the two ASCII
 * letters 'DW' followed by a 16-bit unsigned number
 */
#define DW_I2C_COMP_TYPE 0x44570140

static int dw_i2c_enable(volatile struct i2c_regs *registers, bool enable) {
  u32 ena = enable ? IC_ENABLE_0B : 0;
  int timeout = 100;

  do {
    writel(ena, &(registers->ic_enable));
    // Confirm with a status change
    if ((readl(&registers->ic_enable_status) & IC_ENABLE_0B) == ena)
      return 0;

    /*
     * Wait 10 times the signaling period of the highest I2C
     * transfer supported by the driver (for 400KHz this is
     * 25us) as described in the DesignWare I2C databook.
     */
    udelay(1);
  } while (timeout--);
  LOG_DBG("timeout in %sabling I2C adapter\n", enable ? "en" : "dis");
  return -ETIMEDOUT;
}

/* High and low times in different speed modes (in ns) */
enum {
  /* SDA Hold Time */
  DEFAULT_SDA_HOLD_TIME = 300,
};

/**
 * calc_counts() - Convert a period to a number of IC clk cycles
 *
 * @ic_clk: Input clock in Hz
 * @period_ns: Period to represent, in ns
 * Return: calculated count
 */
static unsigned int calc_counts(unsigned int ic_clk, unsigned int period_ns) {
#define DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))
  return DIV_ROUND_UP(ic_clk / 1000 * period_ns, NANO_TO_KILO);
}

/**
 * struct i2c_mode_info - Information about an I2C speed mode
 *
 * Each speed mode has its own characteristics. This struct holds these to aid
 * calculations in dw_i2c_calc_timing().
 *
 * @speed: Speed in Hz
 * @min_scl_lowtime_ns: Minimum value for SCL low period in ns
 * @min_scl_hightime_ns: Minimum value for SCL high period in ns
 * @def_rise_time_ns: Default rise time in ns
 * @def_fall_time_ns: Default fall time in ns
 */
struct i2c_mode_info {
  int speed;
  int min_scl_hightime_ns;
  int min_scl_lowtime_ns;
  int def_rise_time_ns;
  int def_fall_time_ns;
};

static const struct i2c_mode_info info_for_mode[] = {
    [IC_SPEED_MODE_STANDARD] =
        {
            I2C_SPEED_STANDARD_RATE,
            MIN_SS_SCL_HIGHTIME,
            MIN_SS_SCL_LOWTIME,
            1000,
            300,
        },
    [IC_SPEED_MODE_FAST] =
        {
            I2C_SPEED_FAST_RATE,
            MIN_FS_SCL_HIGHTIME,
            MIN_FS_SCL_LOWTIME,
            300,
            300,
        },
    [IC_SPEED_MODE_FAST_PLUS] =
        {
            I2C_SPEED_FAST_PLUS_RATE,
            MIN_FP_SCL_HIGHTIME,
            MIN_FP_SCL_LOWTIME,
            260,
            500,
        },
    [IC_SPEED_MODE_HIGH] =
        {
            I2C_SPEED_HIGH_RATE,
            MIN_HS_SCL_HIGHTIME,
            MIN_HS_SCL_LOWTIME,
            120,
            120,
        },
};

/**
 * dw_i2c_calc_timing() - Calculate the timings to use for a bus
 *
 * @peripheral: Bus private information (NULL if not using driver model)
 * @mode: Speed mode to use
 * @ic_clk: IC clock speed in Hz
 * @spk_cnt: Spike-suppression count
 * @config: Returns value to use
 * Return: 0 if OK, -EINVAL if the calculation failed due to invalid data
 */
static int dw_i2c_calc_timing(struct dw_i2c *peripheral,
                              enum i2c_speed_mode mode, int ic_clk, int spk_cnt,
                              struct dw_i2c_speed_config *config) {
  int fall_cnt, rise_cnt, min_tlow_cnt, min_thigh_cnt;
  int hcnt, lcnt, period_cnt, diff, tot;
  int sda_hold_time_ns, scl_rise_time_ns, scl_fall_time_ns;
  const struct i2c_mode_info *info;

  UNUSED(peripheral);

  /*
   * Find the period, rise, fall, min tlow, and min thigh in terms of
   * counts of the IC clock
   */
  info = &info_for_mode[mode];
  period_cnt = ic_clk / info->speed;
  scl_rise_time_ns = info->def_rise_time_ns;
  scl_fall_time_ns = info->def_fall_time_ns;
  rise_cnt = calc_counts(ic_clk, scl_rise_time_ns);
  fall_cnt = calc_counts(ic_clk, scl_fall_time_ns);
  min_tlow_cnt = calc_counts(ic_clk, info->min_scl_lowtime_ns);
  min_thigh_cnt = calc_counts(ic_clk, info->min_scl_hightime_ns);

  LOG_DBG("dw_i2c: mode %d, ic_clk %d, speed %d, period %d rise %d fall %d "
          "tlow %d thigh %d spk %d\n",
          mode, ic_clk, info->speed, period_cnt, rise_cnt, fall_cnt,
          min_tlow_cnt, min_thigh_cnt, spk_cnt);

  /*
   * Back-solve for hcnt and lcnt according to the following equations:
   * SCL_High_time = [(HCNT + IC_*_SPKLEN + 7) * ic_clk] + SCL_Fall_time
   * SCL_Low_time = [(LCNT + 1) * ic_clk] - SCL_Fall_time + SCL_Rise_time
   */
  hcnt = min_thigh_cnt - fall_cnt - 7 - spk_cnt;
  lcnt = min_tlow_cnt - rise_cnt + fall_cnt - 1;

  if (hcnt < 0 || lcnt < 0) {
    LOG_DBG("dw_i2c: bad counts. hcnt = %d lcnt = %d\n", hcnt, lcnt);
    return -EINVAL;
  }

  /*
   * Now add things back up to ensure the period is hit. If it is off,
   * split the difference and bias to lcnt for remainder
   */
  tot = hcnt + lcnt + 7 + spk_cnt + rise_cnt + 1;

  if (tot < period_cnt) {
    diff = (period_cnt - tot) / 2;
    hcnt += diff;
    lcnt += diff;
    tot = hcnt + lcnt + 7 + spk_cnt + rise_cnt + 1;
    lcnt += period_cnt - tot;
  }

  config->scl_lcnt = lcnt;
  config->scl_hcnt = hcnt;

  /* Use internal default unless other value is specified */
  sda_hold_time_ns = DEFAULT_SDA_HOLD_TIME;
  config->sda_hold = calc_counts(ic_clk, sda_hold_time_ns);

  LOG_DBG("dw_i2c: hcnt = %d lcnt = %d sda hold = %d\n", hcnt, lcnt,
          config->sda_hold);

  return 0;
}

/**
 * calc_bus_speed() - Calculate the config to use for a particular i2c speed
 *
 * @peripheral: Private information for the driver (NULL if not using driver
 * model)
 * @registers: Registers for the I2C controller
 * @speed: Required i2c speed in Hz
 * @bus_clk: Input clock to the I2C controller in Hz (e.g. IC_CLK)
 * @config: Returns the config to use for this speed
 * Return: 0 if OK, -ve on error
 */
static int calc_bus_speed(struct dw_i2c *peripheral,
                          volatile struct i2c_regs *registers, int speed,
                          unsigned long bus_clk,
                          struct dw_i2c_speed_config *config) {
  const struct dw_scl_sda_cfg *scl_sda_cfg = NULL;
  enum i2c_speed_mode i2c_spd;
  int spk_cnt;
  int ret;

  if (peripheral)
    scl_sda_cfg = peripheral->scl_sda_cfg;
  /*
   * Allow high speed if there is no config, or the config allows it.
   * Round to the newarest lower speed setting.
   */
  if (speed >= I2C_SPEED_HIGH_RATE)
    i2c_spd = IC_SPEED_MODE_HIGH;
  else if (speed >= I2C_SPEED_FAST_PLUS_RATE)
    i2c_spd = IC_SPEED_MODE_FAST_PLUS;
  else if (speed >= I2C_SPEED_FAST_RATE)
    i2c_spd = IC_SPEED_MODE_FAST;
  else
    i2c_spd = IC_SPEED_MODE_STANDARD;

  /* Check if high speed is possible */
  if (i2c_spd == IC_SPEED_MODE_HIGH) {
    u32 comp_param1;

    comp_param1 = readl(&registers->comp_param1);
    if ((comp_param1 & DW_IC_COMP_PARAM_1_SPEED_MODE_MASK) !=
        DW_IC_COMP_PARAM_1_SPEED_MODE_HIGH)
      return 1;
  }

  /* Get the proper spike-suppression count based on target speed */
  if (!peripheral || !peripheral->has_spk_cnt)
    spk_cnt = 0;
  else if (i2c_spd >= IC_SPEED_MODE_HIGH)
    spk_cnt = readl(&registers->hs_spklen);
  else
    spk_cnt = readl(&registers->fs_spklen);
  if (scl_sda_cfg) {
    config->sda_hold = scl_sda_cfg->sda_hold;
    if (i2c_spd == IC_SPEED_MODE_STANDARD) {
      config->scl_hcnt = scl_sda_cfg->ss_hcnt;
      config->scl_lcnt = scl_sda_cfg->ss_lcnt;
    } else if (i2c_spd == IC_SPEED_MODE_HIGH) {
      config->scl_hcnt = scl_sda_cfg->hs_hcnt;
      config->scl_lcnt = scl_sda_cfg->hs_lcnt;
    } else {
      config->scl_hcnt = scl_sda_cfg->fs_hcnt;
      config->scl_lcnt = scl_sda_cfg->fs_lcnt;
    }
  } else {
    ret = dw_i2c_calc_timing(peripheral, i2c_spd, bus_clk, spk_cnt, config);
    if (ret)
      return ret;
  }
  config->speed_mode = i2c_spd;

  return 0;
}

/**
 * i2c_set_bus_speed() - Set the i2c speed
 *
 * @peripheral: Private information for the driver (NULL if not using driver
 * model)
 * @registers: Registers for the I2C controller
 * @speed: Required i2c speed in Hz
 * @bus_clk: Input clock to the I2C controller in Hz (e.g. IC_CLK)
 * Return: 0 if OK, -ve on error
 */
static int i2c_set_bus_speed(struct dw_i2c *peripheral, unsigned int speed) {
  volatile struct i2c_regs *registers = peripheral->regs;
  unsigned long bus_clk = CLK_SOC_PERIPH_Hz;

  struct dw_i2c_speed_config config;
  unsigned int cntl;
  unsigned int ena;
  int ret;

  ret = calc_bus_speed(peripheral, registers, speed, bus_clk, &config);
  if (ret)
    return ret;

  /* Get enable setting for restore later */
  ena = readl(&registers->ic_enable) & IC_ENABLE_0B;

  /* to set speed cltr must be disabled */
  dw_i2c_enable(registers, false);

  cntl = (readl(&registers->ic_con) & (~IC_CON_SPD_MSK));

  switch (config.speed_mode) {
  case IC_SPEED_MODE_HIGH:
    cntl |= IC_CON_SPD_HS;
    writel(config.scl_hcnt, &registers->ic_hs_scl_hcnt);
    writel(config.scl_lcnt, &registers->ic_hs_scl_lcnt);
    break;
  case IC_SPEED_MODE_STANDARD:
    cntl |= IC_CON_SPD_SS;
    writel(config.scl_hcnt, &registers->ic_ss_scl_hcnt);
    writel(config.scl_lcnt, &registers->ic_ss_scl_lcnt);
    break;
  case IC_SPEED_MODE_FAST_PLUS:
  case IC_SPEED_MODE_FAST:
  default:
    cntl |= IC_CON_SPD_FS;
    writel(config.scl_hcnt, &registers->ic_fs_scl_hcnt);
    writel(config.scl_lcnt, &registers->ic_fs_scl_lcnt);
    break;
  }

  writel(cntl, &registers->ic_con);

  /* Configure SDA Hold Time if required */
  if (config.sda_hold)
    writel(config.sda_hold, &registers->ic_sda_hold);

  /* Restore back i2c now speed set */
  if (ena == IC_ENABLE_0B)
    dw_i2c_enable(registers, true);
  if (peripheral)
    peripheral->config = config;

  return 0;
}

int dw_i2c_gen_speed_config(struct dw_i2c *peripheral, int speed_hz,
                            struct dw_i2c_speed_config *config) {
  unsigned long rate;
  int ret;

  rate = CLK_SOC_PERIPH_Hz;
  ret = calc_bus_speed(peripheral, peripheral->regs, speed_hz, rate, config);
  if (ret) {
    LOG_DBG("%s: ret=%d\n", __func__, ret);
    return ret;
  }
  return 0;
}

/*
 * designware_i2c_setaddress
 * @registers:   Base address of device registers
 * @i2c_addr:   Target address
 *
 * Sets the target slave address.
 */
static void i2c_set_address(volatile struct i2c_regs *registers,
                            unsigned int i2c_addr) {
  /* Disable i2c */
  dw_i2c_enable(registers, false);

  writel(i2c_addr, &registers->ic_tar);

  /* Enable i2c */
  dw_i2c_enable(registers, true);
}

/*
 * i2c_set_slave_address
 * @registers:   Base address of device registers
 * @i2c_addr:   Slave address
 *
 * Sets it's own slave address.
 */
static void i2c_set_slave_address(volatile struct i2c_regs *registers,
                                  uint32_t i2c_addr) {
  /* Disable i2c */
  dw_i2c_enable(registers, false);

  writel(i2c_addr, &registers->ic_sar);

  /* Enable i2c */
  dw_i2c_enable(registers, true);
}

/*
 * i2c_flush_rxfifo - Flushes the i2c RX FIFO
 */
static void i2c_flush_rxfifo(volatile struct i2c_regs *registers) {
  while (readl(&registers->ic_status) & IC_STATUS_RFNE)
    readl(&registers->ic_cmd_data);
}

/**
 * i2c_wait_for_bb - Returns true if bus is busy for certain time period
 */
static int i2c_wait_for_bb(volatile struct i2c_regs *registers) {
  unsigned long start_time_bb = get_timer(0);

  // While Master has activity OR while not TFE (Transmit FIFO not Completelyn
  // Empty)
  while ((readl(&registers->ic_status) & IC_STATUS_MA) ||
         !(readl(&registers->ic_status) & IC_STATUS_TFE)) {
    /* Evaluate timeout */
    if (get_timer(start_time_bb) > (unsigned long)(I2C_BYTE_TO_BB)) {
      return 1;
    }
  }

  return 0;
}

/**
 * i2c_init - Init function
 * @speed:      required i2c speed
 * @slaveaddr:  slave address for the device
 *
 * Initialization function.
 */
static int i2c_init(volatile struct i2c_regs *registers, int speed) {
  UNUSED(speed);
  int ret;

  // Get AXI address of the first register
  // To-Do: Speed selector
  // To-Do: Setting slave address

  /* Disable i2c */
  ret = dw_i2c_enable(registers, false);
  if (ret) {
    return ret;
  }

  uint32_t reg_val = IC_CON_SD | IC_CON_RE | IC_CON_SPD_FS | IC_CON_MM;
  writel(reg_val, &registers->ic_con);

  if ((readl(&(registers->ic_con)) & (reg_val | IC_CON_SPD_MSK)) != reg_val) {
    return 1;
  }

  // Set to Threshold Level
  writel(IC_RX_TL, &registers->ic_rx_tl);
  writel(IC_TX_TL, &registers->ic_tx_tl);
  // Enable default interrupts, can be changed
  writel(IC_STOP_DET | IC_RX_UNDER, &registers->ic_intr_mask);

  /* Enable i2c */
  ret = dw_i2c_enable(registers, true);
  if (ret) {
    return ret;
  }

  return 0;
}

static int i2c_xfer_finish(volatile struct i2c_regs *registers) {
  unsigned long start_stop_det = get_timer(0);

  while (1) {
    if ((readl(&registers->ic_raw_intr_stat) & IC_STOP_DET)) {
      readl(&registers->ic_clr_stop_det);
      break;
    } else if (get_timer(start_stop_det) > I2C_STOPDET_TO) {
      break;
    }
  }

  if (i2c_wait_for_bb(registers))
    return 1;

  i2c_flush_rxfifo(registers);

  return 0;
}

/**
 * i2c_xfer_read - Read from i2c memory
 *
 * @registers - pointer to I2C registers
 * @chip      - target chip's I2C address - no need as it was already configured
 * @addr     - address of memory location on the target chip
 * @alen     - number of Bytes of addr
 * @buffer   - buffer for read data
 * @len:     - no of bytes to be read
 */
static int i2c_xfer_read(volatile struct i2c_regs *registers,
                         struct i2c_msg *msg) {
  unsigned i = 0;
  unsigned long start_time_rx;
  unsigned int active = 0;

  start_time_rx = get_timer(0);
  // Address counter already in the chip
  while (i < msg->len) {
    // Initate a read if not active
    if (!active) {
      // Perform a read of the last byte and issue stop condition
      if (msg->len - i == 1)
        writel(IC_CMD | IC_STOP, &registers->ic_cmd_data); // IC_RESTART |
      // Generate start condition and read the first and every subsequent byte
      else
        writel(IC_CMD, &registers->ic_cmd_data); // IC_RESTART |

      /*
       * Avoid writing to ic_cmd_data multiple times
       * in case this loop spins too quickly and the
       * ic_status RFNE bit isn't set after the first
       * write. Subsequent writes to ic_cmd_data can
       * trigger spurious i2c transfer.
       */
      active = 1;
    }

    // If RX FIFO is not empty, read it out
    if (readl(&registers->ic_status) & IC_STATUS_RFNE) {
      msg->buf[i] = (unsigned char)readl(&registers->ic_cmd_data);
      i++;
      start_time_rx = get_timer(0);
      // Only if one byte is read, a next byte can be read
      active = 0;
    }
    // If RX FIFO is empty, wait for the next byte for certain time
    else if (get_timer(start_time_rx) > I2C_BYTE_TO) {
      return 1;
    }
  }

  return 0;
}

/**
 * i2c_xfer_write - Write to i2c memory
 *
 * @registers - pointer to I2C registers
 * @chip      - target chip's I2C address - no need as it was already configured
 * @addr     - address of memory location on the target chip
 * @alen     - number of Bytes of addr
 * @buffer   - buffer for write data
 * @len:     - no of bytes to be written
 */
static int i2c_xfer_write(volatile struct i2c_regs *registers,
                          struct i2c_msg *msg) {
  unsigned i = 0;
  unsigned long start_time_tx;

  start_time_tx = get_timer(0);
  while (i < msg->len) {
    if (readl(&registers->ic_status) & IC_STATUS_TFNF) {
      // Perform a write of the last byte and issue stop condition
      if (i == msg->len - 1) {
        writel(msg->buf[i] | IC_STOP, &registers->ic_cmd_data);
      }
      // Generate start condition and write the first and every subsequent byte
      else {
        writel(msg->buf[i], &registers->ic_cmd_data);
      }
      i++;
      start_time_tx = get_timer(0);
    }
    /*
     * Wait maximum of at least 10*UART_CLK_PERIOD for the next byte to finish
     */
    else if (get_timer(start_time_tx) > ((unsigned)(msg->len * I2C_BYTE_TO))) {
      return 1;
    }
  }

  return 0;
}

/**
 * i2c_configure  - configures interrupts
 *
 * @registers - pointer to I2C registers
 * @enable        - enable/disable I2C, 0 - disable, 1 - enable
 * @interrupts    - interrupts to be enabled
 * @rx_threshold  - RX FIFO threshold level
 * @tx_threshold  - TX FIFO threshold level
 * Return: 0 if OK, otherwise the error code
 */
static int i2c_configure(volatile struct i2c_regs *registers, uint32_t enable,
                         uint32_t interrupts, uint32_t rx_threshold,
                         uint32_t tx_threshold) {
  int ret;

  /* Disable i2c */
  ret = dw_i2c_enable(registers, false);
  if (ret)
    return ret;

  /* Keep IC_ENABLE bits besides bit 0 */
  enable &= ~IC_ENABLE_0B;
  writel(enable, &registers->ic_enable);

  /* Enable interrupts */
  writel(interrupts, &registers->ic_intr_mask);

  /* Keep old speed */
  uint32_t speed = readl(&(registers->ic_con)) & IC_CON_SPD_MSK;
  /* Param to configure IC_CON can be added to the function */
  uint32_t con = IC_CON_RE | IC_CON_MM | speed;
  writel(con, &registers->ic_con);

  /* Set to Threshold Level */
  writel(rx_threshold, &registers->ic_rx_tl);
  writel(tx_threshold, &registers->ic_tx_tl);

  /* Remain disabled if desired */
  if (enable & IC_ENABLE_0B) {
    ret = dw_i2c_enable(registers, true);
    if (ret)
      return ret;
  }

  /* Set TX Command Block bit if necessary */
  writel(enable | IC_ENABLE_0B, &registers->ic_enable);

  return 0;
}

/**
 * i2c_xfer       - configures interrupts
 *
 * @peripheral    - pointer to peripheral structure
 * @msg           - pointer to I2C message array
 * @nmsgs         - number of messages
 * Return: 0 if OK, otherwise the error code
 */
static int i2c_xfer(struct dw_i2c *peripheral, struct i2c_msg *msg, int nmsgs) {
  struct dw_i2c *i2c = peripheral;
  int ret;

  /* Set the target slave address */
  i2c_set_address(peripheral->regs, msg->addr);

  for (; nmsgs > 0; nmsgs--, msg++) {
    if (msg->flags & I2C_M_RD) {
      ret = i2c_xfer_read(i2c->regs, msg);
      if (ret) {
        return -EREMOTEIO;
      }
    } else {
      ret = i2c_xfer_write(i2c->regs, msg);
      if (ret) {
        return -EREMOTEIO;
      }
    }
    udelay(1);
    ret = i2c_wait_for_bb(peripheral->regs);
    if (!CHECK_TRUE(ret == 0, "ERROR: Bus not free in time\n"))
      return 1;
  }

  return i2c_xfer_finish(peripheral->regs);
}

static int i2c_probe_chip(struct dw_i2c *peripheral, unsigned int chip_addr,
                          unsigned int chip_flags) {
  UNUSED(chip_flags);

  int ret;
  struct i2c_msg read_msg[2];
  uint16_t read_addr = 0;
  uint8_t read_addr_buf[2];
  uint8_t read_buf[256];

  /* Only 2 Bytes for address inside EEPROM */
  read_addr_buf[0] = (read_addr >> 8) & 0xFF;
  read_addr_buf[1] = read_addr & 0xFF;

  /* Write command and address of the data inside EEPROM to read from */
  read_msg[0].addr = chip_addr;
  read_msg[0].buf = read_addr_buf;
  read_msg[0].flags = 0;
  read_msg[0].len = 2;

  /* Read command and read buffer for incomming data */
  read_msg[1].addr = chip_addr;
  read_msg[1].buf = read_buf;
  read_msg[1].flags = I2C_M_RD;
  read_msg[1].len = 1;

  ret = i2c_init(peripheral->regs, 0);
  /* Try to read the first location of the chip */
  if (ret == 0)
    ret = i2c_xfer(peripheral, read_msg, 2);
  return 0;
}

/*
    Probe peripheral (device)
*/
static int i2c_probe(struct dw_i2c *peripheral, volatile void *base_addr) {
  MEMSET(peripheral, 0, sizeof(struct dw_i2c));
  peripheral->regs = base_addr;

  /* Skip setting up resets and clocks */

  unsigned int comp_type;

  /* Read perepheral fixed information */
  comp_type = readl(&peripheral->regs->comp_type);
  if (comp_type != DW_I2C_COMP_TYPE) {
    return -ENXIO;
  }

  LOG_DBG("I2C bus version #%x\n", readl(&peripheral->regs->comp_version));

  return i2c_init(peripheral->regs, 0);
}

static void i2c_setup_interrupt(struct dw_i2c *peripheral) {
  dw_i2c_enable(peripheral->regs, false);
  if ((uintptr_t)peripheral->regs == SOC_PERIPH_I2C_0_BASE) {
    // TODO: Make it cleaner?
    HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_I2C_0_SOURCE);
    HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_I2C_0_SOURCE, IRQ_PRIORITY_DEFAULT);
  }
  if ((uintptr_t)peripheral->regs == SOC_PERIPH_I2C_1_BASE) {
    // TODO: Make it cleaner?
    HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_I2C_1_SOURCE);
    HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_I2C_1_SOURCE, IRQ_PRIORITY_DEFAULT);
  }
  dw_i2c_enable(peripheral->regs, true);
}

const struct dm_i2c_ops designware_i2c_ops = {
    .xfer = i2c_xfer,
    .probe = i2c_probe,
    .probe_chip = i2c_probe_chip,
    .set_bus_speed = i2c_set_bus_speed,
    .set_address = i2c_set_address,
    .set_slave_address = i2c_set_slave_address,
    .configure = i2c_configure,
    .setup_interrupt = i2c_setup_interrupt};

uint32_t get_int_status(struct dw_i2c *peripheral) {
  return readl(&peripheral->regs->ic_intr_stat);
}

int set_slave_mode(struct dw_i2c *priv, uint32_t slave_addr) {
  int ret;

  // Disable I2C
  ret = dw_i2c_enable(priv->regs, false);
  if (ret) {
    return ret;
  }

  writel(slave_addr, &priv->regs->ic_sar);

  // Clear IC_SLAVE_DISABLE and MASTER_MODE bits and set addressing to 7 bits
  uint32_t ic_con = readl(&priv->regs->ic_con);
  ic_con &= ~(uint32_t)(IC_CON_SD | IC_CON_MM);
  writel(ic_con, &priv->regs->ic_con);

  // Enable back i2c
  ret = dw_i2c_enable(priv->regs, true);
  return ret;
}

// Overrides the default i2c handler
void i2c0_irq_handler(void) { (void)pI2C0->ic_clr_intr; }

void i2c1_irq_handler(void) { (void)pI2C1->ic_clr_intr; }
