#ifndef CDNS_EMMC_H
#define CDNS_EMMC_H
#include <stdbool.h>
#include <stdint.h>

#define EMMC_MAX_BLOCK_SIZE 512 // in bytes

/// @brief Init EMMC controller:
///        - Configure phy
///        - Enable supply voltage for EMMC mem
///        - Enable clocks for EMMC mem
///        - Enable status flags in controller
void emmc_sd_host_init(void);

/// @brief Configure EMMC card and select it
///
/// @param low_voltage_en Enable support for 1.7-1.95V range in OCR, in addition to the 2.7-3.6V range.
/// @param sd_card_rca RCA to give to the EMMC card
int emmc_card_init(bool low_voltage_en, uint16_t sd_card_rca);

/// @brief Send CMD13 to get card status
///
/// @return EMMC card status (see Section 6.13 - 'Device status' of JEDEC Standard No. 84-B51)
uint32_t emmc_card_get_status();

/// @brief Send CMD7 to select the card and set it to TRANS state.
///
/// @warning This function MUST be called AFTER #emmc_card_init.
void emmc_select_card();

/// @brief Configure the controller to use standard mode
///
/// @param bit_width Transfer width in bits. Valid values: 1,4,8
void emmc_set_standard_mode(uint32_t bit_width);

/// @brief Perform a write transfer from the chip to the emmc card.
///
/// @param system_addr Source buffer address (chip's side)
/// @param emmc_addr Destination address (EMMC's side)
/// @param block_cnt Number of blocks to transfer. Transfer size is (@p block_cnt * #EMMC_MAX_BLOCK_SIZE)
///
/// @return Error status from SRS12 register
uint32_t emmc_dma_write_xfer(uint32_t system_addr, uint32_t emmc_addr,
                             uint32_t block_cnt);

/// @brief Perform a read transfer from the emmc card to the chip.
///
/// @param emmc_addr Source address (EMMC's side)
/// @param system_addr Destination buffer address (chip's side)
/// @param block_cnt Number of blocks to transfer. Transfer size is (@p block_cnt * #EMMC_MAX_BLOCK_SIZE)
///
/// @return Error status from SRS12 register
uint32_t emmc_dma_read_xfer(uint32_t emmc_addr, uint32_t system_addr,
                            uint32_t block_cnt);

/// @brief Reset and configure emmc phy for standard mode
///
/// @warning The parameters defined is this function may change for other speedgrades
///          or input clock frequencies. Use the python script provided with the
///          EMMC controller to check for any changes:
///          hw/ip/emmc/default/calc_settings
void emmc_config_phy_sd(void);

/// @brief Enable interrupt generation
///
/// @param interrupts Interrupts to enable (See SRS12 flags)
///
/// @warning This function must be called after #emmc_sd_host_init
///          since interrupts need SRS13 and SRS14 to be configured
void emmc_enable_interrupts(uint32_t interrupts);

/// @brief Disable interrupt generation
///
/// @param interrupts Interrupts to disable (See SRS12 flags)
void emmc_disable_interrupts(uint32_t interrupts);

/// @brief Return the current interrupt status and clear all W1C interrupts
///
/// @return Current interrupt status
uint32_t emmc_get_int_status(void);

/// @brief EMMC IRQ handler
///
/// @warning This handler is necessary for all for transfers
void emmc_irq_handler(void);

// These functions are used for qemu platform
// on which some basic write/read functionalities are tested
// for cadence sdhci emulation
void reset_core(void);
void write_phy_reg(uint32_t addr, uint32_t data);
uint32_t read_phy_reg(uint32_t addr);

/// @brief Set the value of the 'Internal Clock Stable' (ICS) signal
///
/// @details This signal is set from the SOC_PERIPH CSRs it indicates that the clock
///          generated by the external PLL is stable.
///
/// @param is_stable If true, set ICS to 1 (i.e. clock stable)
void emmc_set_clock_stable(bool is_stable);

/// @brief Enable EMMC interface reset signal
///
void emmc_enable_reset(void);

/// @brief Enable EMMC interface reset signal
///
void emmc_disable_reset(void);
#endif
