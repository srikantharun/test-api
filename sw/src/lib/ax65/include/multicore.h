#pragma once

#include <multicore_common.h>

/**
 * @file multicore.h
 * @brief Library for managing the booting, starting, and synchronization of AI cores and PVE cores.
 */

// Size of registers in bytes
#define SYS_CFG_PVE_REG_SIZE 4
// First 0x200 addresses reserved for PVE PCTL
#define SYS_CFG_PVE_BOOT_ADDR_LSB_OFFSET    (0x200)
#define SYS_CFG_PVE_BOOT_ADDR_MSB_OFFSET    (0x220)
#define SYS_CFG_PVE_BOOT_ADDR_CLK_EN_OFFSET (0x240)

/**
 * @brief Initializes the multicore subsystem.
 * 
 * This function is called internally to perform initialization routines for
 * the multicore subsystem. Users typically do not need to call this function
 * directly.
 */
void _multicores_init();

/**
 * @brief Checks if a specific core is available on the current platform.
 * 
 * This function determines whether a given core is available based on 
 * hardware definitions and the provided core ID.
 * 
 * @param[in] i The core ID to check.
 * @return Returns 1 if the core is available, or 0 if the core is not available.
 */
int is_core_available(uint32_t core_id);

/**
 * @brief Boots an AI Core.
 * 
 * This function enables the necessary signals through the PCTL and configures 
 * the required Always-On (AO) registers to start an AI Core.
 * 
 * @param[in] core_id ID of the AI Core to boot, valid range: [6, 13].
 */
void boot_aicore(uint32_t core_id);

/**
 * @brief Boots a core inside a PVE.
 * 
 * This function enables the necessary signals through the PCTL and configures 
 * the required Always-On (AO) registers to start a core within a Processing 
 * Vector Engine (PVE).
 * 
 * @param[in] core_id ID of the PVE core to boot. 
 *                    - For PVE 0: valid range: [14, 21].
 *                    - For PVE 1: valid range: [22, 29].
 */
void boot_pve_core(uint32_t core_id);

/**
 * @brief Starts a specified core.
 * 
 * This function enables all necessary signals to start the specified core.
 * 
 * @param[in] core_id ID of the core to start:
 *                    - AI Cores: valid range: [6, 13].
 *                    - PVE 0 Cores: valid range: [14, 21].
 *                    - PVE 1 Cores: valid range: [22, 29].
 */
void start_core(uint32_t core_id);

/**
 * @brief Waits for a specific core to finish execution.
 * 
 * This function blocks execution until the specified core has completed its task.
 * 
 * @param[in] core_id ID of the core to wait for:
 *                    - AI Cores: valid range: [6, 13].
 *                    - PVE 0 Cores: valid range: [14, 21].
 *                    - PVE 1 Cores: valid range: [22, 29].
 * @return Returns 0 if the wait operation was successful, or a negative error 
 *         code if it fails.
 */
int wait_core(uint32_t core_id);

/**
 * @brief Starts all cores in PVE 0 individually.
 * 
 * This function starts each core in PVE 0 by enabling the necessary signals 
 * for each core.
 */
void start_aicores();

/**
 * @brief Waits for all cores in PVE 0 to finish execution.
 * 
 * This function blocks execution until all cores in PVE 0 have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a negative error 
 *         code if it fails.
 */
int wait_aicores();

/**
 * @brief Starts all available AI cores in the platform.
 * 
 * This function starts each available AI core by enabling the necessary signals
 * and setting the right registers for each core.
 */
void start_aicores_available();

/**
 * @brief Waits for all available AI cores in the platform to finish execution.
 * 
 * This function blocks execution until all available AI cores have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a non-zero error
 *         code if it fails.
 */
int wait_aicores_available();

/**
 * @brief Starts all cores in PVE 0 individually.
 * 
 * This function starts each core in PVE 0 by enabling the necessary signals 
 * for each core.
 */
void start_cores_pve0();

/**
 * @brief Waits for all cores in PVE 0 to finish execution.
 * 
 * This function blocks execution until all cores in PVE 0 have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a negative error 
 *         code if it fails.
 */
int wait_cores_pve0();

/**
 * @brief Starts all available cores in the platform in PVE 0.
 * 
 * This function starts each core in PVE 0 by enabling the necessary signals
 * and setting the right registers for each core.
 */
void start_cores_pve0_available();

/**
 * @brief Waits for all available cores in the platform in PVE 0 to finish execution.
 * 
 * This function blocks execution until all available cores in PVE 0 have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a non-zero error
 *         code if it fails.
 */
int wait_cores_pve0_available();

/**
 * @brief Starts all cores in PVE 1 individually.
 * 
 * This function starts each core in PVE 1 by enabling the necessary signals 
 * for each core.
 */
void start_cores_pve1();

/**
 * @brief Waits for all cores in PVE 1 to finish execution.
 * 
 * This function blocks execution until all cores in PVE 1 have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a negative error 
 *         code if it fails.
 */
int wait_cores_pve1();

/**
 * @brief Starts all available cores in the platform in PVE 1.
 * 
 * This function starts each available core in PVE 1 by enabling the necessary signals
 * and setting the right registers for each core.
 */
void start_cores_pve1_available();

/**
 * @brief Waits for all available cores in the platform in PVE 1 to finish execution.
 * 
 * This function blocks execution until all available cores in PVE 1 have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a non-zero error
 *         code if it fails.
 */
int wait_cores_pve1_available();

/**
 * @brief Starts all cores on the chip.
 *  
 * This function starts each core by enabling the necessary signals
 * and setting the right registers for each core. Should be called only
 * on the top platform that has all cores instantiated.
 */

void start_cores_all();

/**
 * @brief Starts all available cores in the platform.
 * 
 * This function starts each available core by enabling the necessary signals
 * and setting the right registers for each core.
 */
void start_cores_available();

/**
 * @brief Waits for all available cores in the platform to finish execution.
 * 
 * This function blocks execution until all available cores in PVE 1 have completed their tasks.
 * 
 * @return Returns 0 if the wait operation was successful, or a non-zero error
 *         code if it fails.
 */
int wait_cores_available();
