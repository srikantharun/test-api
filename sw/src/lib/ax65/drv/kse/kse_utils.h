#pragma once

#include <memorymap.h>
#include <stdint.h>

/* Base offsets */
#define ADDR_BASE_RAM                   (SOC_MGMT_ROT_KSE_BASE)
#define SHARED_RAM_SIZE					        (0x1200) //4.5KB

#define ADDR_BASE_CSR                   (ADDR_BASE_RAM+SHARED_RAM_SIZE)
/* ------------------------------------------- */
/* ---------CSR registers offsets--------------*/
/* ------------------------------------------- */
#define ADDR_CMD_CTRL                   ADDR_BASE_CSR+(0x0)
#define ADDR_CMD_STATUS                 ADDR_BASE_CSR+(0x4)
#define ADDR_CMD_TRK                    ADDR_BASE_CSR+(0x8)
#define ADDR_CMD_PERF                   ADDR_BASE_CSR+(0xc)
#define ADDR_INT_CTRL                   ADDR_BASE_CSR+(0x10)
#define ADDR_PWR_CTRL                   ADDR_BASE_CSR+(0x14)
#define ADDR_HW_ID                      ADDR_BASE_CSR+(0x18)
#define ADDR_NAGRA_ID                   ADDR_BASE_CSR+(0x1c)
#define ADDR_DBG_INFO_0                 ADDR_BASE_CSR+(0x20)
#define ADDR_DBG_INFO_1                 ADDR_BASE_CSR+(0x24)
#define ADDR_DBG_INFO_2                 ADDR_BASE_CSR+(0x28)

/* --------------------------------------------------*/
/* Commands supported by KSE3 production romcode */
/* ------------------------------------------------- */
#define KSE3_CMD_INIT_ROT             (0x1)
#define KSE3_CMD_INIT_CRYPTO          (0x2)
#define KSE3_CMD_WIPE_RAM             (0xD)
#define KSE3_CMD_LOAD_SEED            (0xB)
#define KSE3_CMD_GEN_SEED             (0xC)
#define KSE3_CMD_WRAP_KEY             (0x18)
#define KSE3_CMD_AES                  (0xC0)
#define KSE3_CMD_SHA                  (0xC2)
#define KSE3_CMD_HMAC                 (0xC3)
#define KSE3_CMD_TRNG                 (0xC4)
#define KSE3_CMD_ENSCHAR              (0xCA)
#define KSE3_CMD_MOD                  (0xC6)
#define KSE3_CMD_ECC                  (0xC7)
#define KSE3_CMD_SPONGE_AEAD          (0xC8)
#define KSE3_CMD_KDF                  (0xCB)
#define KSE3_CMD_DBG                  (0xA0)
#define KSE3_CMD_IMPORT_KEY           (0xA1)

/* Subtokens used in the commands specified above */
#define KSE3_CMD_AES_SUBTOKEN_CIPHER            (0x0)
#define KSE3_CMD_AES_SUBTOKEN_AEAD              (0x1)
#define KSE3_CMD_AES_SUBTOKEN_MAC               (0x2)
#define KSE3_CMD_AES_SUBTOKEN_AEAD              (0x1)
#define KSE3_CMD_COMMON_SUBTOKEN_INIT           (0x1)
#define KSE3_CMD_COMMON_SUBTOKEN_UPDATE         (0x2)
#define KSE3_CMD_COMMON_SUBTOKEN_FINAL          (0x3)
#define KSE3_CMD_COMMON_SUBTOKEN_GET_CONTEXT    (0x4)
#define KSE3_CMD_COMMON_SUBTOKEN_SET_CONTEXT    (0x5)
#define KSE3_CMD_TRNG_SUBTOKEN_GET_RAW_BITS     (0x1)
#define KSE3_CMD_TRNG_SUBTOKEN_GET_RANDOM_DATA  (0x2)
#define KSE3_CMD_TRNG_SUBTOKEN_RESEED           (0x3)
#define KSE3_CMD_TRNG_SUBTOKEN_UNINSTANTIATE    (0x4)
#define KSE3_CMD_MOD_SUBTOKEN_MUL               (0x0)
#define KSE3_CMD_MOD_SUBTOKEN_SQR               (0x1)
#define KSE3_CMD_MOD_SUBTOKEN_ADD               (0x2)
#define KSE3_CMD_MOD_SUBTOKEN_SUB               (0x3)
#define KSE3_CMD_MOD_SUBTOKEN_MONTMUL           (0x4)
#define KSE3_CMD_MOD_SUBTOKEN_PUB               (0x5)
#define KSE3_CMD_MOD_SUBTOKEN_INV               (0x6)
#define KSE3_CMD_MOD_SUBTOKEN_RED               (0x7)
#define KSE3_CMD_MOD_SUBTOKEN_INIT              (0x8)
#define KSE3_CMD_ECC_SUBTOKEN_SET               (0x0)
#define KSE3_CMD_ECC_SUBTOKEN_KP                (0x1)
#define KSE3_CMD_ECC_SUBTOKEN_KPADD             (0x2)
#define KSE3_CMD_ECC_SUBTOKEN_POINT_CHECK       (0x4)
#define KSE3_CMD_ECC_SUBTOKEN_SIGN              (0x5)
#define KSE3_CMD_ECC_SUBTOKEN_VERIFY            (0x7)
#define KSE3_CMD_ECC_SUBTOKEN_SHS               (0x8)
#define KSE3_CMD_SPONGE_AEAD_SUBTOKEN_INIT      (0x1)
#define KSE3_CMD_SPONGE_AEAD_SUBTOKEN_AUTH      (0x2)
#define KSE3_CMD_SPONGE_AEAD_SUBTOKEN_CIPHER    (0x3)
#define KSE3_CMD_SPONGE_AEAD_SUBTOKEN_FINAL     (0x4)
#define KSE3_CMD_KDF_SUBTOKEN_CMAC              (0x2)
#define KSE3_CMD_KDF_SUBTOKEN_HMAC              (0x3)
#define KSE3_CMD_DBG_SUBTOKEN_SET_SOC_CONFIG    (0x0)
#define KSE3_CMD_DBG_SUBTOKEN_UNLOCK_ACCESS     (0x2)
#define KSE3_CMD_DBG_SUBTOKEN_GET_CHALLENGE     (0x3)
#define KSE3_CMD_DBG_SUBTOKEN_SET_RUN_STATE     (0x4)
#define KSE3_CMD_DBG_SUBTOKEN_SET_OBJECT        (0x10)
#define KSE3_CMD_DBG_SUBTOKEN_GET_OBJECT        (0x11)

/* Status supported by KSE3 production romcode */
#define KSE3_SUCCESS                       (0xe5)

/* Offsets to be used into commands that use DRAM as input */
// InitCrypto
#define KSE3_DRAM_OFFSET_PERSO_STR_LEN    (ADDR_BASE_RAM + 0x0)
#define KSE3_DRAM_OFFSET_TRNG_CFG         (ADDR_BASE_RAM + 0x40)
#define KSE3_DRAM_OFFSET_PERSO_STR_VAL    (ADDR_BASE_RAM + 0x180)
// SetObject
#define KSE3_DRAM_OFFSET_SET_OBJ_TYPEID   (ADDR_BASE_RAM + 0x0)
#define KSE3_DRAM_OFFSET_ANCHOR_VAL_LEN   (ADDR_BASE_RAM + 0x4)
#define KSE3_DRAM_OFFSET_ANCHOR_VAL       (ADDR_BASE_RAM + 0x8)
// SetSocConfig
#define KSE3_DRAM_OFFSET_SOC_ID           (KSE3_DRAM_START_OFFSET + 0x0)
#define KSE3_DRAM_OFFSET_SOC_ID_INV       (KSE3_DRAM_START_OFFSET + 0x10)
#define KSE3_DRAM_OFFSET_DBG_COUNTER      (KSE3_DRAM_START_OFFSET + 0x20)
#define KSE3_DRAM_OFFSET_DBG_COUNTER_INV  (KSE3_DRAM_START_OFFSET + 0x24)
#define KSE3_DRAM_OFFSET_SOC_CLASS        (KSE3_DRAM_START_OFFSET + 0x28)

/* ------------------------------------------- */
/* ---------------AOR OFFSETS----------------- */
/* ------------------------------------------- */
#define KSE_AOR_BASE_ADDR                 (SOC_MGMT_ROT_AO_BASE)
#define KSE_AOR_SIZE                      (0x64)
#define KSE_AOR_SOC_CONFIG0_ADDR          (KSE_AOR_BASE_ADDR + 0x0)
#define KSE_AOR_SOC_CONFIG0_INV_ADDR      (KSE_AOR_BASE_ADDR + 0x4)
#define KSE_AOR_SOC_CONFIG1_ADDR          (KSE_AOR_BASE_ADDR + 0x8)
#define KSE_AOR_SOC_CONFIG1_INV_ADDR      (KSE_AOR_BASE_ADDR + 0xC)
#define KSE_AOR_PLT_CONFIG_ADDR           (KSE_AOR_BASE_ADDR + 0x10)
#define KSE_AOR_PLT_CONFIG_INV_ADDR       (KSE_AOR_BASE_ADDR + 0x14)
#define KSE_AOR_KSE3_STATE_ADDR           (KSE_AOR_BASE_ADDR + 0x18)
#define KSE_AOR_KSE3_STATE_INV_ADDR       (KSE_AOR_BASE_ADDR + 0x1C)
#define KSE_AOR_KSE3_FR0_ADDR             (KSE_AOR_BASE_ADDR + 0x20)
#define KSE_AOR_KSE3_FR1_ADDR             (KSE_AOR_BASE_ADDR + 0x24)
#define KSE_AOR_KSE3_FR2_ADDR             (KSE_AOR_BASE_ADDR + 0x28)
#define KSE_AOR_KSE3_FR3_ADDR             (KSE_AOR_BASE_ADDR + 0x2C)
#define KSE_AOR_KSE3_FR4_ADDR             (KSE_AOR_BASE_ADDR + 0x30)
#define KSE_AOR_KSE3_FR5_ADDR             (KSE_AOR_BASE_ADDR + 0x34)
#define KSE_AOR_KSE3_FR6_ADDR             (KSE_AOR_BASE_ADDR + 0x38)
#define KSE_AOR_KSE3_FR7_ADDR             (KSE_AOR_BASE_ADDR + 0x3C)

/* ------------------------------------------- */
/* -----------------OTP addresses------------- */
/* ------------------------------------------- */
//define OTP Memory spaces
#define OTP_MEM_OFFSET              0x0
#define OTP_MEM_BASE_ADDR           (SOC_MGMT_OTP_HOST_BASE+OTP_MEM_OFFSET)
#define OTP_SECURE_SIZE             0x100 //256 bytes
#define OTP_PUBLIC_RESERVED_SIZE    0x358 //856 bytes
#define OTP_PUBLIC_UNPROTECTED_SIZE 0x3A8 //936 bytes

/* ------------------------------------------- */
/* -----------------Functions----------------- */
/* ------------------------------------------- */
/* Implement the after reset sequence */
uint32_t kse_execute_after_reset_sequence();
/* Execute command function based on token and subtoken */
uint32_t kse_execute_cmd( uint8_t token, uint16_t sub_token, uint32_t allow_error);
/* Clear interrupt */
void kse_clear_irq();
/* Print HW and FW Revision */
void kse_print_ids();
/* Prepare data for InitCrypto command */
void prepare_data_for_cmd_init_crypto();


