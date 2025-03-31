#pragma once

#include <memorymap.h>
/*
Constants related to KSE3 and its stand-alone test-bench
*/

/* Base offsets */
#define ADDR_BASE_RAM                    (SOC_MGMT_ROT_KSE_BASE)
#define SHARED_RAM_SIZE					 (0x1200) //4.5KB

#define ADDR_BASE_CSR                    (ADDR_BASE_RAM+SHARED_RAM_SIZE)

/* CSR registers offsets */
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

/* Commands supported by KSE3 integration romcode */

/* HVC */
#define KSE3_CMD_HVC                  (0x00)

/* Cryptobox validation */
#define KSE3_CMD_CB_TEST_AES          (0xE0)
#define KSE3_CMD_CB_TEST_MODARITH     (0xE1)
#define KSE3_CMD_CB_TEST_SHA2         (0xE2)
#define KSE3_CMD_CB_TEST_SPONGE_BASIC (0xE3)
#define KSE3_CMD_CB_TEST_SPONGE_AEAD  (0xE4)
#define KSE3_CMD_CB_TEST_SHA3         (0xE5)
#define KSE3_CMD_CB_TEST_SEED         (0xE6)
#define KSE3_CMD_CB_TEST_CHACHA20     (0xE7)

/* Internal CPU validation */
#define KSE3_CMD_HW_TEST_CPU          (0xB0)

/* Interface validation */
#define KSE3_CMD_HW_TEST_IRAM_EXEC    (0xBE)
#define KSE3_CMD_HW_TEST_IRAM         (0xBF)
#define KSE3_CMD_HW_TEST_OTP_READ     (0xC0)
#define KSE3_CMD_HW_TEST_CLK          (0xC1)
#define KSE3_CMD_HW_TEST_DRAM         (0xC2)
#define KSE3_CMD_HW_TEST_PLATFORM     (0xC3)
#define KSE3_CMD_HW_TEST_OTP_WRITE    (0xC4)
#define KSE3_CMD_HW_TEST_RAM_ERROR    (0xC5)
#define KSE3_CMD_HW_TEST_RAM_WIPE     (0xC6)
#define KSE3_CMD_HW_TEST_CONFIG       (0xC7)
#define KSE3_CMD_HW_TEST_RAM_PRIVATE  (0xC8)
#define KSE3_CMD_HW_TEST_RAM_LOCK     (0xC9)
#define KSE3_CMD_HW_TEST_ILLOP        (0xCA)
#define KSE3_CMD_HW_TEST_BAD_DADDR    (0xCB)
#define KSE3_CMD_HW_TEST_BAD_IADDR    (0xCC)
#define KSE3_CMD_HW_TEST_AOR_0_7      (0xCD)
#define KSE3_CMD_HW_TEST_ROM          (0xCE)
#define KSE3_CMD_HW_TEST_AOR_8_15     (0xCF)
#define KSE3_CMD_HW_TEST_KEYBUS       (0xD0)
#define KSE3_CMD_HW_TEST_ENS          (0xD1)
#define KSE3_CMD_HW_TEST_KEYPROT      (0xD2)
#define KSE3_CMD_HW_TEST_HOST_ID      (0xD3)
#define KSE3_CMD_HW_TEST_KEYPROT_IP   (0xD4)

/* Status supported by KSE3 integration romcode */
#define KSE3_SUCCESS                       (0xe5)


/* Nagra stand-alone testbench for integration */
#define TB_CRM_BASE_ADDR     0x00100000
#define TB_CRM_CTRL          (TB_CRM_BASE_ADDR + 0x0)
#define TB_REGS_BASE_ADDR    0x00200000
#define TB_REGS_CTRL         (TB_REGS_BASE_ADDR + 0x4)
#define TB_REGS_CONFIG       (TB_REGS_BASE_ADDR + 0x8)
#define TB_REGS_KP_DOUT      (TB_REGS_BASE_ADDR + 0xC)
#define TB_KEYBUS_BASE_ADDR  0x00300000
#define TB_KEYPROT_BASE_ADDR 0x00400000
#define TB_AHB_AOR_ADDR      0x00080000
