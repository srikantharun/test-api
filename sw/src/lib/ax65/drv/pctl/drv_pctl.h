// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#pragma once

#include <memorymap.h>
#include <std/std_basetype.h>
#include <stdint.h>
#include <std/std_bit.h>

#define MAX_RESETS  8
#define MAX_CLKDIVS 8
#define MAX_FENCES  4
#define MAX_BANKS   4

#define MAX_ITERATIONS 10

/* Bitfields in PPMU_RESET_CONTROL */
// Initiates reset removal
#define RESET_REMOVE_OFFSET               0
#define RESET_REMOVE_MASK                 0x01

// Initiates reset activation
#define RESET_ACTIVATE_OFFSET             1
#define RESET_ACTIVATE_MASK               0x01


/* Bitfields in PPMU_RESET_TIMING_CONTROL */
#define PRE_RST_0_CYCLES_OFFSET            0x00
#define PRE_RST_0_CYCLES_MASK              0xff
#define PRE_RST_0_CYCLES_RESET_VAL         0x4

#define PRE_RST_1_CYCLES_OFFSET            8
#define PRE_RST_1_CYCLES_MASK              0xff
#define PRE_RST_1_CYCLES_RESET_VAL         0x4

#define PRE_RST_2_CYCLES_OFFSET            16
#define PRE_RST_2_CYCLES_MASK              0xff
#define PRE_RST_2_CYCLES_RESET_VAL         0x4

#define PRE_REL_CYCLES_OFFSET              24
#define PRE_REL_CYCLES_MASK                0xff
#define PRE_REL_CYCLES_RESET_VAL           0x4


/* Bitfields in PPMU_STATUS */
#define PARTITION_RESET_FSM_STATE_0_OFFSET 0
#define PARTITION_RESET_FSM_STATE_0_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_1_OFFSET 4
#define PARTITION_RESET_FSM_STATE_1_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_2_OFFSET 8
#define PARTITION_RESET_FSM_STATE_2_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_3_OFFSET 12
#define PARTITION_RESET_FSM_STATE_3_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_4_OFFSET 16
#define PARTITION_RESET_FSM_STATE_4_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_5_OFFSET 20
#define PARTITION_RESET_FSM_STATE_5_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_6_OFFSET 24
#define PARTITION_RESET_FSM_STATE_6_MASK   0x0f

#define PARTITION_RESET_FSM_STATE_7_OFFSET 28
#define PARTITION_RESET_FSM_STATE_7_MASK   0x0f


/* Bitfields in PPMU_ISOLATION_CONTROL */
#define ISOLATION_IDLE_REQ_0_OFFSET        0
#define ISOLATION_IDLE_REQ_0_MASK          0x01

#define ISOLATION_IDLE_REQ_1_OFFSET        1
#define ISOLATION_IDLE_REQ_1_MASK          0x01

#define ISOLATION_IDLE_REQ_2_OFFSET        2
#define ISOLATION_IDLE_REQ_2_MASK          0x01

#define ISOLATION_IDLE_REQ_3_OFFSET        3
#define ISOLATION_IDLE_REQ_3_MASK          0x01

/* Bitfields in PPMU_ISOLATION_STATUS */
#define ISOLATION_IDLE_ACK_OFFSET          0
#define ISOLATION_IDLE_ACK_MASK            0x01

#define ISOLATION_IDLE_VAL_OFFSET          1
#define ISOLATION_IDLE_VAL_MASK            0x01

/* Bitfields in PPMU_INTERNAL_SHUTDOWN_CONTROL */
#define SW_SHUTDOWN_REQ_OFFSET             0
#define SW_SHUTDOWN_REQ_MASK               0x01

/* Bitfields in PPMU_INTERNAL_SHUTDOWN_STATUS */
#define SW_SHUTDOWN_COMPLETE_OFFSET        0
#define SW_SHUTDOWN_COMPLETE_MASK          0x01

/* Bitfields in PPMU_INTERNAL_SHUTDOWN_ACK */
#define SW_SHUTDOWN_ACK_OFFSET             0
#define SW_SHUTDOWN_ACK_MASK               0x01

/* Bitfields in PPMU_CLOCK_GATING_CONTROL */
#define CLOCK_DISABLE_OFFSET               0
#define CLOCK_DISABLE_MASK                 0x01

#define CLOCK_DIVIDER_OFFSET               8
#define CLOCK_DIVIDER_MASK                 0x0f

/* Bitfields in MEM_POWER_MODE */
#define RETENTION_MODE_OFFSET              0
#define RETENTION_MODE_MASK                0x01

#define POWER_DOWN_MODE_OFFSET             1
#define POWER_DOWN_MODE_MASK               0x01

/* Bitfields in MEM_POWER_UP_READY */
#define PRN_0_MODE_OFFSET                  0
#define PRN_0_MODE_MASK                    0x01

#define PRN_1_MODE_OFFSET                  1
#define PRN_1_MODE_MASK                    0x01

#define PRN_2_MODE_OFFSET                  2
#define PRN_2_MODE_MASK                    0x01

#define PRN_3_MODE_OFFSET                  3
#define PRN_3_MODE_MASK                    0x01

/* Bitfields in GLOBAL_SYNC_CONTROL */
#define SYNC_DELAY_OFFSET                  0
#define SYNC_DELAY_MASK                    0x3f

/* Bitfields in GLOBAL_SYNC_CONTROL */
#define THROTTLE_CLOCK_DIVIDER_0_OFFSET    0
#define THROTTLE_CLOCK_DIVIDER_0_MASK      0xff

#define THROTTLE_CLOCK_DIVIDER_1_OFFSET    8
#define THROTTLE_CLOCK_DIVIDER_1_MASK      0xff

#define THROTTLE_CLOCK_DIVIDER_2_OFFSET    16
#define THROTTLE_CLOCK_DIVIDER_2_MASK      0xff

#define THROTTLE_CLOCK_DIVIDER_3_OFFSET    24
#define THROTTLE_CLOCK_DIVIDER_3_MASK      0xff


/* Control macros */
#define CLOCK_GATE_OFF                   0x0
#define CLOCK_GATE_ON                    0x1


/* Common registers offset */
typedef struct {
    reg32_t ppmu_reset_control[8];          // 0x000 - Partition Power Management Reset Control Registers
    reg32_t ppmu_reset_timing_control[8];   // 0x020 - Partition Power Management Reset Timing Control Registers
    reg32_t ppmu_status;                    // 0x040 - Partition Power Management Reset Status Register
    reg32_t ppmu_isolation_control;         // 0x044 - Partition Power Management NoC Isolation Control Register
    reg32_t ppmu_isolation_status[4];       // 0x048 - Partition Power Management NoC Isolation Status Registers
    reg32_t ppmu_internal_shutdown_control; // 0x058 - Partition Power Management Shutdown Control Register
    reg32_t ppmu_internal_shutdown_status;  // 0x05c - Partition Power Management Shutdown Status Register
    reg32_t ppmu_internal_shutdown_ack;     // 0x060 - Partition Power Management Shutdown Acknowledgement Register
    reg32_t ppmu_clock_gating_control[8];   // 0x064 - Partition 0 Power Management Root Clock Gate Control Register
    reg32_t mem_power_mode[4];              // 0x090 - Memory Power Mode Control Registers
    reg32_t mem_power_up_ready;             // 0x094 - Memory Operation Ready Status Register
    reg32_t global_sync_control;            // 0x098 - High Precision Sync Delay Control Register
    reg32_t throttle_control;               // 0x09c - Clock Throttle Control
} pctl_regs;

enum pctrl_fsm {            //  <fsm1> //  <fsm0> // RST_N   // CLK
    PPMU_FSM_RESETHW   = 8, //     1   //     0   //   0     //   0
    PPMU_FSM_PRE_RST_0 = 2, //     0   //     0   //   1     //   0
    PPMU_FSM_PRE_RST_1 = 0, //     0   //     0   //   0     //   0
    PPMU_FSM_PRE_RST_2 = 1, //     0   //     0   //   0     //   1
    PPMU_FSM_RESET     = 4, //     0   //     1   //   0     //   0
    PPMU_FSM_PRE_REL   = 6, //     0   //     1   //   1     //   0
    PPMU_FSM_ACTIVE    = 7  //     0   //     1   //   1     //   1
};

// PPMU_RESET_TIMING_CONTROL register fields
typedef struct {
    uint8_t pre_rst_0_cycles; // Number of cycles to wait before the first reset state.
    uint8_t pre_rst_1_cycles; // Number of cycles to wait before the second reset state.
    uint8_t pre_rst_2_cycles; // Number of cycles to wait before the third reset state.
    uint8_t pre_rel_cycles;   // Number of cycles to wait before the release state.
} ppmu_timing_control;


/**
 * @brief Retrieves the FSM state of the specified PPMU.
 * 
 * This function returns the finite state machine (FSM) state of the specified 
 * PPMU (Partition Power Management Unit) identified by its index.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the PPMU to check, valid range: 0 to 7.
 * @return The FSM state of the specified PPMU, which can range from reset 
 *         state to active state, as well as intermediate states.
 */
uint32_t pctlResetStatus(pctl_regs* pctl_regs, unsigned int num);

/**
 * @brief Removes the reset associated with the specified PPMU.
 * 
 * This function transitions the num'th PPMU (Partition Power Management Unit) 
 * to an active state, enabling the associated partition to operate normally.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the PPMU for which to remove reset, valid range: 0 to 7.
 * @return Returns 0 on successful removal of the reset, or a negative error code if the operation fails.
 */
int pctlResetRemove(pctl_regs* pctl_regs, unsigned int num);

/**
 * @brief Activates the reset associated with the specified PPMU.
 * 
 * This function sets the num'th PPMU (Partition Power Management Unit) 
 * to a reset state, disabling operation for the associated partition.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the PPMU for which to activate the reset state, valid range: 0 to 7.
 * @return Returns 0 on successful activation of the reset, or a negative error code if the operation fails.
 */
int pctlResetActivate(pctl_regs* pctl_regs, unsigned int num);

/**
 * @brief Sets the wait cycles before each FSM state for the specified PPMU.
 * 
 * This function configures the number of cycles to wait before each transitional FSM state
 * in the num'th PPMU (Partition Power Management Unit).
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the PPMU to configure, valid range: 0 to 7.
 * @param[in] timing_config Reset timing configuration to set
 */
void pctlSetTiming(pctl_regs* pctl_regs, unsigned int num, ppmu_timing_control * timing_control);

/**
 * @brief Get the wait cycles before each FSM state for the specified PPMU.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the PPMU to read from, valid range: 0 to 7.
 * @param[out] timing_config Current reset timing configuration
 */
void pctlGetTiming(pctl_regs* pctl_regs, unsigned int num, ppmu_timing_control *timing_config);

/**
 * @brief Activates or removes clock gating for the specified Clock Divider.
 * 
 * This function controls the clock gating of the num'th Clock Divider. 
 * When clock gating is active, the clock signal is disabled (gated); 
 * when clock gating is removed, the clock signal passes through.
 * 
 * @param[in] num Index of the Clock Divider to control, ranging from 0 to 7.
 * @param[in] control Clock gating control flag:
 *                    - 0: Passes through the clock (disables gating)
 *                    - 1: Gates the clock (enables gating)
 */
void pctlClockGate(pctl_regs* pctl_regs, unsigned int num, uint32_t control);

/**
 * @brief Sets the clock divider value for the specified Clock Divider.
 * 
 * This function configures the clock divider value for the num'th Clock Divider, 
 * maintaining the current clock gating state. The divider setting will take 
 * effect when the clock is not gated.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the Clock Divider to configure, valid range: 0 to 7.
 * @param[in] div Divider value to set, specified as a 6-bit unsigned integer. 
 *                Valid range: 0 to 63.
 */
void pctlClockSetDivider(pctl_regs* pctl_regs, unsigned int num, uint32_t div);

/**
 * @brief Retrieves the status of the specified fence.
 * 
 * This function returns the status of the num'th fence in the PCTL (Partition 
 * Control) instance.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the fence to check, valid range: 0 to 3.
 * @return The status of the specified fence as a 32-bit unsigned integer.
 */
uint32_t pctlFenceStatus(pctl_regs* pctl_regs, unsigned int num);

/**
 * @brief Removes the specified fence.
 * 
 * This function removes the num'th fence in the PCTL (Partition Control) 
 * instance, clearing any restrictions imposed by the fence.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the fence to remove, valid range: 0 to 4.
 * @return Returns 0 on successful removal of the fence, or a negative error code if the operation fails.
 */
int pctlFenceRemove(pctl_regs* pctl_regs, unsigned int num);

/**
 * @brief Activates the specified fence.
 * 
 * This function activates the num'th fence in the PCTL (Partition Control) 
 * instance, imposing AXI access restrictions for the block associated with the specified PCTL.
 * 
 * @param[in] pctl_regs Pointer to the base of the PCTL instance.
 * @param[in] num Index of the fence to activate, valid range: 0 to 4.
 * @return Returns 0 on successful activation of the fence, or a negative error code if the operation fails.
 */
int pctlFenceActivate(pctl_regs* pctl_regs, unsigned int num);
