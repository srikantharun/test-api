/*
------------------------------------------------------------------------
--
// ------------------------------------------------------------------------------
// 
// Copyright 2002 - 2020 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// 
// Component Name   : DW_apb_timers
// Component Version: 2.13a
// Release Type     : GA
// ------------------------------------------------------------------------------

// 
// Release version :  2.13a
// File Version     :        $Revision: #1 $ 
// Revision: $Id: //dwh/DW_ocb/DW_apb_timers/amba_dev/src/DW_apb_timers_cc_constants.vh#1 $ 
--
-- File         : DW_apb_timers_cc_constants.vh
//
//
-- Abstract     : Configuration Parameters for DW_apb_timers 
--
------------------------------------------------------------------------
*/
//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef soc_periph_dw_timers___GUARD__DW_APB_TIMERS_CC_CONSTANTS__VH__
`define soc_periph_dw_timers___GUARD__DW_APB_TIMERS_CC_CONSTANTS__VH__



// Name:         SLAVE_INTERFACE_TYPE
// Default:      APB2
// Values:       APB2 (0), APB3 (1), APB4 (2)
// 
// Selects Register Interface type as APB2, APB3 or APB4. 
// By default, DW_apb_timers supports APB2 interface.
`define soc_periph_dw_timers_SLAVE_INTERFACE_TYPE 2


// Name:         SLVERR_RESP_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1
// 
// Enables Slave Error response signaling. The component will refrain 
// From signaling an error response if this parameter is disabled.
`define soc_periph_dw_timers_SLVERR_RESP_EN 0

//APB Interface has APB3 signals

`define soc_periph_dw_timers_TIMERS_HAS_APB3_IF_SIGNALS

//APB Interface has APB4 signals

`define soc_periph_dw_timers_TIMERS_HAS_APB4_IF_SIGNALS

//Component has slave error response enabled

// `define soc_periph_dw_timers_TIMERS_HAS_SLVERR_RESP_EN
 

// Name:         PROT_LEVEL_RST
// Default:      0x2
// Values:       0x0, ..., 0x7
// Enabled:      SLAVE_INTERFACE_TYPE>1 && SLVERR_RESP_EN==1
// 
// Reset Value of TIMER_N_PROT_LEVEL register. 
// A high on any bit of timer protection level requires a high on the 
// corresponding pprot input bit to gain access to the load count registers. 
// Else, SLVERR response is triggered. A zero on the protection bit will 
// provide access to the register if other protection levels are satisfied.
`define soc_periph_dw_timers_PROT_LEVEL_RST 3'h2


// Name:         HC_PROT_LEVEL
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1 && SLVERR_RESP_EN==1
// 
// Checking this parameter makes TIMERS_N_PROT_LEVEL a read-only register, 
// reflecting default PROT_LEVEL_RST when read. 
// The register can be programmed at run-time by a user if this 
// hard-code option is turned off.
`define soc_periph_dw_timers_HC_PROT_LEVEL 0

//Component has hard-coded protection level enabled

// `define soc_periph_dw_timers_TIMERS_HAS_PROT_HC

//Component has protection functionality enabled

// `define soc_periph_dw_timers_TIMERS_HAS_PROT_FN


// Name:         APB_DATA_WIDTH
// Default:      32
// Values:       8 16 32
// 
// Width of the APB data bus to which this component is attached.
`define soc_periph_dw_timers_APB_DATA_WIDTH 32


`define soc_periph_dw_timers_APB_DW_EQ_32


// `define soc_periph_dw_timers_APB_DW_EQ_16


// `define soc_periph_dw_timers_APB_DW_EQ_8


// Name:         TIM_NEWMODE
// Default:      false
// Values:       false (0), true (1)
// Enabled:      APB_DATA_WIDTH==32
// 
// When set to True (1), this parameter enables the following features in all the timers: 
//  - If TimerNControlReg[4] is set to 1, the width of LOW and HIGH periods of timer toggle outputs can be separately 
//  programmed through TimerNLoadCount and TimerNLoadCount2 registers, respectively. 
//  - Timer_N_clk can be free-running; that is, timer_n_clk does not have to be stopped when timer is disabled. 
//  - Timer interrupt can be detected, even when pclk is stopped. 
//  - Timer can be paused using timer_N_pause inputs.
// `define soc_periph_dw_timers_TIM_NEWMODE


`define soc_periph_dw_timers_TIM_NEWMODE_VAL 0


// Name:         INTR_SYNC2PCLK
// Default:      Timer clock (timer_clk)
// Values:       Timer clock (timer_clk) (0), system clock (pclk) (1)
// Enabled:      TIM_NEWMODE==1
// 
// When TIM_NEWMODE is enabled, the timer interrupt can be generated 
// either in the system clock (pclk) or in the Timer clock (timer_clk) domain. When set to 
// 0, the timer interrupt is generated in the Timer clock domain; when set to 1, the timer 
// interrupt is generated in the system clock domain.
`define soc_periph_dw_timers_INTR_SYNC2PCLK 0


// `define soc_periph_dw_timers_INTR_SYNC2PCLK_EN


// Name:         TIM_0N100_PWM_MODE
// Default:      false
// Values:       false (0), true (1)
// Enabled:      ((TIMER_HAS_TOGGLE_1 == 1) || (TIMER_HAS_TOGGLE_2 == 1) || 
//               (TIMER_HAS_TOGGLE_3 == 1) || (TIMER_HAS_TOGGLE_4 == 1) || (TIMER_HAS_TOGGLE_5 
//               == 1) || (TIMER_HAS_TOGGLE_6 == 1) || (TIMER_HAS_TOGGLE_7 == 1) || 
//               (TIMER_HAS_TOGGLE_8 == 1)) && (TIM_NEWMODE_VAL == 1)
// 
// When set to True (1), this parameter enables the 0% and 100% PWM mode on the  
// toggle output. This feature adds 1-bit to the TimerNControlReg as follows: 
//   TimerNControlReg[4] - Timer 0% and 100% duty cycle Mode Enable
`define soc_periph_dw_timers_TIM_0N100_PWM_MODE 0


// Name:         TIM_HAS_0N100_PWM_MODE
// Default:      0 ( (TIM_0N100_PWM_MODE==1) ? 1 : 0)
// Values:       0, 1
// 
// Timer has 0% and 100% PWM mode enabled
// `define soc_periph_dw_timers_TIM_HAS_0N100_PWM_MODE


// Name:         TIMER_0N100_PWM_HC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      TIM_0N100_PWM_MODE == 1
// 
// When set to True (1), this parameter hardcodes the 0% and 100% PWM mode enable bit in the  
// TimerNControlReg in the register. This is provided to reduce the software overhead.
`define soc_periph_dw_timers_TIMER_0N100_PWM_HC_EN 0


// `define soc_periph_dw_timers_TIMER_HAS_0N100_PWM_HC_EN


// Name:         NUM_TIMERS
// Default:      2
// Values:       1 2 3 4 5 6 7 8
// 
// Number of timers to instantiate in DW_apb_timers. Up to eight timers can be instantiated.
`define soc_periph_dw_timers_NUM_TIMERS 2


`define soc_periph_dw_timers_NUM_TIMERS_GTE_1


`define soc_periph_dw_timers_NUM_TIMERS_GTE_2


// `define soc_periph_dw_timers_NUM_TIMERS_GTE_3


// `define soc_periph_dw_timers_NUM_TIMERS_GTE_4


// `define soc_periph_dw_timers_NUM_TIMERS_GTE_5


// `define soc_periph_dw_timers_NUM_TIMERS_GTE_6


// `define soc_periph_dw_timers_NUM_TIMERS_GTE_7


// `define soc_periph_dw_timers_NUM_TIMERS_GTE_8

//Polarity of interrupt signals generated by DW_apb_timers

// Name:         TIM_INTRPT_PLRITY
// Default:      Active High
// Values:       Active Low (0), Active High (1)
// Enabled:      TIM_NEWMODE==0
// 
// Polarity of interrupt signals generated by DW_apb_timers.
`define soc_periph_dw_timers_TIM_INTRPT_PLRITY 1


// Name:         TIM_INTR_IO
// Default:      false
// Values:       false (0), true (1)
// Enabled:      TIM_NEWMODE==0
// 
// When set to True (1), the component generates a single interrupt 
// combining all timer interrupts. If set to False (0), the component generates an interrupt 
// output for each timer.
`define soc_periph_dw_timers_TIM_INTR_IO 0


// Name:         TIMER_WIDTH_1
// Default:      32
// Values:       8, ..., 32
// 
// Width of each Timer.
`define soc_periph_dw_timers_TIMER_WIDTH_1 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_1 32'h0


// Name:         TIMER_HAS_TOGGLE_1
// Default:      false
// Values:       false (0), true (1)
// 
// When set to True (1), the interface includes an output (timer_N_toggle) 
// that toggles each time the timer counter reloads. The output is disabled to 0 each time 
// the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_1 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_1


// Name:         TIM_METASTABLE_1
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0
// 
// This option instantiates metastability registers to synchronize timer 
// interrupt signals to the pclk domain. Set this to Present (1) if timer_N_clk is independent 
// of pclk. If this parameter is set to Absent (0), then timer_N_clk is considered to be 
// connected to or synchronous with pclk.
`define soc_periph_dw_timers_TIM_METASTABLE_1 0


// Name:         TIM_SYNC_DEPTH_1
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_1==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_1 2


// Name:         TIM_PULSE_EXTD_1
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0
// 
// If this timer clock is faster than the system bus clock, you can extend the 
// internal interrupt by up to three timer clock cycles to guarantee that it is seen in the bus 
// clock domain. A 0 value in this field means that no pulse extension is performed. Also 
// refer to the "Controlling Clock Boundaries and Metastability" section in the DW_apb_timers databook. 
//  
// Set this parameter to the following values, depending on the timer_N_clk/pclk frequency ratio R: 
//  
// timer_N_clk/pclk frequency R    PULSE_EXTEND_N  
//  
//          R<=1    ---------------------------------  0        
//                 
//          1<R<=2  ------------------------------     1        
//                 
//          2<R<=3  ------------------------------     2        
//                 
//          3<R<=4  ------------------------------     3        
//                 
//          R>4     ---------------------------------  Not Valid
`define soc_periph_dw_timers_TIM_PULSE_EXTD_1 0


// Name:         TIM_COHERENCY_1
// Default:      false
// Values:       false (0), true (1)
// Enabled:      APB_DATA_WIDTH < TIMER_WIDTH_1
// 
// When set to True (1), a bank of registers is added between this timer and 
// the APB interface of DW_apb_timers to guarantee that the timer value read back from 
// this block is coherent. It does not reflect ongoing changes in the timer value that takes 
// place while the read operation is in progress. 
//  
// Note: Including coherency can dramatically increase the register count of the design.
`define soc_periph_dw_timers_TIM_COHERENCY_1 0
 

`define soc_periph_dw_timers_TIMER_COH_WIDTH_1 0


// Name:         TIMER_WIDTH_2
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 1
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_2 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_2 32'h0


// Name:         TIMER_HAS_TOGGLE_2
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 1
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_2 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_2


// Name:         TIM_METASTABLE_2
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 1
// 
// Set this parameter to "Present" if you 
// want metastability flops instantiated on this timer's internal interrupt flag 
// on the boundary between this timer's clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_2 0


// Name:         TIM_SYNC_DEPTH_2
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_2==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_2 2


// Name:         TIM_PULSE_EXTD_2
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 1
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_2 0


// Name:         TIM_COHERENCY_2
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 2 && APB_DATA_WIDTH < TIMER_WIDTH_2
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_2 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_2 0


// Name:         TIMER_WIDTH_3
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 2
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_3 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_3 32'h0


// Name:         TIMER_HAS_TOGGLE_3
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 2
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_3 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_3


// Name:         TIM_METASTABLE_3
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 2
// 
// Set this parameter to "Present" if you 
// want metastability flops instantiated on this timer's internal interrupt flag 
// on the boundary between this timer's clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_3 0


// Name:         TIM_SYNC_DEPTH_3
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_3==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_3 2


// Name:         TIM_PULSE_EXTD_3
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 2
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_3 0


// Name:         TIM_COHERENCY_3
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 3 && APB_DATA_WIDTH < TIMER_WIDTH_3
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_3 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_3 0


// Name:         TIMER_WIDTH_4
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 3
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_4 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_4 32'h0


// Name:         TIMER_HAS_TOGGLE_4
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 3
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_4 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_4


// Name:         TIM_METASTABLE_4
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 3
// 
// Set this parameter to "Present" if you 
// want metastability flops instantiated on this timer's internal interrupt flag 
// on the boundary between this timer's clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_4 0


// Name:         TIM_SYNC_DEPTH_4
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_4==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_4 2


// Name:         TIM_PULSE_EXTD_4
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 3
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_4 0


// Name:         TIM_COHERENCY_4
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 4 && APB_DATA_WIDTH < TIMER_WIDTH_4
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_4 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_4 0


// Name:         TIMER_WIDTH_5
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 4
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_5 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_5 32'h0


// Name:         TIMER_HAS_TOGGLE_5
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 4
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_5 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_5


// Name:         TIM_METASTABLE_5
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 4
// 
// Set this parameter to "Present" if you 
// want metastability flops instantiated on this timer's internal interrupt flag 
// on the boundary between this timer's clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_5 0


// Name:         TIM_SYNC_DEPTH_5
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_5==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_5 2


// Name:         TIM_PULSE_EXTD_5
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 4
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_5 0


// Name:         TIM_COHERENCY_5
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 5 && APB_DATA_WIDTH < TIMER_WIDTH_5
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_5 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_5 0


// Name:         TIMER_WIDTH_6
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 5
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_6 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_6 32'h0


// Name:         TIMER_HAS_TOGGLE_6
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 5
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_6 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_6


// Name:         TIM_METASTABLE_6
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 5
// 
// Set this parameter to "Present" if you want metastability flops instantiated  
// on this timer's internal interrupt flag on the boundary between this timer's  
// clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_6 0


// Name:         TIM_SYNC_DEPTH_6
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_6==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_6 2


// Name:         TIM_PULSE_EXTD_6
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 5
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_6 0


// Name:         TIM_COHERENCY_6
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 6 && APB_DATA_WIDTH < TIMER_WIDTH_6
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_6 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_6 0


// Name:         TIMER_WIDTH_7
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 6
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_7 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_7 32'h0


// Name:         TIMER_HAS_TOGGLE_7
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 6
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_7 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_7


// Name:         TIM_METASTABLE_7
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 6
// 
// Set this parameter to "Present" if you 
// want metastability flops instantiated on this timer's internal interrupt flag 
// on the boundary between this timer's clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_7 0


// Name:         TIM_SYNC_DEPTH_7
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_7==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_7 2


// Name:         TIM_PULSE_EXTD_7
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 6
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_7 0


// Name:         TIM_COHERENCY_7
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 7 && APB_DATA_WIDTH < TIMER_WIDTH_7
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_7 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_7 0


// Name:         TIMER_WIDTH_8
// Default:      32
// Values:       8, ..., 32
// Enabled:      NUM_TIMERS > 7
// 
// Width of Timer 
// Timers can be between 8 and 32 bits wide (inclusive).
`define soc_periph_dw_timers_TIMER_WIDTH_8 32


`define soc_periph_dw_timers_TIM_RST_CURRENTVAL_8 32'h0


// Name:         TIMER_HAS_TOGGLE_8
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS > 7
// 
// Include an output which toggles each time the counter reloads. 
// Disabled to zero each time the timer is disabled.
`define soc_periph_dw_timers_TIMER_HAS_TOGGLE_8 0


// `define soc_periph_dw_timers_TIM_HAS_TOGGLE_8


// Name:         TIM_METASTABLE_8
// Default:      Absent (TIM_NEWMODE)
// Values:       Absent (0), Present (1)
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 7
// 
// Set this parameter to "Present" if you 
// want metastability flops instantiated on this timer's internal interrupt flag 
// on the boundary between this timer's clock and the bus clock domain.
`define soc_periph_dw_timers_TIM_METASTABLE_8 0


// Name:         TIM_SYNC_DEPTH_8
// Default:      2
// Values:       2 3 4
// Enabled:      TIM_METASTABLE_8==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals for timer N. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_timers_TIM_SYNC_DEPTH_8 2


// Name:         TIM_PULSE_EXTD_8
// Default:      0
// Values:       0 1 2 3
// Enabled:      TIM_NEWMODE==0 && NUM_TIMERS > 7
// 
// Pulse Extension Control 
// If this timer's clock is faster than the system bus clock, you can extend 
// the internal interrupt flag by up to three timer clock cycles to guarantee 
// that it is seen in the bus clock domain.  A zero value in this field means 
// that no pulse extension is to be performed.
`define soc_periph_dw_timers_TIM_PULSE_EXTD_8 0


// Name:         TIM_COHERENCY_8
// Default:      false
// Values:       false (0), true (1)
// Enabled:      NUM_TIMERS >= 8 && APB_DATA_WIDTH < TIMER_WIDTH_8
// 
// Adds a bank of registers between 
// this timer and the APB interface of DW_apb_timers to guarantee that 
// the timer value read back from this block is coherent - i.e. it does 
// not reflect ongoing changes in the timer's value which take place while 
// the read operation is in progress.  Note that including coherency can 
// dramatically increase the register count of the design. Note also 
// that coherency will not be implemented if the timer width is less 
// than or equal to the APB Data Width
`define soc_periph_dw_timers_TIM_COHERENCY_8 0


`define soc_periph_dw_timers_TIMER_COH_WIDTH_8 0


`define soc_periph_dw_timers_TOTAL_COH_WIDTH 0


`define soc_periph_dw_timers_TIM_VERIF_EN 1


`define soc_periph_dw_timers_TIM_ADDR_SLICE_RHS 2

//TIM_ADDR_SLICE_LHS: MSB of decoded address

`define soc_periph_dw_timers_TIM_ADDR_SLICE_LHS 7

//Width of DW_apb_timers' Write Data Bus.
//If the APB Data Bus Width configured above is wider than the widest timer, 
//this component will have a Write Data Bus Width equal to the width of the
//widest timer.  If the APB Data Bus Width is narrower than the widest
//timer, the component's Write Data Bus width will equal that of the APB
//Data Bus.

`define soc_periph_dw_timers_TIM_WDATA_WIDTH 32

//Width of DW_apb_timers' Read Data Bus
//This is equal to the component's Write Data Bus width.

`define soc_periph_dw_timers_TIM_RDATA_WIDTH 32

//Bits to decode on paddr

`define soc_periph_dw_timers_MAX_APB_DATA_WIDTH 32


`define soc_periph_dw_timers_TIM_CTL_WIDTH 3


// `define soc_periph_dw_timers_TIM_RC_1


// `define soc_periph_dw_timers_TIM_RC_2


// `define soc_periph_dw_timers_TIM_RC_3


// `define soc_periph_dw_timers_TIM_RC_4


// `define soc_periph_dw_timers_TIM_RC_5


// `define soc_periph_dw_timers_TIM_RC_6


// `define soc_periph_dw_timers_TIM_RC_7


// `define soc_periph_dw_timers_TIM_RC_8


`define soc_periph_dw_timers_TIM_FREE_RUNNING 0


`define soc_periph_dw_timers_TIM_USER_DEFINED 1


`define soc_periph_dw_timers_TIM_MAX_TIMERS 8


`define soc_periph_dw_timers_MAX_CURRVALUE_WIDTH 256


`define soc_periph_dw_timers_TIM1_CV_INDEX 32


`define soc_periph_dw_timers_TIM2_CV_INDEX 64


`define soc_periph_dw_timers_TIM3_CV_INDEX 96


`define soc_periph_dw_timers_TIM4_CV_INDEX 128


`define soc_periph_dw_timers_TIM5_CV_INDEX 160


`define soc_periph_dw_timers_TIM6_CV_INDEX 192


`define soc_periph_dw_timers_TIM7_CV_INDEX 224


`define soc_periph_dw_timers_TIM8_CV_INDEX 256


`define soc_periph_dw_timers_COH_INDEX_1 0


`define soc_periph_dw_timers_COH_INDEX_2 0


`define soc_periph_dw_timers_COH_INDEX_3 0


`define soc_periph_dw_timers_COH_INDEX_4 0


`define soc_periph_dw_timers_COH_INDEX_5 0


`define soc_periph_dw_timers_COH_INDEX_6 0


`define soc_periph_dw_timers_COH_INDEX_7 0


`define soc_periph_dw_timers_COH_INDEX_8 0


`define soc_periph_dw_timers_NUM_TIMERS_WIDTH 64

//TIM_INDIVIDUAL: Individual Timer Interrupts used

`define soc_periph_dw_timers_TIM_INDIVIDUAL 0

//TIM_COMBINED: Combined (Single) Timer Interrupt used

`define soc_periph_dw_timers_TIM_COMBINED 1

//Creates a define to check TIM_INTRPT_PLRITY is 1 

`define soc_periph_dw_timers_TIM_INTRPT_PLRITY_1

//Creates a define to check TIM_INTR_IO is equal TIM_INDIVIDUAL  is 1 

`define soc_periph_dw_timers_TIM_INTR_IO_EQUAL_TIM_INDIVIDUAL

//Creates a define to check TIM_INTR_IO is equal TIM_COMBINED is 1 

// `define soc_periph_dw_timers_TIM_INTR_IO_EQUAL_TIM_COMBINED

//Creates a define the timer contains timer_1_pause

// `define soc_periph_dw_timers_TIMER_1_PAUSE

//Creates a define the timer contains timer_2_pause

// `define soc_periph_dw_timers_TIMER_2_PAUSE

//Creates a define the timer contains timer_3_pause

// `define soc_periph_dw_timers_TIMER_3_PAUSE

//Creates a define the timer contains timer_4_pause

// `define soc_periph_dw_timers_TIMER_4_PAUSE

//Creates a define the timer contains timer_5_pause

// `define soc_periph_dw_timers_TIMER_5_PAUSE

//Creates a define the timer contains timer_6_pause

// `define soc_periph_dw_timers_TIMER_6_PAUSE

//Creates a define the timer contains timer_7_pause

// `define soc_periph_dw_timers_TIMER_7_PAUSE

//Creates a define the timer contains timer_8_pause

// `define soc_periph_dw_timers_TIMER_8_PAUSE









//Each corekit has a version number.
//This is relected in the ascii version number which needs to get translated.
//0 => 48 -> 30
//1 => 49 -> 31
//2 => 50 -> 32
//A => 65 -> 41
//B => 66 -> 42
//C => 67 -> 43
//
//Current Version is 2.13* => 32_31_33_2A
//

`define soc_periph_dw_timers_TIM_VERSION_ID 32'h3231332a

//Setting up a clock period for the Timers.

`define soc_periph_dw_timers_TIM_CLK_PERIOD 200

//Random seed used in the testbench

`define soc_periph_dw_timers_SIM_RAND_SEED 1


//Used to insert internal tests

//**************************************************************************************************
// Parameters to remove init and test ports in bcm
//**************************************************************************************************


`define soc_periph_dw_timers_DWC_NO_TST_MODE

`define soc_periph_dw_timers_DWC_NO_CDC_INIT

//==============================================================================
// End Guard
//==============================================================================
 `endif

