/*
--------------------------------------------------------------------------
// ------------------------------------------------------------------------------
//
// Copyright 2013 - 2024 Synopsys, INC.
//
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
//
// Component Name   : DW_axi_dmac
// Component Version: 2.03a
// Release Type     : GA
// Build ID         : 39.65.47.15
// ------------------------------------------------------------------------------

//
// Release version :  2.03a
// Revision: $Id: //dwh/DW_ocb/DW_axi_dmac/amba_sfty_dev_br/src/DW_axi_dmac_cc_constants.vh#11 $
//
-- File :                       DW_axi_dmac_cc_constants.vh
-- Abstract     :               CoreConsultant constants file
--------------------------------------------------------------------------

*/

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef APU___GUARD__DW_AXI_DMAC_CC_CONSTANTS__VH__
`define APU___GUARD__DW_AXI_DMAC_CC_CONSTANTS__VH__


// Name:         DMAX_ID_NUM
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
//
// A 32-bit value that is hardwired and read back by a read to the DW_axi_dmac ID Register (DMAC_IDReg).
`define APU_DMAX_ID_NUM 32'h0

//A 32-bit value that is hardwired and read back by a read to the DW_axi_dmac Component Version Register.

`define APU_DMAX_COMP_VER 32'h3230332a


// Name:         DMAX_NUM_CHANNELS
// Default:      1
// Values:       1, ..., 32
//
// Creates the specified number of DW_axi_dmac channels, each of which is unidirectional and transfers data from the
// channel source to the channel destination. The channel source and destination AXI layer, system address, and handshaking
// interface are under software control.
`define APU_DMAX_NUM_CHANNELS 2


// Name:         DMAX_MSTIF_MODE
// Default:      AXI3
// Values:       AXI3 (0), AXI4 (1)
//
// The protocol used for the AXI Manager Interface.
`define APU_DMAX_MSTIF_MODE 1


// Name:         DMAX_HAS_QOS
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_MSTIF_MODE==1
//
// When set to Yes (1), enables the QoS signals in the AXI4 interface.
`define APU_DMAX_HAS_QOS 0


// Name:         DMAX_NUM_MASTER_IF
// Default:      1
// Values:       1 2
//
// Creates the specified number of AXI manager interfaces. A channel source or destination device can be programmed to be
// on any of the configured AXI layers attached to the AXI manager interface. This setting determines if AXI manager 2
// interface signal set is present on the I/O. AXI manager interface signals are always present.
`define APU_DMAX_NUM_MASTER_IF 1


// Name:         DMAX_SLVIF_MODE
// Default:      AHB
// Values:       AHB (0), APB4 (2)
// Enabled:      Always
//
// The protocol used for Register Bus Interface.
// Only AHB and APB4 is supported in this version.
`define APU_DMAX_SLVIF_MODE 0


// Name:         DMAX_SLVIF_CLOCK_MODE
// Default:      Synchronous
// Values:       Synchronous (0), Asynchronous (1)
// Enabled:      DMAX_LS_PROT_EN==0
//
// Selects the relationship between the register bus interface clock (AHB/APB4) and the Core clock.
//  - 0: Register Bus interface clock is synchronous to the core clock.
//  - 1: Register Bus interface clock is asynchronous to the core clock.
`define APU_DMAX_SLVIF_CLOCK_MODE 0


`define APU_DMAX_APB3_APB4 0


// Name:         DMAX_S_2_C_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_SLVIF_CLOCK_MODE==1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac Register Bus Interface
// clock domain to the DW_axi_dmac Core Clock domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge.
`define APU_DMAX_S_2_C_SYNC_DEPTH 2


// Name:         DMAX_C_2_S_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_SLVIF_CLOCK_MODE==1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac Core Clock Domain to the
// Register Bus Interface clock domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge.
`define APU_DMAX_C_2_S_SYNC_DEPTH 2


// Name:         DMAX_MSTIF1_CLOCK_MODE
// Default:      Synchronous
// Values:       Synchronous (0), Asynchronous (1)
// Enabled:      DMAX_LS_PROT_EN==0
//
// Selects the relationship between the Manager i Interface clock (aclk_m(i)) and the Core clock.
//  - 0: Manager i interface clock is synchronous to the core clock.
//  - 1: Manager i interface clock is asynchronous to the core clock.
`define APU_DMAX_MSTIF1_CLOCK_MODE 0


// Name:         DMAX_M1_2_C_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_MSTIF1_CLOCK_MODE==1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac Manager i clock domain to
// the DW_axi_dmac Core Clock domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge.
`define APU_DMAX_M1_2_C_SYNC_DEPTH 2


// Name:         DMAX_C_2_M1_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_MSTIF1_CLOCK_MODE==1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac Core Clock domain to the
// Manager i clock domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge.
`define APU_DMAX_C_2_M1_SYNC_DEPTH 2


// Name:         DMAX_MSTIF2_CLOCK_MODE
// Default:      Synchronous
// Values:       Synchronous (0), Asynchronous (1)
// Enabled:      (DMAX_NUM_MASTER_IF > 1) && (DMAX_LS_PROT_EN==0)
//
// Selects the relationship between the Manager 2 Interface clock (aclk_m2) and Core clock.
//  - 0: Manager 2 Interface clock is synchronous to core clock.
//  - 1: Manager 2 Interface clock is asynchronous to core clock.
`define APU_DMAX_MSTIF2_CLOCK_MODE 0


// Name:         DMAX_M2_2_C_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_MSTIF2_CLOCK_MODE==1 && DMAX_NUM_MASTER_IF > 1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac DW_axi_dmac Core Clock
// Domain to Manager 2 clock domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge.
`define APU_DMAX_M2_2_C_SYNC_DEPTH 2


// Name:         DMAX_C_2_M2_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_MSTIF2_CLOCK_MODE==1 && DMAX_NUM_MASTER_IF > 1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac Manager 2 clock domain to
// DW_axi_dmac Core Clock Domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge
`define APU_DMAX_C_2_M2_SYNC_DEPTH 2


// Name:         DMAX_UNALIGNED_XFER_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), this parameter enables the unaligned
// transfer support on CHx_SAR and CHx_DAR. This reduces the software
// overhead of converting the unaligned address to aligned address.
`define APU_DMAX_UNALIGNED_XFER_EN 1


// Name:         DMAX_ARB_TYPE
// Default:      Dynamic Priority Arbitration with Fair-Among-Equals
// Values:       Dynamic Priority Arbitration with Fair-Among-Equals (0), Dynamic
//               Priority Arbitration with Round Robin (1)
// Enabled:      DMAX_NUM_CHANNELS > 1
//
// This parameter allows user to configure the arbitration type:
//  - Dynamic Priority Arbitration with Fair-Among-Equals
//  - Dynamic Priority Arbitration with Round Robin
//  User can configure Dynamic Priority as first-tier arbitration
//  with option to have second-tier arbitration as "Fair Among Equals" or
//  "Round Robin".
`define APU_DMAX_ARB_TYPE 0


// Name:         DMAX_ARB_TIMING_OPT
// Default:      No ((DMAX_ARB_TYPE==1) ? 1 : 0)
// Values:       No (0), Yes (1)
// Enabled:      DMAX_ARB_TYPE == 1
//
// This parameter allows user to Enable the Timing Optimization of the Arbiter Logic.
// This feature will enable the timing optmization with the following :
//  - Number of Channel requests to Arbiter are optimized.
//  - The BCM01 is split into multiple stages to improve the timing.
`define APU_DMAX_ARB_TIMING_OPT 0


// Name:         DMAX_MULT_ARB_EN
// Default:      No (((DMAX_NUM_CHANNELS>8) && (DMAX_ARB_TYPE == 0)) ? 1 : 0)
// Values:       No (0), Yes (1)
// Enabled:      (DMAX_NUM_CHANNELS>8) && (DMAX_ARB_TYPE == 0)
//
// When set to Yes (1), Multi-arbiter feature is enabled. This feature
// implements the Multiple Stage Arbiter Architecture (Multi-Arbiter) to arbitrate the
// requests from source, destination, and LLI state machine to access an
// AXI Manager interface. Enabling this feature helps to improve the
// QoR for the implemented design.
`define APU_DMAX_MULT_ARB_EN 0


// Name:         DMAX_MSTIF1_OSR_LMT
// Default:      16
// Values:       16 32 48 64 80 96 112 128
//
// The maximum number of active write requests that can be generated by an AXI Manager interface (i) without sending the
// respective write data. This parameter is used to select the depth of a FIFO, which tracks the write data transferred on AXI
// Manager interface for the active AXI write requests.
// Note: AXI outstanding write/read requests on the channel are controlled through the programming registers
// CHx_CFG.SRC_OSR_LMT and CHx_CFG.DST_OSR_LMT.
//  This parameter does not limit the outstanding read requests on the AXI interface.
`define APU_DMAX_MSTIF1_OSR_LMT 32


// Name:         DMAX_MSTIF2_OSR_LMT
// Default:      16
// Values:       16 32 48 64 80 96 112 128
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// The maximum number of active write requests that can be generated by an AXI Manager interface (i) without sending the
// respective write data. This parameter is used to select the depth of a FIFO, which tracks the write data transferred on AXI
// Manager interface for the active AXI write requests.
// Note: AXI outstanding write/read requests on the channel are controlled through the programming registers
// CHx_CFG.SRC_OSR_LMT and CHx_CFG.DST_OSR_LMT.
//  This parameter does not limit the outstanding read requests on the AXI interface.
`define APU_DMAX_MSTIF2_OSR_LMT 16


// Name:         DMAX_NUM_HS_IF
// Default:      2
// Values:       0, ..., 64
//
// Creates the specified number of hardware handshaking interfaces. DW_axi_dmac can be programmed to assign a handshaking
// interface for each channel source and destination. If 0 is selected, then no hardware handshaking signals are present on
// the I/O.
`define APU_DMAX_NUM_HS_IF 0


// Name:         DMAX_ASYNC_HS_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_NUM_HS_IF > 0
//
// When set to Yes (1), allows you to include or exclude asynchronous DMA handshake support.
`define APU_DMAX_ASYNC_HS_EN 0


// Name:         DMAX_HS_SAME_ASYNC_CLK
// Default:      Yes
// Values:       No (0), Yes (1)
// Enabled:      DMAX_ASYNC_HS_EN == 1
//
// When set to Yes (1), configures whether all DMA handshake interface has the same asynchronous clock.
`define APU_DMAX_HS_SAME_ASYNC_CLK 1


// Name:         DMAX_HS_2_C_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_ASYNC_HS_EN==1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac handshake interface clock
// domain to the DW_axi_dmac Core Clock Domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge
`define APU_DMAX_HS_2_C_SYNC_DEPTH 2


// Name:         DMAX_C_2_HS_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      DMAX_ASYNC_HS_EN==1
//
// Defines the number of synchronization register stages for signals passing from the DW_axi_dmac Core Clock domain to
// handshake interface clock domain.
//  - 2: Two-stage synchronization, both stages positive edge.
//  - 3: Three-stage synchronization, all stages positive edge.
//  - 4: Four-stage synchronization, all stages positive edge
`define APU_DMAX_C_2_HS_SYNC_DEPTH 2


// Name:         DMAX_HS1_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 1)
//
// The DMA handshake interface y has asynchronous clock.
`define APU_DMAX_HS1_ASYNC_CLK 1


// Name:         DMAX_HS2_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 2)
//
// The DMA handshake interface 2 has asynchronous clock.
`define APU_DMAX_HS2_ASYNC_CLK 1


// Name:         DMAX_HS3_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 3)
//
// The DMA handshake interface 3 has asynchronous clock.
`define APU_DMAX_HS3_ASYNC_CLK 1


// Name:         DMAX_HS4_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 4)
//
// The DMA handshake interface 4 has asynchronous clock.
`define APU_DMAX_HS4_ASYNC_CLK 1


// Name:         DMAX_HS5_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 5)
//
// The DMA handshake interface 5 has asynchronous clock.
`define APU_DMAX_HS5_ASYNC_CLK 1


// Name:         DMAX_HS6_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 6)
//
// The DMA handshake interface 6 has asynchronous clock.
`define APU_DMAX_HS6_ASYNC_CLK 1


// Name:         DMAX_HS7_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 7)
//
// The DMA handshake interface 7 has asynchronous clock.
`define APU_DMAX_HS7_ASYNC_CLK 1


// Name:         DMAX_HS8_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 8)
//
// The DMA handshake interface 8 has asynchronous clock.
`define APU_DMAX_HS8_ASYNC_CLK 1


// Name:         DMAX_HS9_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 9)
//
// The DMA handshake interface 9 has asynchronous clock.
`define APU_DMAX_HS9_ASYNC_CLK 1


// Name:         DMAX_HS10_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 10)
//
// The DMA handshake interface 10 has asynchronous clock.
`define APU_DMAX_HS10_ASYNC_CLK 1


// Name:         DMAX_HS11_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 11)
//
// The DMA handshake interface 11 has asynchronous clock.
`define APU_DMAX_HS11_ASYNC_CLK 1


// Name:         DMAX_HS12_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 12)
//
// The DMA handshake interface 12 has asynchronous clock.
`define APU_DMAX_HS12_ASYNC_CLK 1


// Name:         DMAX_HS13_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 13)
//
// The DMA handshake interface 13 has asynchronous clock.
`define APU_DMAX_HS13_ASYNC_CLK 1


// Name:         DMAX_HS14_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 14)
//
// The DMA handshake interface 14 has asynchronous clock.
`define APU_DMAX_HS14_ASYNC_CLK 1


// Name:         DMAX_HS15_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 15)
//
// The DMA handshake interface 15 has asynchronous clock.
`define APU_DMAX_HS15_ASYNC_CLK 1


// Name:         DMAX_HS16_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 16)
//
// The DMA handshake interface 16 has asynchronous clock.
`define APU_DMAX_HS16_ASYNC_CLK 1


// Name:         DMAX_HS17_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 17)
//
// The DMA handshake interface 17 has asynchronous clock.
`define APU_DMAX_HS17_ASYNC_CLK 1


// Name:         DMAX_HS18_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 18)
//
// The DMA handshake interface 18 has asynchronous clock.
`define APU_DMAX_HS18_ASYNC_CLK 1


// Name:         DMAX_HS19_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 19)
//
// The DMA handshake interface 19 has asynchronous clock.
`define APU_DMAX_HS19_ASYNC_CLK 1


// Name:         DMAX_HS20_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 20)
//
// The DMA handshake interface 20 has asynchronous clock.
`define APU_DMAX_HS20_ASYNC_CLK 1


// Name:         DMAX_HS21_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 21)
//
// The DMA handshake interface 21 has asynchronous clock.
`define APU_DMAX_HS21_ASYNC_CLK 1


// Name:         DMAX_HS22_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 22)
//
// The DMA handshake interface 22 has asynchronous clock.
`define APU_DMAX_HS22_ASYNC_CLK 1


// Name:         DMAX_HS23_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 23)
//
// The DMA handshake interface 23 has asynchronous clock.
`define APU_DMAX_HS23_ASYNC_CLK 1


// Name:         DMAX_HS24_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 24)
//
// The DMA handshake interface 24 has asynchronous clock.
`define APU_DMAX_HS24_ASYNC_CLK 1


// Name:         DMAX_HS25_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 25)
//
// The DMA handshake interface 25 has asynchronous clock.
`define APU_DMAX_HS25_ASYNC_CLK 1


// Name:         DMAX_HS26_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 26)
//
// The DMA handshake interface 26 has asynchronous clock.
`define APU_DMAX_HS26_ASYNC_CLK 1


// Name:         DMAX_HS27_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 27)
//
// The DMA handshake interface 27 has asynchronous clock.
`define APU_DMAX_HS27_ASYNC_CLK 1


// Name:         DMAX_HS28_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 28)
//
// The DMA handshake interface 28 has asynchronous clock.
`define APU_DMAX_HS28_ASYNC_CLK 1


// Name:         DMAX_HS29_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 29)
//
// The DMA handshake interface 29 has asynchronous clock.
`define APU_DMAX_HS29_ASYNC_CLK 1


// Name:         DMAX_HS30_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 30)
//
// The DMA handshake interface 30 has asynchronous clock.
`define APU_DMAX_HS30_ASYNC_CLK 1


// Name:         DMAX_HS31_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 31)
//
// The DMA handshake interface 31 has asynchronous clock.
`define APU_DMAX_HS31_ASYNC_CLK 1


// Name:         DMAX_HS32_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 32)
//
// The DMA handshake interface 32 has asynchronous clock.
`define APU_DMAX_HS32_ASYNC_CLK 1


// Name:         DMAX_HS33_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 33)
//
// The DMA handshake interface 33 has asynchronous clock.
`define APU_DMAX_HS33_ASYNC_CLK 1


// Name:         DMAX_HS34_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 34)
//
// The DMA handshake interface 34 has asynchronous clock.
`define APU_DMAX_HS34_ASYNC_CLK 1


// Name:         DMAX_HS35_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 35)
//
// The DMA handshake interface 35 has asynchronous clock.
`define APU_DMAX_HS35_ASYNC_CLK 1


// Name:         DMAX_HS36_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 36)
//
// The DMA handshake interface 36 has asynchronous clock.
`define APU_DMAX_HS36_ASYNC_CLK 1


// Name:         DMAX_HS37_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 37)
//
// The DMA handshake interface 37 has asynchronous clock.
`define APU_DMAX_HS37_ASYNC_CLK 1


// Name:         DMAX_HS38_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 38)
//
// The DMA handshake interface 38 has asynchronous clock.
`define APU_DMAX_HS38_ASYNC_CLK 1


// Name:         DMAX_HS39_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 39)
//
// The DMA handshake interface 39 has asynchronous clock.
`define APU_DMAX_HS39_ASYNC_CLK 1


// Name:         DMAX_HS40_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 40)
//
// The DMA handshake interface 40 has asynchronous clock.
`define APU_DMAX_HS40_ASYNC_CLK 1


// Name:         DMAX_HS41_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 41)
//
// The DMA handshake interface 41 has asynchronous clock.
`define APU_DMAX_HS41_ASYNC_CLK 1


// Name:         DMAX_HS42_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 42)
//
// The DMA handshake interface 42 has asynchronous clock.
`define APU_DMAX_HS42_ASYNC_CLK 1


// Name:         DMAX_HS43_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 43)
//
// The DMA handshake interface 43 has asynchronous clock.
`define APU_DMAX_HS43_ASYNC_CLK 1


// Name:         DMAX_HS44_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 44)
//
// The DMA handshake interface 44 has asynchronous clock.
`define APU_DMAX_HS44_ASYNC_CLK 1


// Name:         DMAX_HS45_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 45)
//
// The DMA handshake interface 45 has asynchronous clock.
`define APU_DMAX_HS45_ASYNC_CLK 1


// Name:         DMAX_HS46_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 46)
//
// The DMA handshake interface 46 has asynchronous clock.
`define APU_DMAX_HS46_ASYNC_CLK 1


// Name:         DMAX_HS47_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 47)
//
// The DMA handshake interface 47 has asynchronous clock.
`define APU_DMAX_HS47_ASYNC_CLK 1


// Name:         DMAX_HS48_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 48)
//
// The DMA handshake interface 48 has asynchronous clock.
`define APU_DMAX_HS48_ASYNC_CLK 1


// Name:         DMAX_HS49_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 49)
//
// The DMA handshake interface 49 has asynchronous clock.
`define APU_DMAX_HS49_ASYNC_CLK 1


// Name:         DMAX_HS50_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 50)
//
// The DMA handshake interface 50 has asynchronous clock.
`define APU_DMAX_HS50_ASYNC_CLK 1


// Name:         DMAX_HS51_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 51)
//
// The DMA handshake interface 51 has asynchronous clock.
`define APU_DMAX_HS51_ASYNC_CLK 1


// Name:         DMAX_HS52_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 52)
//
// The DMA handshake interface 52 has asynchronous clock.
`define APU_DMAX_HS52_ASYNC_CLK 1


// Name:         DMAX_HS53_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 53)
//
// The DMA handshake interface 53 has asynchronous clock.
`define APU_DMAX_HS53_ASYNC_CLK 1


// Name:         DMAX_HS54_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 54)
//
// The DMA handshake interface 54 has asynchronous clock.
`define APU_DMAX_HS54_ASYNC_CLK 1


// Name:         DMAX_HS55_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 55)
//
// The DMA handshake interface 55 has asynchronous clock.
`define APU_DMAX_HS55_ASYNC_CLK 1


// Name:         DMAX_HS56_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 56)
//
// The DMA handshake interface 56 has asynchronous clock.
`define APU_DMAX_HS56_ASYNC_CLK 1


// Name:         DMAX_HS57_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 57)
//
// The DMA handshake interface 57 has asynchronous clock.
`define APU_DMAX_HS57_ASYNC_CLK 1


// Name:         DMAX_HS58_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 58)
//
// The DMA handshake interface 58 has asynchronous clock.
`define APU_DMAX_HS58_ASYNC_CLK 1


// Name:         DMAX_HS59_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 59)
//
// The DMA handshake interface 59 has asynchronous clock.
`define APU_DMAX_HS59_ASYNC_CLK 1


// Name:         DMAX_HS60_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 60)
//
// The DMA handshake interface 60 has asynchronous clock.
`define APU_DMAX_HS60_ASYNC_CLK 1


// Name:         DMAX_HS61_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 61)
//
// The DMA handshake interface 61 has asynchronous clock.
`define APU_DMAX_HS61_ASYNC_CLK 1


// Name:         DMAX_HS62_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 62)
//
// The DMA handshake interface 62 has asynchronous clock.
`define APU_DMAX_HS62_ASYNC_CLK 1


// Name:         DMAX_HS63_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 63)
//
// The DMA handshake interface 63 has asynchronous clock.
`define APU_DMAX_HS63_ASYNC_CLK 1


// Name:         DMAX_HS64_ASYNC_CLK
// Default:      true ((DMAX_HS_SAME_ASYNC_CLK==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      (DMAX_ASYNC_HS_EN == 1) && (DMAX_HS_SAME_ASYNC_CLK == 0) &&
//               (DMAX_NUM_HS_IF >= 64)
//
// The DMA handshake interface 64 has asynchronous clock.
`define APU_DMAX_HS64_ASYNC_CLK 1


// Name:         DMAX_INTR_IO_TYPE
// Default:      COMBINED ONLY
// Values:       COMBINED ONLY (0), CHANNEL AND COMMONREG (1), ALL INTERRUPTS
//               OUTPUTS (2)
//
// Selects which interrupt-related signals appear as outputs on the design.
//  - COMBINED_ONLY: Only "intr" output exist.
// Bitwise OR of all bits of DMAC_IntStatusReg register is driven onto "intr" output.
//  - CHANNEL_AND_COMMONREG: "intr_ch" and "intr_cmnreg" outputs exist.
// Bitwise OR of all the corresponding channel bits of DMAC_IntStatusReg register is driven onto the respective "intr_ch"
// output.
// Bitwise OR of all the bits of DMAC_CommonReg_IntStatusReg register is driven onto the respective "intr_cmnreg" output.
//   - ALL_INTERRUPT_OUTPUTS: "intr", "intr_ch" and "intr_cmnreg" outputs exist.
// Bitwise OR of all bits of DMAC_IntStatusReg register is driven onto "intr" output.
// Bitwise OR of all the corresponding channel bits of DMAC_IntStatusReg register is driven onto the respective "intr_ch"
// output.
// Bitwise OR of all the bits of DMAC_CommonReg_IntStatusReg register is driven onto the respective "intr_cmnreg" output.
`define APU_DMAX_INTR_IO_TYPE 1


// Name:         DMAX_INTR_SYNC2SLVCLK
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_SLVIF_CLOCK_MODE!=0
//
// By default, interrupt output is synchronous to dmac_core_clock. When this parameter is set to Yes (1), the interrupt
// output pins are synchronous to register bus Interface clock. In this case, additional synchronizers are added inside
// DW_axi_dmac.
`define APU_DMAX_INTR_SYNC2SLVCLK 0


// Name:         DMAX_SLVIF_STATUS_OP_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// By default, this option creates a register bus interface status indication (Busy/Idle) signals on the I/O, which is
// synchronous to the register bus interface clock. When you set this option to False (0), the signal is not included on the I/O.
`define APU_DMAX_SLVIF_STATUS_OP_EN 0


// Name:         DMAX_CORE_STATUS_OP_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// By default, this option creates a DMAC internal status indication (Busy/Idle) signal on the I/O, which is synchronous to
// dmac_core_clock. When you set this option to False (0), the signal is not included on the I/O.
`define APU_DMAX_CORE_STATUS_OP_EN 0


// Name:         DMAX_HOLD_IO_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), this option creates a DMAC Hold Request Input signal (dmac_hold_req) and DMAC Hold Acknowledgement
// Output signal (dmac_hold_ack) on the I/O, which are synchronous to dmac_core_clock. When you set this option to False (0),
// this signal is not included on the I/O.
`define APU_DMAX_HOLD_IO_EN 0


// Name:         DMAX_ENCODED_COMP_PARAMS_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      0
//
// Setting this option to 1 enables component parameter
// registers in DW_axi_dmac which captures the current DW_axi_dmac
// configuration details.
// There is some area overhead when these parameters are included.
`define APU_DMAX_ENCODED_COMP_PARAMS_EN 0


// Name:         DMAX_DEBUG_REGS_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      0
//
// Setting this option to 1 enables debug registers in
// DW_axi_dmac which captures the address corresponding to the latest
// error events on register bus interface, LLI interface, source peripheral
// interface and destination peripheral interface.
// There is some area overhead when these registers are included.
`define APU_DMAX_DEBUG_REGS_EN 0


// Name:         DMAX_CH_ABORT_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), enables logic to support Channel Terminate feature in DW_axi_dmac.
`define APU_DMAX_CH_ABORT_EN 0


// Name:         DMAX_STATIC_ENDIAN_SELECT_MSTIF
// Default:      Yes
// Values:       No (0), Yes (1)
//
// The endian scheme of the DW_axi_dmac manager interfaces can be configured statically through coreConsultant or
// dynamically through pins on the I/O.
//  - For the static case, there is a single coreConsultant parameter that controls the endianness of all AXI manager
//  interfaces.
//  - For the dynamic case, there is an individual pin for each of the AXI manager interfaces.
// When set to Yes (1), the endianness is configured based on the value of DMAX_ENDIAN_FORMAT_MSTIF; otherwise it is
// configured based on the value of input pin, dmac_endian_format_mstif_m(i).
`define APU_DMAX_STATIC_ENDIAN_SELECT_MSTIF 1


// Name:         DMAX_ENDIAN_FORMAT_MSTIF
// Default:      Little Endian
// Values:       Little Endian (0), Big Endian BE-8 (1)
// Enabled:      DMAX_STATIC_ENDIAN_SELECT_MSTIF == 1
//
// DMAX_ENDIAN_FORMAT_MSTIF values for different AXI manager interface endian formats are as follows.
//  - 0: Little Endian
//  - 1: Big Endian BE-8
`define APU_DMAX_ENDIAN_FORMAT_MSTIF 0


// Name:         DMAX_LLI_ENDIAN_SELECTION_PIN_EN
// Default:      0
// Values:       0 1
// Enabled:      !((DMAX_STATIC_ENDIAN_SELECT_MSTIF == 1) &&
//               (DMAX_ENDIAN_FORMAT_MSTIF ==0))
//
// When set to Yes (1), enables additional inputs are enabled to control the endian scheme used for LLI access. An
// individual pin is added for each AXI Manager interface. LLI access on each AXI Manager interface can be independently configured
// to support Big Endian scheme (BE-8) based on the endian scheme selected for that particular manager interface or Little
// Endian scheme irrespective of the endian scheme selected for that particular manager interface.
//  - 0: Endian scheme used for LLI access is the same as that used for data access for M1/M2 interfaces.
//  - 1: Endian scheme used for LLI access is the same as that used for data access for M1/M2 interfaces.
// or
//  - Little Endian method is used for LLI access irrespective of the endian scheme used for data access depending on the
//  value of dmac_le_select_lli_mstif_m(i) input.
`define APU_DMAX_LLI_ENDIAN_SELECTION_PIN_EN 0


// Name:         DMAX_CH_MEM_EXT
// Default:      Internal
// Values:       Internal (0), External (1), TopLevel (2)
//
// This parameter is used for selecting Channel FIFO Memory and Unique ID Memory - internal or external or Top Level of the
// DW_axi_dmac. All channels share this parameter.
// The default value is 0, then internal channel memory interface scheme is used. The internal channel FIFO/Unique ID
// Memory uses Synopsys flip-flop based memory.
// When external channel memory interface scheme is used, SoC designer needs to implement the memories based on memory
// size and memory library external to DW_axi_dmac.
// When Top Level channel memory interface scheme is used, then internal channel FIFO/Unique ID Memory uses Synopsys
// flip-flop based memory and instantiates them at the top level of the DW_axi_dmac.
`define APU_DMAX_CH_MEM_EXT 1


// Name:         DMAX_S_DATA_WIDTH
// Default:      32
// Values:       32 64
// Enabled:      DMAX_SLVIF_MODE == 0
//
// Specifies the data bus width for the AHB/APB4 register bus interface.
`define APU_DMAX_S_DATA_WIDTH 64


// Name:         DMAX_OPT_TIMING
// Default:      Yes
// Values:       No (0), Yes (1)
//
// This parameter allows user to Enable the Timing Optimization. This feature will enable the timing optmization for the
// following :
//  - Global - Context Sensitive Low Power Logic
//  - AXI Manager Interface - Context Sensitive Low Power Logic
//  - AXI Manager Interface - AR Channel and AW Channel FIFO Push Logic
`define APU_DMAX_OPT_TIMING 1


// Name:         DMAX_HW_VIRT_EN
// Default:      False
// Values:       False (0), True (1)
// Enabled:      <DWC-AXI-DMAC-GEN2 feature authorize> == 1
//
// This parameter enables the hardware virtualization feature. When enabled,
//  - Virtual Machine ID is associated with the AXI Manager interface
//  - Channel Enable, Suspend and Terminate register fields are accessible through the channel specific registers CHx_EN
//  - Channel Priority and Virtual Machine ID register fields are accessible through common register space
//  DMAC_CHPRIOR_REG and DMAC_VMID_REG respectively.
`define APU_DMAX_HW_VIRT_EN 0


// Name:         DMAX_HW_VIRT_VMID_EN
// Default:      False
// Values:       False (0), True (1)
// Enabled:      DMAX_HW_VIRT_EN == 1
//
// This parameter enables the following features,
//  - Virtual Machine ID is associated with the AXI Manager interface
//  - Virtual Machine ID register field will be accessible through common register space DMAC_VMID_REG.
`define APU_DMAX_HW_VIRT_VMID_EN 0


// Name:         DMAX_VMID_WIDTH
// Default:      1
// Values:       1, ..., 19
// Enabled:      DMAX_HW_VIRT_VMID_EN == 1
//
// Width of Virtual Machine ID associated with AWID, ARID, WID, RID, and BID.
`define APU_DMAX_VMID_WIDTH 1


// Name:         DMAX_CHEN_REORG
// Default:      False
// Values:       False (0), True (1)
// Enabled:      DMAX_HW_VIRT_EN == 1
//
// This parameter decides how the Channel Enable, Suspend and Terminate register fields are organized. When set to 0, these
// fields are present in the common register space. When set to 1, they are moved to the channel specific registers.
`define APU_DMAX_CHEN_REORG 0


// Name:         DMAX_CHPRIOR_REORG
// Default:      False
// Values:       False (0), True (1)
// Enabled:      DMAX_HW_VIRT_EN == 1
//
// This parameter will allow the Channel Priority field to be accessible through common register space DMAC_CHPRIOR_REG.
`define APU_DMAX_CHPRIOR_REORG 0


// Name:         DMAX_SAFETY_FEATURE_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to Enable the Safety features. If enabled, this allows us to enable Safety Features:
//  - Register Bus Interface Parity Feature
//  - ECC Protection Feature for :
//    -- Channel Memory Interface
//    -- UID Memory Interface
//  - ECC/Parity Protection for :
//    -- AXI Manager Interface
//  - Lock Step Protection Feature
`define APU_DMAX_SAFETY_FEATURE_EN 0


// Name:         DMAX_ADV_SAFETY_FEATURE_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_SAFETY_FEATURE_EN==1
//
// This parameter allows user to Enable the Advanced Safety features. If enabled, this allows us to enable Adavanced Safety
// Features:
//  - Interface Timeouts
//  - Lock Step Protection - Error Injection Failure Indication
//  - Safety Interrupts Re-organization
`define APU_DMAX_ADV_SAFETY_FEATURE_EN 0


// Name:         DMAX_SFTY_INTR_IO_TYPE
// Default:      COMBINED ONLY
// Values:       COMBINED ONLY (0), SEPERATE_INTERRUPTS_OUTPUTS (1)
// Enabled:      DMAX_ADV_SAFETY_FEATURE_EN==1
//
// Selects which safety interrupt-related signals appear as outputs on the design.
//  - COMBINED_ONLY: Only correctable (prot_corr_err_intr) and uncorrectable (prot_uncorr_err_intr) safety interrupt
//  outputs exist.
// Bitwise OR of all safety feature related bits of interrupt status register is driven onto "prot_corr_err_intr" and
// "prot_uncorr_err_intr" output.
//  - SEPERATE_INTERRUPTS_OUTPUTS: All safety interrupts exist separately.
`define APU_DMAX_SFTY_INTR_IO_TYPE 0


// Name:         DMAX_PARITY_PROT_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_SAFETY_FEATURE_EN==1
//
// Specifies whether or not parity check is enabled for data bus of the AHB/APB4 register bus interface.
`define APU_DMAX_PARITY_PROT_EN 0


// Name:         DMAX_DEF_PARITY_MODE
// Default:      Even
// Values:       Even (0x0), Odd (0x1)
// Enabled:      DMAX_PARITY_PROT_EN == 1
//
// Default value of the Parity Mode i.e. DMAC_PARITYREG.PARITY_MODE field.
`define APU_DMAX_DEF_PARITY_MODE 1'h0


// Name:         DMAX_DEF_PARITY_EN
// Default:      0x1
// Values:       0x0, 0x1
// Enabled:      DMAX_PARITY_PROT_EN == 1
//
// Default value of the Parity Enable i.e. DMAC_PARITYREG.PARITY_En field.
`define APU_DMAX_DEF_PARITY_EN 1'h1


// Name:         DMAX_HWDATA_PIPE_LINE
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      (DMAX_PARITY_PROT_EN == 1) && (DMAX_SLVIF_MODE == 0)
//
// The Write Parity check can be performed when hwdata is ready or after a pipelining stage.
// (For input timing purpose). Due to this the hready_resp will also be delayed by one or
// two cycles.
`define APU_DMAX_HWDATA_PIPE_LINE 0


// Name:         DMAX_ADDR_PARITY_PROT_EN
// Default:      0 (DMAX_PARITY_PROT_EN)
// Values:       0 1
// Enabled:      DMAX_PARITY_PROT_EN == 1
//
// Specifies whether or not parity check is enabled for address bus of the AHB/APB4 register bus interface.
`define APU_DMAX_ADDR_PARITY_PROT_EN 0


// Name:         DMAX_ECC_PROT_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_SAFETY_FEATURE_EN==1
//
// This parameter allows user to include ECC/Parity Protection feature.
//
// If enabled, the ECC Protection feature can be included for:
//  - Channel Memory Interface
//  - UID Memory Interface
// If enabled, ECC/Parity Protection feature can be included for:
//  - AXI Manager Interface
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_ECC_PROT_EN 0


// Name:         DMAX_ECC_MEMIF_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_ECC_PROT_EN == 1) && (DMAX_CH_MEM_EXT >= 1)
//
// This parameter allows user to include or exclude ECC Protection feature for the FIFO Memory interface of all the
// channels.
`define APU_DMAX_ECC_MEMIF_EN 0


// Name:         DMAX_ECC_UIDMEMIF_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_ECC_PROT_EN == 1) && (DMAX_CH_MEM_EXT >= 1) &&
//               (DMAX_HAS_RUID_PARAM == 1)
//
// This parameter allows user to include or exclude ECC Protection feature for the UID Memory interface of all the
// channels.
`define APU_DMAX_ECC_UIDMEMIF_EN 0


// Name:         DMAX_ECC_MXIF_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_ECC_PROT_EN == 1
//
// This parameter allows user to include or exclude ECC Protection feature for the AXI Manager interface(s).
`define APU_DMAX_ECC_MXIF_EN 0


// Name:         DMAX_MXIF_ECC_PAR_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_ECC_PROT_EN == 1
//
// Enables the Safety feature on the AXI Manager Interface.
// Safety Features include:
//  - Parity Protection Feature and/or
//  - ECC Protection Feature
`define APU_DMAX_MXIF_ECC_PAR_EN 0


// Name:         DMAX_MXIF_ECC_PAR_MODE
// Default:      ECC - Address/Data and Control
// Values:       ECC - Address/Data and Control (1), ECC - Address/Data and Parity -
//               Control (2), ECC - Data and Parity - Address/Control (3)
// Enabled:      DMAX_MXIF_ECC_PAR_EN == 1
//
// Selects the AXI Interface ECC and Parity Mode.
//  - 1: ECC for Address/Data and Control signals
//  - 2: ECC for Address/Data and Parity for Control signals
//  - 3: ECC for Data and Parity for Address/Control signals
`define APU_DMAX_MXIF_ECC_PAR_MODE 1


// Name:         DMAX_MXIF_PAR_MODE
// Default:      ARC Compatibility Mode
// Values:       Per Byte Parity Mode (0), ARC Compatibility Mode (1)
// Enabled:      DMAX_MXIF_ECC_PAR_EN == 1 && DMAX_MXIF_ECC_PAR_MODE == 2
//
// Selects AXI Interface Parity Mode.
//   - 0: Per 8-bit Parity Computation
//   - 1: ARC Mode Parity Computation
`define APU_DMAX_MXIF_PAR_MODE 1


// Name:         DMAX_MXIF_PAR_TYPE
// Default:      Odd
// Values:       Even (0), Odd (1)
// Enabled:      DMAX_MXIF_ECC_PAR_EN == 1 && DMAX_MXIF_ECC_PAR_MODE == 2
//
// Selects AXI Interface Parity type for data, address, or control signals
//  - Even Parity
//  - Odd Parity
`define APU_DMAX_MXIF_PAR_TYPE 1


// Name:         DMAX_MXIF_ECC_GRAN_TYPE
// Default:      Full Width
// Values:       Full Width (0), 32-Bit ECC (1), 64-Bit ECC (2)
// Enabled:      DMAX_MXIF_ECC_PAR_EN == 1
//
// AXI Interface ECC Resolution Type. This parameter selects the Granularity of ECC Checkbits generation.
//  - 0: Full Width ECC Computation
//  - 1: 32 bit Granularity ECC Computation
//  - 2: 64 bit Granularity ECC Computation
`define APU_DMAX_MXIF_ECC_GRAN_TYPE 0


// Name:         DMAX_MXIF_READY_VALID_PAR_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_MXIF_ECC_PAR_EN==1
//
// Enables AXI Interface Ready and Valid Parity feature
`define APU_DMAX_MXIF_READY_VALID_PAR_EN 0


// Name:         DMAX_MXIF_READY_VALID_PAR_TYPE
// Default:      Odd
// Values:       Even (0), Odd (1)
// Enabled:      DMAX_MXIF_READY_VALID_PAR_EN == 1
//
// Selects AXI Interface Parity type for valid and ready signals
//  - Even Parity
//  - Odd Parity
`define APU_DMAX_MXIF_READY_VALID_PAR_TYPE 1


// Name:         DMAX_MXIF_ECC_MODE
// Default:      DesignWare ECC Engine
// Values:       DesignWare ECC Engine (0), ARC Mode ECC Engine (1), User Defined
//               ECC Engine (2)
// Enabled:      DMAX_ECC_PROT_EN==1 && (DMAX_ECC_MXIF_EN==1 ||
//               DMAX_MXIF_ECC_PAR_EN==1)
//
// Selects the ECC Engine used for ECC Generation and Monitoring for AXI Manager Interface.
// The following ECC Modes are supported:
//  - DesignWare ECC Engine(0)
//  - ARC Mode ECC Engine(1)
//  - User Defined ECC Engine(2)
// Setting appropriate value based on the system requirement.
`define APU_DMAX_MXIF_ECC_MODE 0

//The AXI Address (AW or AR) Channel ECC and Parity Mode Selection

`define APU_DMAX_MXIF_ADDR_ECC_PAR_MODE 1

//The AXI Data (W or R) Channel ECC and Parity Mode Selection

`define APU_DMAX_MXIF_DATA_ECC_PAR_MODE 1

//The AXI B Channel ECC and Parity Mode Selection

`define APU_DMAX_MXIF_B_ECC_PAR_MODE 1


// Name:         DMAX_LAST_WRITE_ECC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_ECC_MXIF_EN == 1) && (DMAX_ENABLE_LAST_WRITE == 1)
//
// This parameter allows user to include or exclude Write Last in the AXI Manager interface(s) B Channel ECC Computation.
`define APU_DMAX_LAST_WRITE_ECC_EN 0


// Name:         DMAX_ECC_DIAG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_ECC_PROT_EN == 1
//
// This parameter allows user to include or exclude ECC additional diagnostic features like access to correctable, and
// uncorrectable counters through the register DMAC_COMMONREG_ECCCTLSTATUSREG.
`define APU_DMAX_ECC_DIAG_EN 0



// Name:         DMAX_CH_MEM_REGOUT
// Default:      No (DMAX_ECC_MEMIF_EN == 1 ? 1 : 0)
// Values:       No (0), Yes (1)
// Enabled:      (DMAX_CH_MEM_EXT>= 1) && (DMAX_ECC_MEMIF_EN == 0)
//
// This parameter decides if to add pipeline register after channel FIFO/UID memory. It is only valid when external memory
// is enabled. If enabled, pipeline register is added in DMAC IP and memory read data timing will be improved.
`define APU_DMAX_CH_MEM_REGOUT 1


// Name:         DMAX_ECC_ERR_INJ_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_ECC_MEMIF_EN==1 || DMAX_ECC_UIDMEMIF_EN==1
//
// Enables the error injection capability in FIFO/UID memory interface.
`define APU_DMAX_ECC_ERR_INJ_EN 0


// Name:         DMAX_LS_PROT_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      (DMAX_CH_MEM_EXT >= 1) && (DMAX_SAFETY_FEATURE_EN == 1)
//
// This parameter allows user to include Lock Step Protection feature. If enabled, this allows us to duplicate the
// DW_axi_dmac instance to provide delayed Lock Step operation.
//
// Note: The Lock Step Protection feature duplicates the entire DW_axi_dmac to provide the Lock step operation. Hence this
// feature must be chosen based system level functional safety requirement.
`define APU_DMAX_LS_PROT_EN 0


// Name:         DMAX_LS_DIAG_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_LS_PROT_EN == 1
//
// This parameter allows user to include or exclude Lock Step Protection feature diagnostic feature to include hardware
// error injection logic.
`define APU_DMAX_LS_DIAG_EN 0

//This parameter allows user to enable advanced features in Lock Step Protection. If enabled, this allows to:
//- Select the interface for which error needs to be injected.
//- Include output interface signal to indicate error causing interface.


// Name:         DMAX_M_ADDR_WIDTH
// Default:      32
// Values:       32, ..., 64
//
// AXI Manager 1 interface address bus width.
`define APU_DMAX_M_ADDR_WIDTH 40


// Name:         DMAX_M_DATA_WIDTH
// Default:      32
// Values:       32 64 128 256 512 1024
//
// AXI Manager interface data bus width.
`define APU_DMAX_M_DATA_WIDTH 256


// Name:         DMAX_M_ID_WIDTH
// Default:      6
// Values:       1, ..., 20
//
// AXI manager interface ID bus width (common for awid_m(i), arid_m(i), wid_m(i), bid_m(i) and rid_m(i)).
// Note: The Minimum value of DMAC_M_ID_WIDTH is equal to log2(DMAX_NUM_CHANNELS) if multi-block transfer type is
// hardcoded to non-linked-list-based schemes, otherwise [log2(DMAX_NUM_CHANNELS)] + 1.
`define APU_DMAX_M_ID_WIDTH 8


// Name:         DMAX_M_BURSTLEN_WIDTH
// Default:      4
// Values:       4 5 6 7 8
//
// AXI manager interface Burst Length (arlen(i)/awlen(i)) width.
`define APU_DMAX_M_BURSTLEN_WIDTH 8


// Name:         DMAX_M_ADDR_FIFO_DEPTH
// Default:      4
// Values:       4 8
// Enabled:      DMAX_MSTIF1_CLOCK_MODE == 1 || DMAX_MSTIF2_CLOCK_MODE == 1
//
// AXI manager interface read/write address channel FIFO depth. Setting appropriate value based on the system requirement
// allows some logic optimization of the implementation.
`define APU_DMAX_M_ADDR_FIFO_DEPTH 4


// Name:         DMAX_M_DATA_FIFO_DEPTH
// Default:      8 ((DMAX_CH_MEM_EXT==1) ? 8 : 4)
// Values:       4 8
// Enabled:      DMAX_MSTIF1_CLOCK_MODE == 1 || DMAX_MSTIF2_CLOCK_MODE == 1 ||
//               DMAX_CH_MEM_EXT == 1
//
// AXI manager interface Read/Write Data Channel FIFO depth. Setting appropriate value based on the system requirement
// allows some logic optimization of the implementation.
// When channel FIFO selects external scheme, it is suggested to set this parameter to 8.
`define APU_DMAX_M_DATA_FIFO_DEPTH 4


// Name:         DMAX_M_BRESP_FIFO_DEPTH
// Default:      4
// Values:       4 8
// Enabled:      DMAX_MSTIF1_CLOCK_MODE == 1 || DMAX_MSTIF2_CLOCK_MODE == 1
//
// AXI manager interface write response channel FIFO depth. Setting appropriate value based on the system requirement
// allows some logic optimization of the implementation.
`define APU_DMAX_M_BRESP_FIFO_DEPTH 4


// Name:         DMAX_ENABLE_LAST_WRITE
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), enables the additional handshaking signal last_write_mi on all AXI manager interfaces.
// The last_write_mi signal is asserted on last data phase of every destination block transfer and remains asserted until
// the last data phase completes.
`define APU_DMAX_ENABLE_LAST_WRITE 0



// Name:         DMAX_CSLP_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), allows you to include Context Sensitive Low Power feature. If enabled, it includes Global Context
// Sensitive Low Power feature and allows other Context Sensitive Low Power feature to be implemented optionally. Enabling
// this feature saves significant amount of power, with minimal area consumption.
`define APU_DMAX_CSLP_EN 1


// Name:         DMAX_DEBUG_PORTS_EN
// Default:      Yes (DMAX_CSLP_EN == 1 ? 1 : 0)
// Values:       No (0), Yes (1)
//
// When set to Yes (1), enables debug_* ports in DW_axi_dmac.
`define APU_DMAX_DEBUG_PORTS_EN 1


// Name:         DMAX_CHNL_CSLP_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_CSLP_EN == 1
//
// When set to Yes (1), includes the logic that implements Context Sensitive Low Power feature in DMA Channels.
`define APU_DMAX_CHNL_CSLP_EN 1



// Name:         DMAX_SBIU_CSLP_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_CSLP_EN == 1
//
// When set to Yes (1), includes the logic that implements Context Sensitive Low Power feature in Register Bus Interface.
`define APU_DMAX_SBIU_CSLP_EN 1


// Name:         DMAX_MXIF_CSLP_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      DMAX_CSLP_EN == 1
//
// Include or exclude logic that implements Context Sensitive Low Power feature in Manager Bus Interface.
`define APU_DMAX_MXIF_CSLP_EN 1


// Name:         DMAX_GLCH_LPDLY_WIDTH
// Default:      4
// Values:       4 5 6 7 8
// Enabled:      DMAX_CSLP_EN == 1 || DMAX_CHNL_CSLP_EN == 1
//
// Defines the width of the Global and DMA Channel Low Power Delay Counter.
`define APU_DMAX_GLCH_LPDLY_WIDTH 4


// Name:         DMAX_SBIU_LPDLY_WIDTH
// Default:      4
// Values:       4 5 6 7 8
// Enabled:      DMAX_SBIU_CSLP_EN == 1
//
// Defines the width of the SBIU Low Power Delay Counter.
`define APU_DMAX_SBIU_LPDLY_WIDTH 4


// Name:         DMAX_MXIF_LPDLY_WIDTH
// Default:      4
// Values:       4 5 6 7 8
// Enabled:      DMAX_MXIF_CSLP_EN == 1
//
// Defines the width of the AXI Manager Interface Low Power Delay Counter.
`define APU_DMAX_MXIF_LPDLY_WIDTH 4


// Name:         DMAX_GLCH_LPDLY
// Default:      4
// Values:       4, ..., 255
// Enabled:      DMAX_CSLP_EN == 1 || DMAX_CHNL_CSLP_EN == 1
//
// Defines the default load value of the Global and DMA Channel Low Power Delay Counter.
`define APU_DMAX_GLCH_LPDLY 4


// Name:         DMAX_SBIU_LPDLY
// Default:      4
// Values:       4, ..., 255
// Enabled:      DMAX_SBIU_CSLP_EN == 1
//
// Defines the default load value of the SBIU Low Power Delay Counter.
`define APU_DMAX_SBIU_LPDLY 4


// Name:         DMAX_MXIF_LPDLY
// Default:      4
// Values:       4, ..., 255
// Enabled:      DMAX_MXIF_CSLP_EN == 1
//
// Defines the default load value of the AXI Manager Interface Low Power Delay Counter.
`define APU_DMAX_MXIF_LPDLY 4






// Name:         DMAX_LLI_AUTO_RESUME_REQ_CNT
// Default:      0
// Values:       0 8 16 32 64 128 256 512 1024
// Enabled:      ([ <functionof>]) && <DWC-AXI-DMAC-GEN2 feature authorize> == 1
//
// This parameter allows the user to specify the number of wait cycles to request for the LLI block transfer resume. For
// example: when this parameter is chosen as 8, DW_axi_dmac waits for 8 cycles before initiating a LLI fetch request after
// finding an LLI invalid entry (ShadowReg_Or_LLI_Valid = 0). For more information, refer to the section "LLI Auto Resume
// Request". When this parameter is set to 0, DW_axi_dmac excludes the logic to implement LLI Auto Resume Request feature.
// Note: Number of wait cycles specified will be considered in terms of dmac_core_clock cycles.
`define APU_DMAX_LLI_AUTO_RESUME_REQ_CNT 0

//Log2(DMAX_LLI_AUTO_RESUME_REQ_CNT)

`define APU_LOG2_DMAX_LLI_AUTO_RESUME_REQ_CNT 1


// Name:         DMAX_CH1_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel x FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation. For more information on the FIFO depth calculation, see "Calculating FIFO Depth" section in the user guide.
`define APU_DMAX_CH1_FIFO_DEPTH 256


// Name:         DMAX_CH1_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel x (CH(x)_CTL.SRC_MSIZE and
// CH(x)_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH1_MAX_MSIZE 256


// Name:         DMAX_CH1_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH(x)_BLOCK_TS.BLOCK_TS), that can be programmed for channel x. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH(x)_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH(x)_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size
//  exceeds the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH1_MAX_BLOCK_TS 131071


// Name:         DMAX_CH1_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel x. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH(x)_MAX_AMBA_BURST_LENGTH <= DMAX_CH(x)_MAX_BLOCK_TS
//  - DMAX_CH(x)_MAX_AMBA_BURST_LENGTH <= DMAX_CH(x)_MAX_MSIZE
`define APU_DMAX_CH1_MAX_AMBA_BURST_LENGTH 64


// Name:         DMAX_CH1_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel x. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH1_LOCK_EN 0


// Name:         DMAX_CH1_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel x. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH1_TT_FC 4'h0


// Name:         DMAX_CH1_FC
// Default:      DMAC (DMAX_CH1_TT_FC == 8 ? 0 : (DMAX_CH1_TT_FC <= 3 ? 1 :
//               (DMAX_CH1_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 1 Flow Controller
`define APU_DMAX_CH1_FC 1


// Name:         DMAX_CH1_TT
// Default:      Memory to Memory (DMAX_CH1_TT_FC == 8 ? 0 : (DMAX_CH1_TT_FC == 0 ?
//               1 : (DMAX_CH1_TT_FC == 1 || DMAX_CH1_TT_FC == 6 ? 3: (DMAX_CH1_TT_FC
//               == 2 || DMAX_CH1_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 1 Transfer Type
`define APU_DMAX_CH1_TT 1


// Name:         DMAX_CH1_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel x. If this is not hardcoded, software can program
// the source of channel x to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH1_SMS 2'h0


// Name:         DMAX_CH1_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel x destination. If this is not hardcoded, then software can
// program the destination of channel x to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH1_DMS 2'h0


// Name:         DMAX_CH1_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel x. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH1_STW 0


// Name:         DMAX_CH1_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel x. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH1_DTW 0


// Name:         DMAX_CH1_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH1_MULTI_BLK_EN==1) && ((DMAX_CH1_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH1_MULTI_BLK_TYPE ==2) || (DMAX_CH1_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH1_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel x. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH1_SHADOW_REG_EN 1


// Name:         DMAX_CH1_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel x. If this option is set to 0, then hardware
// hardwires channel x to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH1_MULTI_BLK_EN 1


// Name:         DMAX_CH1_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH1_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel x. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH1_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH1_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH1_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH1_MULTI_BLK_TYPE == 6 || DMAX_CH1_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH1_MULTI_BLK_TYPE == 1 || DMAX_CH1_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH1_MULTI_BLK_TYPE == 7 || DMAX_CH1_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH1_MULTI_BLK_TYPE == 2 || DMAX_CH1_MULTI_BLK_TYPE == 5 || DMAX_CH1_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH1_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH1_MULTI_BLK_TYPE == 10 || DMAX_CH1_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 1 Destination MultiBlock Type
`define APU_DMAX_CH1_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH1_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH1_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH1_MULTI_BLK_TYPE == 2 || DMAX_CH1_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH1_MULTI_BLK_TYPE == 3 || DMAX_CH1_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH1_MULTI_BLK_TYPE == 5 || DMAX_CH1_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH1_MULTI_BLK_TYPE == 6 || DMAX_CH1_MULTI_BLK_TYPE == 7 || DMAX_CH1_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH1_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH1_MULTI_BLK_TYPE == 12 || DMAX_CH1_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 1 Source MultiBlock Type
`define APU_DMAX_CH1_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH1_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH1_MULTI_BLK_EN==1) && (DMAX_CH1_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH1_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel x. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH1_LLI_PREFETCH_EN 1


// Name:         DMAX_CH1_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH1_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH1_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel x. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel x to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH1_LMS 2'h0


// Name:         DMAX_CH1_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel x pointed to by the content of CH(x)_SSTATAR
// register and store it in CHx_SSTAT register if CH(x)_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH(x)_SSTAT location of linked list at end of each block transfer if DMAX_CH(x)_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH1_SRC_STAT_EN 0


// Name:         DMAX_CH1_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel x pointed to by the content of
// CHx_DSTATAR register and store it in CH(x)_DSTAT register if CH(x)_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH(x)_DSTAT location of linked list at end of each block transfer if DMAX_CH(x)_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some
// logic optimization of the implementation.
`define APU_DMAX_CH1_DST_STAT_EN 0


// Name:         DMAX_CH1_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH1_MULTI_BLK_TYPE == 0 || DMAX_CH1_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH(x)_CTL, CH(x)_LLP_STATUS, CH(x)_SSTAT and CHx_DSTAT registers
// at the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH1_LLI_WB_EN 1


// Name:         DMAX_CH1_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH1_RD_UID_EN 0


// Name:         DMAX_CH1_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH1_WR_UID_EN 0


// Name:         DMAX_CH1_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH1_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH1_RD_UID 2


// Name:         DMAX_CH1_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH1_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH1_WR_UID 2


// Name:         DMAX_CH1_REORDER_BUFF_DEPTH
// Default:      256 (DMAX_CH1_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH1_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH1_REORDER_BUFF_DEPTH 256


// Name:         DMAX_CH1_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH1_RD_UID_EN==0) && (DMAX_CH1_WR_UID_EN==0) &&
//               ((<DWC-AXI-DMAC-CRC feature authorize>==1) && (<DWC-AXI-DMAC-GEN2 feature
//               authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH1_CRC_EN 0


// Name:         DMAX_CH2_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 2 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH2_FIFO_DEPTH 256


// Name:         DMAX_CH2_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 2 (CH2_CTL.SRC_MSIZE and CH2_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH2_MAX_MSIZE 256


// Name:         DMAX_CH2_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH2_BLOCK_TS.BLOCK_TS), that can be programmed for channel 2. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH2_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH2_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH2_MAX_BLOCK_TS 131071


// Name:         DMAX_CH2_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 2. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH2_MAX_AMBA_BURST_LENGTH <= DMAX_CH2_MAX_BLOCK_TS
//  - DMAX_CH2_MAX_AMBA_BURST_LENGTH <= DMAX_CH2_MAX_MSIZE
`define APU_DMAX_CH2_MAX_AMBA_BURST_LENGTH 64


// Name:         DMAX_CH2_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 2. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH2_LOCK_EN 0


// Name:         DMAX_CH2_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 2. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH2_TT_FC 4'h0


// Name:         DMAX_CH2_FC
// Default:      DMAC (DMAX_CH2_TT_FC == 8 ? 0 : (DMAX_CH2_TT_FC <= 3 ? 1 :
//               (DMAX_CH2_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 2 Flow Controller
`define APU_DMAX_CH2_FC 1


// Name:         DMAX_CH2_TT
// Default:      Memory to Memory (DMAX_CH2_TT_FC == 8 ? 0 : (DMAX_CH2_TT_FC == 0 ?
//               1 : (DMAX_CH2_TT_FC == 1 || DMAX_CH2_TT_FC == 6 ? 3: (DMAX_CH2_TT_FC
//               == 2 || DMAX_CH2_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 2 Transfer Type
`define APU_DMAX_CH2_TT 1


// Name:         DMAX_CH2_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 2. If this is not hardcoded, software can program
// the source of channel 2 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH2_SMS 2'h0


// Name:         DMAX_CH2_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 2 destination. If this is not hardcoded, then software can
// program the destination of channel 2 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH2_DMS 2'h0


// Name:         DMAX_CH2_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 2. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH2_STW 0


// Name:         DMAX_CH2_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 2. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH2_DTW 0


// Name:         DMAX_CH2_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH2_MULTI_BLK_EN==1) && ((DMAX_CH2_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH2_MULTI_BLK_TYPE ==2) || (DMAX_CH2_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH2_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 2. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH2_SHADOW_REG_EN 1


// Name:         DMAX_CH2_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 2. If this option is set to 0, then hardware
// hardwires channel 2 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH2_MULTI_BLK_EN 1


// Name:         DMAX_CH2_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH2_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 2. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH2_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH2_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH2_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH2_MULTI_BLK_TYPE == 6 || DMAX_CH2_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH2_MULTI_BLK_TYPE == 1 || DMAX_CH2_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH2_MULTI_BLK_TYPE == 7 || DMAX_CH2_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH2_MULTI_BLK_TYPE == 2 || DMAX_CH2_MULTI_BLK_TYPE == 5 || DMAX_CH2_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH2_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH2_MULTI_BLK_TYPE == 10 || DMAX_CH2_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 2 Destination MultiBlock Type
`define APU_DMAX_CH2_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH2_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH2_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH2_MULTI_BLK_TYPE == 2 || DMAX_CH2_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH2_MULTI_BLK_TYPE == 3 || DMAX_CH2_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH2_MULTI_BLK_TYPE == 5 || DMAX_CH2_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH2_MULTI_BLK_TYPE == 6 || DMAX_CH2_MULTI_BLK_TYPE == 7 || DMAX_CH2_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH2_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH2_MULTI_BLK_TYPE == 12 || DMAX_CH2_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 2 Source MultiBlock Type
`define APU_DMAX_CH2_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH2_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH2_MULTI_BLK_EN==1) && (DMAX_CH2_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH2_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 2. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH2_LLI_PREFETCH_EN 1


// Name:         DMAX_CH2_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH2_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH2_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 2. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 2 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH2_LMS 2'h0


// Name:         DMAX_CH2_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 2 pointed to by the content of CH2_SSTATAR
// register and store it in CH2_SSTAT register if CH2_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH2_SSTAT location of linked list at end of each block transfer if DMAX_CH2_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH2_SRC_STAT_EN 0


// Name:         DMAX_CH2_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 2 pointed to by the content of
// CHx_DSTATAR register and store it in CH2_DSTAT register if CH2_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH2_DSTAT location of linked list at end of each block transfer if DMAX_CH2_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH2_DST_STAT_EN 0


// Name:         DMAX_CH2_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH2_MULTI_BLK_TYPE == 0 || DMAX_CH2_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH2_CTL, CH2_LLP_STATUS, CH2_SSTAT and CH2_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH2_LLI_WB_EN 1


// Name:         DMAX_CH2_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH2_RD_UID_EN 0


// Name:         DMAX_CH2_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH2_WR_UID_EN 0


// Name:         DMAX_CH2_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH2_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH2_RD_UID 2


// Name:         DMAX_CH2_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH2_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH2_WR_UID 2


// Name:         DMAX_CH2_REORDER_BUFF_DEPTH
// Default:      256 (DMAX_CH2_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH2_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH2_REORDER_BUFF_DEPTH 256


// Name:         DMAX_CH2_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=2) && (DMAX_CH2_RD_UID_EN==0) &&
//               (DMAX_CH2_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH2_CRC_EN 0


// Name:         DMAX_CH3_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 3 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH3_FIFO_DEPTH 8


// Name:         DMAX_CH3_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 3 (CH3_CTL.SRC_MSIZE and CH3_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH3_MAX_MSIZE 8


// Name:         DMAX_CH3_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH3_BLOCK_TS.BLOCK_TS), that can be programmed for channel 3. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH3_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH3_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH3_MAX_BLOCK_TS 31


// Name:         DMAX_CH3_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 3. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH3_MAX_AMBA_BURST_LENGTH <= DMAX_CH3_MAX_BLOCK_TS
//  - DMAX_CH3_MAX_AMBA_BURST_LENGTH <= DMAX_CH3_MAX_MSIZE
`define APU_DMAX_CH3_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH3_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 3. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH3_LOCK_EN 0


// Name:         DMAX_CH3_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 3. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH3_TT_FC 4'h8


// Name:         DMAX_CH3_FC
// Default:      No Hardcode (DMAX_CH3_TT_FC == 8 ? 0 : (DMAX_CH3_TT_FC <= 3 ? 1 :
//               (DMAX_CH3_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 3 Flow Controller
`define APU_DMAX_CH3_FC 0


// Name:         DMAX_CH3_TT
// Default:      No Hardcode (DMAX_CH3_TT_FC == 8 ? 0 : (DMAX_CH3_TT_FC == 0 ? 1 :
//               (DMAX_CH3_TT_FC == 1 || DMAX_CH3_TT_FC == 6 ? 3: (DMAX_CH3_TT_FC == 2
//               || DMAX_CH3_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 3 Transfer Type
`define APU_DMAX_CH3_TT 0


// Name:         DMAX_CH3_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 3. If this is not hardcoded, software can program
// the source of channel 3 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH3_SMS 2'h0


// Name:         DMAX_CH3_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 3 destination. If this is not hardcoded, then software can
// program the destination of channel 3 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH3_DMS 2'h0


// Name:         DMAX_CH3_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 3. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH3_STW 32


// Name:         DMAX_CH3_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 3. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH3_DTW 32


// Name:         DMAX_CH3_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH3_MULTI_BLK_EN==1) && ((DMAX_CH3_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH3_MULTI_BLK_TYPE ==2) || (DMAX_CH3_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH3_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 3. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH3_SHADOW_REG_EN 0


// Name:         DMAX_CH3_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 3. If this option is set to 0, then hardware
// hardwires channel 3 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH3_MULTI_BLK_EN 0


// Name:         DMAX_CH3_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH3_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 3. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH3_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH3_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH3_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH3_MULTI_BLK_TYPE == 6 || DMAX_CH3_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH3_MULTI_BLK_TYPE == 1 || DMAX_CH3_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH3_MULTI_BLK_TYPE == 7 || DMAX_CH3_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH3_MULTI_BLK_TYPE == 2 || DMAX_CH3_MULTI_BLK_TYPE == 5 || DMAX_CH3_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH3_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH3_MULTI_BLK_TYPE == 10 || DMAX_CH3_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 3 Destination MultiBlock Type
`define APU_DMAX_CH3_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH3_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH3_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH3_MULTI_BLK_TYPE == 2 || DMAX_CH3_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH3_MULTI_BLK_TYPE == 3 || DMAX_CH3_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH3_MULTI_BLK_TYPE == 5 || DMAX_CH3_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH3_MULTI_BLK_TYPE == 6 || DMAX_CH3_MULTI_BLK_TYPE == 7 || DMAX_CH3_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH3_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH3_MULTI_BLK_TYPE == 12 || DMAX_CH3_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 3 Source MultiBlock Type
`define APU_DMAX_CH3_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH3_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH3_MULTI_BLK_EN==1) && (DMAX_CH3_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH3_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 3. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH3_LLI_PREFETCH_EN 0


// Name:         DMAX_CH3_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH3_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH3_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 3. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 3 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH3_LMS 2'h0


// Name:         DMAX_CH3_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 3 pointed to by the content of CH3_SSTATAR
// register and store it in CH3_SSTAT register if CH3_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH3_SSTAT location of linked list at end of each block transfer if DMAX_CH3_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH3_SRC_STAT_EN 0


// Name:         DMAX_CH3_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 3 pointed to by the content of
// CHx_DSTATAR register and store it in CH3_DSTAT register if CH3_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH3_DSTAT location of linked list at end of each block transfer if DMAX_CH3_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH3_DST_STAT_EN 0


// Name:         DMAX_CH3_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH3_MULTI_BLK_TYPE == 0 || DMAX_CH3_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH3_CTL, CH3_LLP_STATUS, CH3_SSTAT and CH3_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH3_LLI_WB_EN 0


// Name:         DMAX_CH3_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH3_RD_UID_EN 0


// Name:         DMAX_CH3_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH3_WR_UID_EN 0


// Name:         DMAX_CH3_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH3_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH3_RD_UID 2


// Name:         DMAX_CH3_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH3_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH3_WR_UID 2


// Name:         DMAX_CH3_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH3_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH3_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH3_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH3_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=3) && (DMAX_CH3_RD_UID_EN==0) &&
//               (DMAX_CH3_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH3_CRC_EN 0


// Name:         DMAX_CH4_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 4 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH4_FIFO_DEPTH 8


// Name:         DMAX_CH4_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 4 (CH4_CTL.SRC_MSIZE and CH4_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH4_MAX_MSIZE 8


// Name:         DMAX_CH4_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH4_BLOCK_TS.BLOCK_TS), that can be programmed for channel 4. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH4_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH4_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH4_MAX_BLOCK_TS 31


// Name:         DMAX_CH4_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 4. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH4_MAX_AMBA_BURST_LENGTH <= DMAX_CH4_MAX_BLOCK_TS
//  - DMAX_CH4_MAX_AMBA_BURST_LENGTH <= DMAX_CH4_MAX_MSIZE
`define APU_DMAX_CH4_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH4_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 4. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH4_LOCK_EN 0


// Name:         DMAX_CH4_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 4. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH4_TT_FC 4'h8


// Name:         DMAX_CH4_FC
// Default:      No Hardcode (DMAX_CH4_TT_FC == 8 ? 0 : (DMAX_CH4_TT_FC <= 3 ? 1 :
//               (DMAX_CH4_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 4 Flow Controller
`define APU_DMAX_CH4_FC 0


// Name:         DMAX_CH4_TT
// Default:      No Hardcode (DMAX_CH4_TT_FC == 8 ? 0 : (DMAX_CH4_TT_FC == 0 ? 1 :
//               (DMAX_CH4_TT_FC == 1 || DMAX_CH4_TT_FC == 6 ? 3: (DMAX_CH4_TT_FC == 2
//               || DMAX_CH4_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 4 Transfer Type
`define APU_DMAX_CH4_TT 0


// Name:         DMAX_CH4_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 4. If this is not hardcoded, software can program
// the source of channel 4 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH4_SMS 2'h0


// Name:         DMAX_CH4_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 4 destination. If this is not hardcoded, then software can
// program the destination of channel 4 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH4_DMS 2'h0


// Name:         DMAX_CH4_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 4. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH4_STW 32


// Name:         DMAX_CH4_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 4. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH4_DTW 32


// Name:         DMAX_CH4_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH4_MULTI_BLK_EN==1) && ((DMAX_CH4_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH4_MULTI_BLK_TYPE ==2) || (DMAX_CH4_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH4_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 4. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH4_SHADOW_REG_EN 0


// Name:         DMAX_CH4_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 4. If this option is set to 0, then hardware
// hardwires channel 4 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH4_MULTI_BLK_EN 0


// Name:         DMAX_CH4_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH4_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 4. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH4_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH4_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH4_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH4_MULTI_BLK_TYPE == 6 || DMAX_CH4_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH4_MULTI_BLK_TYPE == 1 || DMAX_CH4_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH4_MULTI_BLK_TYPE == 7 || DMAX_CH4_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH4_MULTI_BLK_TYPE == 2 || DMAX_CH4_MULTI_BLK_TYPE == 5 || DMAX_CH4_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH4_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH4_MULTI_BLK_TYPE == 10 || DMAX_CH4_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 4 Destination MultiBlock Type
`define APU_DMAX_CH4_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH4_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH4_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH4_MULTI_BLK_TYPE == 2 || DMAX_CH4_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH4_MULTI_BLK_TYPE == 3 || DMAX_CH4_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH4_MULTI_BLK_TYPE == 5 || DMAX_CH4_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH4_MULTI_BLK_TYPE == 6 || DMAX_CH4_MULTI_BLK_TYPE == 7 || DMAX_CH4_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH4_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH4_MULTI_BLK_TYPE == 12 || DMAX_CH4_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 4 Source MultiBlock Type
`define APU_DMAX_CH4_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH4_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH4_MULTI_BLK_EN==1) && (DMAX_CH4_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH4_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 4. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH4_LLI_PREFETCH_EN 0


// Name:         DMAX_CH4_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH4_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH4_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 4. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 4 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH4_LMS 2'h0


// Name:         DMAX_CH4_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 4 pointed to by the content of CH4_SSTATAR
// register and store it in CH4_SSTAT register if CH4_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH4_SSTAT location of linked list at end of each block transfer if DMAX_CH4_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH4_SRC_STAT_EN 0


// Name:         DMAX_CH4_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 4 pointed to by the content of
// CHx_DSTATAR register and store it in CH4_DSTAT register if CH4_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH4_DSTAT location of linked list at end of each block transfer if DMAX_CH4_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH4_DST_STAT_EN 0


// Name:         DMAX_CH4_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH4_MULTI_BLK_TYPE == 0 || DMAX_CH4_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH4_CTL, CH4_LLP_STATUS, CH4_SSTAT and CH4_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH4_LLI_WB_EN 0


// Name:         DMAX_CH4_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH4_RD_UID_EN 0


// Name:         DMAX_CH4_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH4_WR_UID_EN 0


// Name:         DMAX_CH4_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH4_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH4_RD_UID 2


// Name:         DMAX_CH4_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH4_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH4_WR_UID 2


// Name:         DMAX_CH4_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH4_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH4_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH4_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH4_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=4) && (DMAX_CH4_RD_UID_EN==0) &&
//               (DMAX_CH4_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH4_CRC_EN 0


// Name:         DMAX_CH5_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 5 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH5_FIFO_DEPTH 8


// Name:         DMAX_CH5_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 5 (CH5_CTL.SRC_MSIZE and CH5_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH5_MAX_MSIZE 8


// Name:         DMAX_CH5_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH5_BLOCK_TS.BLOCK_TS), that can be programmed for channel 5. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH5_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH5_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH5_MAX_BLOCK_TS 31


// Name:         DMAX_CH5_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 5. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH5_MAX_AMBA_BURST_LENGTH <= DMAX_CH5_MAX_BLOCK_TS
//  - DMAX_CH5_MAX_AMBA_BURST_LENGTH <= DMAX_CH5_MAX_MSIZE
`define APU_DMAX_CH5_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH5_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 5. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH5_LOCK_EN 0


// Name:         DMAX_CH5_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 5. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH5_TT_FC 4'h8


// Name:         DMAX_CH5_FC
// Default:      No Hardcode (DMAX_CH5_TT_FC == 8 ? 0 : (DMAX_CH5_TT_FC <= 3 ? 1 :
//               (DMAX_CH5_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 5 Flow Controller
`define APU_DMAX_CH5_FC 0


// Name:         DMAX_CH5_TT
// Default:      No Hardcode (DMAX_CH5_TT_FC == 8 ? 0 : (DMAX_CH5_TT_FC == 0 ? 1 :
//               (DMAX_CH5_TT_FC == 1 || DMAX_CH5_TT_FC == 6 ? 3: (DMAX_CH5_TT_FC == 2
//               || DMAX_CH5_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 5 Transfer Type
`define APU_DMAX_CH5_TT 0


// Name:         DMAX_CH5_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 5. If this is not hardcoded, software can program
// the source of channel 5 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH5_SMS 2'h0


// Name:         DMAX_CH5_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 5 destination. If this is not hardcoded, then software can
// program the destination of channel 5 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH5_DMS 2'h0


// Name:         DMAX_CH5_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 5. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH5_STW 32


// Name:         DMAX_CH5_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 5. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH5_DTW 32


// Name:         DMAX_CH5_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH5_MULTI_BLK_EN==1) && ((DMAX_CH5_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH5_MULTI_BLK_TYPE ==2) || (DMAX_CH5_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH5_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 5. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH5_SHADOW_REG_EN 0


// Name:         DMAX_CH5_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 5. If this option is set to 0, then hardware
// hardwires channel 5 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH5_MULTI_BLK_EN 0


// Name:         DMAX_CH5_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH5_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 5. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH5_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH5_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH5_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH5_MULTI_BLK_TYPE == 6 || DMAX_CH5_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH5_MULTI_BLK_TYPE == 1 || DMAX_CH5_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH5_MULTI_BLK_TYPE == 7 || DMAX_CH5_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH5_MULTI_BLK_TYPE == 2 || DMAX_CH5_MULTI_BLK_TYPE == 5 || DMAX_CH5_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH5_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH5_MULTI_BLK_TYPE == 10 || DMAX_CH5_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 5 Destination MultiBlock Type
`define APU_DMAX_CH5_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH5_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH5_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH5_MULTI_BLK_TYPE == 2 || DMAX_CH5_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH5_MULTI_BLK_TYPE == 3 || DMAX_CH5_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH5_MULTI_BLK_TYPE == 5 || DMAX_CH5_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH5_MULTI_BLK_TYPE == 6 || DMAX_CH5_MULTI_BLK_TYPE == 7 || DMAX_CH5_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH5_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH5_MULTI_BLK_TYPE == 12 || DMAX_CH5_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 5 Source MultiBlock Type
`define APU_DMAX_CH5_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH5_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH5_MULTI_BLK_EN==1) && (DMAX_CH5_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH5_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 5. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH5_LLI_PREFETCH_EN 0


// Name:         DMAX_CH5_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH5_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH5_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 5. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 5 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH5_LMS 2'h0


// Name:         DMAX_CH5_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 5 pointed to by the content of CH5_SSTATAR
// register and store it in CH5_SSTAT register if CH5_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH5_SSTAT location of linked list at end of each block transfer if DMAX_CH5_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH5_SRC_STAT_EN 0


// Name:         DMAX_CH5_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 5 pointed to by the content of
// CHx_DSTATAR register and store it in CH5_DSTAT register if CH5_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH5_DSTAT location of linked list at end of each block transfer if DMAX_CH5_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH5_DST_STAT_EN 0


// Name:         DMAX_CH5_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH5_MULTI_BLK_TYPE == 0 || DMAX_CH5_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH5_CTL, CH5_LLP_STATUS, CH5_SSTAT and CH5_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH5_LLI_WB_EN 0


// Name:         DMAX_CH5_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH5_RD_UID_EN 0


// Name:         DMAX_CH5_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH5_WR_UID_EN 0


// Name:         DMAX_CH5_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH5_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH5_RD_UID 2


// Name:         DMAX_CH5_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH5_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH5_WR_UID 2


// Name:         DMAX_CH5_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH5_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH5_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH5_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH5_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=5) && (DMAX_CH5_RD_UID_EN==0) &&
//               (DMAX_CH5_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH5_CRC_EN 0


// Name:         DMAX_CH6_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 6 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH6_FIFO_DEPTH 8


// Name:         DMAX_CH6_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 6 (CH6_CTL.SRC_MSIZE and CH6_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH6_MAX_MSIZE 8


// Name:         DMAX_CH6_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH6_BLOCK_TS.BLOCK_TS), that can be programmed for channel 6. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH6_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH6_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH6_MAX_BLOCK_TS 31


// Name:         DMAX_CH6_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 6. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH6_MAX_AMBA_BURST_LENGTH <= DMAX_CH6_MAX_BLOCK_TS
//  - DMAX_CH6_MAX_AMBA_BURST_LENGTH <= DMAX_CH6_MAX_MSIZE
`define APU_DMAX_CH6_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH6_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 6. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH6_LOCK_EN 0


// Name:         DMAX_CH6_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 6. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH6_TT_FC 4'h8


// Name:         DMAX_CH6_FC
// Default:      No Hardcode (DMAX_CH6_TT_FC == 8 ? 0 : (DMAX_CH6_TT_FC <= 3 ? 1 :
//               (DMAX_CH6_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 6 Flow Controller
`define APU_DMAX_CH6_FC 0


// Name:         DMAX_CH6_TT
// Default:      No Hardcode (DMAX_CH6_TT_FC == 8 ? 0 : (DMAX_CH6_TT_FC == 0 ? 1 :
//               (DMAX_CH6_TT_FC == 1 || DMAX_CH6_TT_FC == 6 ? 3: (DMAX_CH6_TT_FC == 2
//               || DMAX_CH6_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 6 Transfer Type
`define APU_DMAX_CH6_TT 0


// Name:         DMAX_CH6_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 6. If this is not hardcoded, software can program
// the source of channel 6 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH6_SMS 2'h0


// Name:         DMAX_CH6_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 6 destination. If this is not hardcoded, then software can
// program the destination of channel 6 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH6_DMS 2'h0


// Name:         DMAX_CH6_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 6. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH6_STW 32


// Name:         DMAX_CH6_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 6. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH6_DTW 32


// Name:         DMAX_CH6_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH6_MULTI_BLK_EN==1) && ((DMAX_CH6_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH6_MULTI_BLK_TYPE ==2) || (DMAX_CH6_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH6_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 6. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH6_SHADOW_REG_EN 0


// Name:         DMAX_CH6_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 6. If this option is set to 0, then hardware
// hardwires channel 6 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH6_MULTI_BLK_EN 0


// Name:         DMAX_CH6_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH6_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 6. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH6_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH6_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH6_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH6_MULTI_BLK_TYPE == 6 || DMAX_CH6_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH6_MULTI_BLK_TYPE == 1 || DMAX_CH6_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH6_MULTI_BLK_TYPE == 7 || DMAX_CH6_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH6_MULTI_BLK_TYPE == 2 || DMAX_CH6_MULTI_BLK_TYPE == 5 || DMAX_CH6_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH6_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH6_MULTI_BLK_TYPE == 10 || DMAX_CH6_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 6 Destination MultiBlock Type
`define APU_DMAX_CH6_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH6_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH6_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH6_MULTI_BLK_TYPE == 2 || DMAX_CH6_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH6_MULTI_BLK_TYPE == 3 || DMAX_CH6_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH6_MULTI_BLK_TYPE == 5 || DMAX_CH6_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH6_MULTI_BLK_TYPE == 6 || DMAX_CH6_MULTI_BLK_TYPE == 7 || DMAX_CH6_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH6_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH6_MULTI_BLK_TYPE == 12 || DMAX_CH6_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 6 Source MultiBlock Type
`define APU_DMAX_CH6_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH6_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH6_MULTI_BLK_EN==1) && (DMAX_CH6_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH6_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 6. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH6_LLI_PREFETCH_EN 0


// Name:         DMAX_CH6_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH6_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH6_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 6. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 6 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH6_LMS 2'h0


// Name:         DMAX_CH6_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 6 pointed to by the content of CH6_SSTATAR
// register and store it in CH6_SSTAT register if CH6_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH6_SSTAT location of linked list at end of each block transfer if DMAX_CH6_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH6_SRC_STAT_EN 0


// Name:         DMAX_CH6_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 6 pointed to by the content of
// CHx_DSTATAR register and store it in CH6_DSTAT register if CH6_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH6_DSTAT location of linked list at end of each block transfer if DMAX_CH6_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH6_DST_STAT_EN 0


// Name:         DMAX_CH6_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH6_MULTI_BLK_TYPE == 0 || DMAX_CH6_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH6_CTL, CH6_LLP_STATUS, CH6_SSTAT and CH6_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH6_LLI_WB_EN 0


// Name:         DMAX_CH6_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH6_RD_UID_EN 0


// Name:         DMAX_CH6_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH6_WR_UID_EN 0


// Name:         DMAX_CH6_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH6_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH6_RD_UID 2


// Name:         DMAX_CH6_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH6_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH6_WR_UID 2


// Name:         DMAX_CH6_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH6_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH6_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH6_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH6_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=6) && (DMAX_CH6_RD_UID_EN==0) &&
//               (DMAX_CH6_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH6_CRC_EN 0


// Name:         DMAX_CH7_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 7 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH7_FIFO_DEPTH 8


// Name:         DMAX_CH7_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 7 (CH7_CTL.SRC_MSIZE and CH7_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH7_MAX_MSIZE 8


// Name:         DMAX_CH7_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH7_BLOCK_TS.BLOCK_TS), that can be programmed for channel 7. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH7_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH7_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH7_MAX_BLOCK_TS 31


// Name:         DMAX_CH7_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 7. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH7_MAX_AMBA_BURST_LENGTH <= DMAX_CH7_MAX_BLOCK_TS
//  - DMAX_CH7_MAX_AMBA_BURST_LENGTH <= DMAX_CH7_MAX_MSIZE
`define APU_DMAX_CH7_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH7_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 7. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH7_LOCK_EN 0


// Name:         DMAX_CH7_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 7. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH7_TT_FC 4'h8


// Name:         DMAX_CH7_FC
// Default:      No Hardcode (DMAX_CH7_TT_FC == 8 ? 0 : (DMAX_CH7_TT_FC <= 3 ? 1 :
//               (DMAX_CH7_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 7 Flow Controller
`define APU_DMAX_CH7_FC 0


// Name:         DMAX_CH7_TT
// Default:      No Hardcode (DMAX_CH7_TT_FC == 8 ? 0 : (DMAX_CH7_TT_FC == 0 ? 1 :
//               (DMAX_CH7_TT_FC == 1 || DMAX_CH7_TT_FC == 6 ? 3: (DMAX_CH7_TT_FC == 2
//               || DMAX_CH7_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 7 Transfer Type
`define APU_DMAX_CH7_TT 0


// Name:         DMAX_CH7_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 7. If this is not hardcoded, software can program
// the source of channel 7 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH7_SMS 2'h0


// Name:         DMAX_CH7_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 7 destination. If this is not hardcoded, then software can
// program the destination of channel 7 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH7_DMS 2'h0


// Name:         DMAX_CH7_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 7. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH7_STW 32


// Name:         DMAX_CH7_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 7. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH7_DTW 32


// Name:         DMAX_CH7_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH7_MULTI_BLK_EN==1) && ((DMAX_CH7_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH7_MULTI_BLK_TYPE ==2) || (DMAX_CH7_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH7_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 7. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH7_SHADOW_REG_EN 0


// Name:         DMAX_CH7_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 7. If this option is set to 0, then hardware
// hardwires channel 7 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH7_MULTI_BLK_EN 0


// Name:         DMAX_CH7_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH7_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 7. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH7_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH7_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH7_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH7_MULTI_BLK_TYPE == 6 || DMAX_CH7_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH7_MULTI_BLK_TYPE == 1 || DMAX_CH7_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH7_MULTI_BLK_TYPE == 7 || DMAX_CH7_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH7_MULTI_BLK_TYPE == 2 || DMAX_CH7_MULTI_BLK_TYPE == 5 || DMAX_CH7_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH7_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH7_MULTI_BLK_TYPE == 10 || DMAX_CH7_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 7 Destination MultiBlock Type
`define APU_DMAX_CH7_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH7_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH7_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH7_MULTI_BLK_TYPE == 2 || DMAX_CH7_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH7_MULTI_BLK_TYPE == 3 || DMAX_CH7_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH7_MULTI_BLK_TYPE == 5 || DMAX_CH7_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH7_MULTI_BLK_TYPE == 6 || DMAX_CH7_MULTI_BLK_TYPE == 7 || DMAX_CH7_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH7_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH7_MULTI_BLK_TYPE == 12 || DMAX_CH7_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 7 Source MultiBlock Type
`define APU_DMAX_CH7_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH7_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH7_MULTI_BLK_EN==1) && (DMAX_CH7_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH7_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 7. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH7_LLI_PREFETCH_EN 0


// Name:         DMAX_CH7_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH7_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH7_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 7. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 7 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH7_LMS 2'h0


// Name:         DMAX_CH7_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 7 pointed to by the content of CH7_SSTATAR
// register and store it in CH7_SSTAT register if CH7_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH7_SSTAT location of linked list at end of each block transfer if DMAX_CH7_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH7_SRC_STAT_EN 0


// Name:         DMAX_CH7_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 7 pointed to by the content of
// CHx_DSTATAR register and store it in CH7_DSTAT register if CH7_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH7_DSTAT location of linked list at end of each block transfer if DMAX_CH7_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH7_DST_STAT_EN 0


// Name:         DMAX_CH7_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH7_MULTI_BLK_TYPE == 0 || DMAX_CH7_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH7_CTL, CH7_LLP_STATUS, CH7_SSTAT and CH7_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH7_LLI_WB_EN 0


// Name:         DMAX_CH7_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH7_RD_UID_EN 0


// Name:         DMAX_CH7_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH7_WR_UID_EN 0


// Name:         DMAX_CH7_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH7_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH7_RD_UID 2


// Name:         DMAX_CH7_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH7_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH7_WR_UID 2


// Name:         DMAX_CH7_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH7_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH7_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH7_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH7_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=7) && (DMAX_CH7_RD_UID_EN==0) &&
//               (DMAX_CH7_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH7_CRC_EN 0


// Name:         DMAX_CH8_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 8 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH8_FIFO_DEPTH 8


// Name:         DMAX_CH8_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 8 (CH8_CTL.SRC_MSIZE and CH8_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH8_MAX_MSIZE 8


// Name:         DMAX_CH8_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH8_BLOCK_TS.BLOCK_TS), that can be programmed for channel 8. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH8_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH8_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH8_MAX_BLOCK_TS 31


// Name:         DMAX_CH8_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 8. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH8_MAX_AMBA_BURST_LENGTH <= DMAX_CH8_MAX_BLOCK_TS
//  - DMAX_CH8_MAX_AMBA_BURST_LENGTH <= DMAX_CH8_MAX_MSIZE
`define APU_DMAX_CH8_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH8_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 8. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH8_LOCK_EN 0


// Name:         DMAX_CH8_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 8. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH8_TT_FC 4'h8


// Name:         DMAX_CH8_FC
// Default:      No Hardcode (DMAX_CH8_TT_FC == 8 ? 0 : (DMAX_CH8_TT_FC <= 3 ? 1 :
//               (DMAX_CH8_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 8 Flow Controller
`define APU_DMAX_CH8_FC 0


// Name:         DMAX_CH8_TT
// Default:      No Hardcode (DMAX_CH8_TT_FC == 8 ? 0 : (DMAX_CH8_TT_FC == 0 ? 1 :
//               (DMAX_CH8_TT_FC == 1 || DMAX_CH8_TT_FC == 6 ? 3: (DMAX_CH8_TT_FC == 2
//               || DMAX_CH8_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 8 Transfer Type
`define APU_DMAX_CH8_TT 0


// Name:         DMAX_CH8_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 8. If this is not hardcoded, software can program
// the source of channel 8 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH8_SMS 2'h0


// Name:         DMAX_CH8_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 8 destination. If this is not hardcoded, then software can
// program the destination of channel 8 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH8_DMS 2'h0


// Name:         DMAX_CH8_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 8. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH8_STW 32


// Name:         DMAX_CH8_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 8. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH8_DTW 32


// Name:         DMAX_CH8_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH8_MULTI_BLK_EN==1) && ((DMAX_CH8_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH8_MULTI_BLK_TYPE ==2) || (DMAX_CH8_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH8_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 8. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH8_SHADOW_REG_EN 0


// Name:         DMAX_CH8_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 8. If this option is set to 0, then hardware
// hardwires channel 8 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH8_MULTI_BLK_EN 0


// Name:         DMAX_CH8_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH8_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 8. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH8_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH8_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH8_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH8_MULTI_BLK_TYPE == 6 || DMAX_CH8_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH8_MULTI_BLK_TYPE == 1 || DMAX_CH8_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH8_MULTI_BLK_TYPE == 7 || DMAX_CH8_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH8_MULTI_BLK_TYPE == 2 || DMAX_CH8_MULTI_BLK_TYPE == 5 || DMAX_CH8_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH8_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH8_MULTI_BLK_TYPE == 10 || DMAX_CH8_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 8 Destination MultiBlock Type
`define APU_DMAX_CH8_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH8_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH8_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH8_MULTI_BLK_TYPE == 2 || DMAX_CH8_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH8_MULTI_BLK_TYPE == 3 || DMAX_CH8_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH8_MULTI_BLK_TYPE == 5 || DMAX_CH8_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH8_MULTI_BLK_TYPE == 6 || DMAX_CH8_MULTI_BLK_TYPE == 7 || DMAX_CH8_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH8_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH8_MULTI_BLK_TYPE == 12 || DMAX_CH8_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 8 Source MultiBlock Type
`define APU_DMAX_CH8_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH8_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH8_MULTI_BLK_EN==1) && (DMAX_CH8_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH8_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 8. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH8_LLI_PREFETCH_EN 0


// Name:         DMAX_CH8_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH8_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH8_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 8. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 8 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH8_LMS 2'h0


// Name:         DMAX_CH8_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 8 pointed to by the content of CH8_SSTATAR
// register and store it in CH8_SSTAT register if CH8_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH8_SSTAT location of linked list at end of each block transfer if DMAX_CH8_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH8_SRC_STAT_EN 0


// Name:         DMAX_CH8_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 8 pointed to by the content of
// CHx_DSTATAR register and store it in CH8_DSTAT register if CH8_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH8_DSTAT location of linked list at end of each block transfer if DMAX_CH8_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH8_DST_STAT_EN 0


// Name:         DMAX_CH8_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH8_MULTI_BLK_TYPE == 0 || DMAX_CH8_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH8_CTL, CH8_LLP_STATUS, CH8_SSTAT and CH8_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH8_LLI_WB_EN 0


// Name:         DMAX_CH8_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH8_RD_UID_EN 0


// Name:         DMAX_CH8_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH8_WR_UID_EN 0


// Name:         DMAX_CH8_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH8_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH8_RD_UID 2


// Name:         DMAX_CH8_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH8_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH8_WR_UID 2


// Name:         DMAX_CH8_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH8_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH8_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH8_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH8_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=8) && (DMAX_CH8_RD_UID_EN==0) &&
//               (DMAX_CH8_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH8_CRC_EN 0


// Name:         DMAX_CH9_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 9 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH9_FIFO_DEPTH 8


// Name:         DMAX_CH9_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 9 (CH9_CTL.SRC_MSIZE and CH9_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH9_MAX_MSIZE 8


// Name:         DMAX_CH9_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH9_BLOCK_TS.BLOCK_TS), that can be programmed for channel 9. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH9_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH9_MAX_BLOCK_TS. This does
//  not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH9_MAX_BLOCK_TS 31


// Name:         DMAX_CH9_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 9. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH9_MAX_AMBA_BURST_LENGTH <= DMAX_CH9_MAX_BLOCK_TS
//  - DMAX_CH9_MAX_AMBA_BURST_LENGTH <= DMAX_CH9_MAX_MSIZE
`define APU_DMAX_CH9_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH9_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 9. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH9_LOCK_EN 0


// Name:         DMAX_CH9_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 9. If NO_HARDCODE is selected, then the transfer
// type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH9_TT_FC 4'h8


// Name:         DMAX_CH9_FC
// Default:      No Hardcode (DMAX_CH9_TT_FC == 8 ? 0 : (DMAX_CH9_TT_FC <= 3 ? 1 :
//               (DMAX_CH9_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 9 Flow Controller
`define APU_DMAX_CH9_FC 0


// Name:         DMAX_CH9_TT
// Default:      No Hardcode (DMAX_CH9_TT_FC == 8 ? 0 : (DMAX_CH9_TT_FC == 0 ? 1 :
//               (DMAX_CH9_TT_FC == 1 || DMAX_CH9_TT_FC == 6 ? 3: (DMAX_CH9_TT_FC == 2
//               || DMAX_CH9_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 9 Transfer Type
`define APU_DMAX_CH9_TT 0


// Name:         DMAX_CH9_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 9. If this is not hardcoded, software can program
// the source of channel 9 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH9_SMS 2'h0


// Name:         DMAX_CH9_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 9 destination. If this is not hardcoded, then software can
// program the destination of channel 9 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation.
`define APU_DMAX_CH9_DMS 2'h0


// Name:         DMAX_CH9_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 9. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH9_STW 32


// Name:         DMAX_CH9_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 9. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH9_DTW 32


// Name:         DMAX_CH9_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH9_MULTI_BLK_EN==1) && ((DMAX_CH9_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH9_MULTI_BLK_TYPE ==2) || (DMAX_CH9_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH9_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 9. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH9_SHADOW_REG_EN 0


// Name:         DMAX_CH9_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 9. If this option is set to 0, then hardware
// hardwires channel 9 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH9_MULTI_BLK_EN 0


// Name:         DMAX_CH9_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH9_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 9. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH9_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH9_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH9_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH9_MULTI_BLK_TYPE == 6 || DMAX_CH9_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH9_MULTI_BLK_TYPE == 1 || DMAX_CH9_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH9_MULTI_BLK_TYPE == 7 || DMAX_CH9_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH9_MULTI_BLK_TYPE == 2 || DMAX_CH9_MULTI_BLK_TYPE == 5 || DMAX_CH9_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH9_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH9_MULTI_BLK_TYPE == 10 || DMAX_CH9_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 9 Destination MultiBlock Type
`define APU_DMAX_CH9_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH9_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH9_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH9_MULTI_BLK_TYPE == 2 || DMAX_CH9_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH9_MULTI_BLK_TYPE == 3 || DMAX_CH9_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH9_MULTI_BLK_TYPE == 5 || DMAX_CH9_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH9_MULTI_BLK_TYPE == 6 || DMAX_CH9_MULTI_BLK_TYPE == 7 || DMAX_CH9_MULTI_BLK_TYPE
//               == 8) ? 2 : ( (DMAX_CH9_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH9_MULTI_BLK_TYPE == 12 || DMAX_CH9_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 9 Source MultiBlock Type
`define APU_DMAX_CH9_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH9_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH9_MULTI_BLK_EN==1) && (DMAX_CH9_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH9_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 9. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH9_LLI_PREFETCH_EN 0


// Name:         DMAX_CH9_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH9_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH9_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 9. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 9 to
// be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH9_LMS 2'h0


// Name:         DMAX_CH9_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 9 pointed to by the content of CH9_SSTATAR
// register and store it in CH9_SSTAT register if CH9_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH9_SSTAT location of linked list at end of each block transfer if DMAX_CH9_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH9_SRC_STAT_EN 0


// Name:         DMAX_CH9_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 9 pointed to by the content of
// CHx_DSTATAR register and store it in CH9_DSTAT register if CH9_CTL.DST_STAT_EN bit is set to 1. This value is written back to the
// CH9_DSTAT location of linked list at end of each block transfer if DMAX_CH9_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH9_DST_STAT_EN 0


// Name:         DMAX_CH9_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH9_MULTI_BLK_TYPE == 0 || DMAX_CH9_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH9_CTL, CH9_LLP_STATUS, CH9_SSTAT and CH9_DSTAT registers at the
// end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either source
// or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH9_LLI_WB_EN 0


// Name:         DMAX_CH9_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH9_RD_UID_EN 0


// Name:         DMAX_CH9_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH9_WR_UID_EN 0


// Name:         DMAX_CH9_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH9_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH9_RD_UID 2


// Name:         DMAX_CH9_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH9_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH9_WR_UID 2


// Name:         DMAX_CH9_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH9_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH9_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH9_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH9_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=9) && (DMAX_CH9_RD_UID_EN==0) &&
//               (DMAX_CH9_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH9_CRC_EN 0


// Name:         DMAX_CH10_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 10 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH10_FIFO_DEPTH 8


// Name:         DMAX_CH10_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 10 (CH10_CTL.SRC_MSIZE and
// CH10_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH10_MAX_MSIZE 8


// Name:         DMAX_CH10_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH10_BLOCK_TS.BLOCK_TS), that can be programmed for channel 10. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH10_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH10_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH10_MAX_BLOCK_TS 31


// Name:         DMAX_CH10_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 10. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH10_MAX_AMBA_BURST_LENGTH <= DMAX_CH10_MAX_BLOCK_TS
//  - DMAX_CH10_MAX_AMBA_BURST_LENGTH <= DMAX_CH10_MAX_MSIZE
`define APU_DMAX_CH10_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH10_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 10. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH10_LOCK_EN 0


// Name:         DMAX_CH10_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 10. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH10_TT_FC 4'h8


// Name:         DMAX_CH10_FC
// Default:      No Hardcode (DMAX_CH10_TT_FC == 8 ? 0 : (DMAX_CH10_TT_FC <= 3 ? 1 :
//               (DMAX_CH10_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 10 Flow Controller
`define APU_DMAX_CH10_FC 0


// Name:         DMAX_CH10_TT
// Default:      No Hardcode (DMAX_CH10_TT_FC == 8 ? 0 : (DMAX_CH10_TT_FC == 0 ? 1 :
//               (DMAX_CH10_TT_FC == 1 || DMAX_CH10_TT_FC == 6 ? 3: (DMAX_CH10_TT_FC
//               == 2 || DMAX_CH10_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 10 Transfer Type
`define APU_DMAX_CH10_TT 0


// Name:         DMAX_CH10_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 10. If this is not hardcoded, software can program
// the source of channel 10 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH10_SMS 2'h0


// Name:         DMAX_CH10_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 10 destination. If this is not hardcoded, then software can
// program the destination of channel 10 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH10_DMS 2'h0


// Name:         DMAX_CH10_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 10. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH10_STW 32


// Name:         DMAX_CH10_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 10. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH10_DTW 32


// Name:         DMAX_CH10_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH10_MULTI_BLK_EN==1) && ((DMAX_CH10_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH10_MULTI_BLK_TYPE ==2) || (DMAX_CH10_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH10_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 10. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH10_SHADOW_REG_EN 0


// Name:         DMAX_CH10_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 10. If this option is set to 0, then hardware
// hardwires channel 10 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH10_MULTI_BLK_EN 0


// Name:         DMAX_CH10_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH10_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 10. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH10_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH10_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH10_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 6 || DMAX_CH10_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH10_MULTI_BLK_TYPE == 1 || DMAX_CH10_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 7 || DMAX_CH10_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH10_MULTI_BLK_TYPE == 2 || DMAX_CH10_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH10_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 10 || DMAX_CH10_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 10 Destination MultiBlock Type
`define APU_DMAX_CH10_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH10_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH10_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 2 || DMAX_CH10_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH10_MULTI_BLK_TYPE == 3 || DMAX_CH10_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 5 || DMAX_CH10_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH10_MULTI_BLK_TYPE == 6 || DMAX_CH10_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH10_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH10_MULTI_BLK_TYPE == 12 || DMAX_CH10_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 10 Source MultiBlock Type
`define APU_DMAX_CH10_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH10_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH10_MULTI_BLK_EN==1) && (DMAX_CH10_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH10_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 10. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH10_LLI_PREFETCH_EN 0


// Name:         DMAX_CH10_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH10_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH10_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 10. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 10
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH10_LMS 2'h0


// Name:         DMAX_CH10_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 10 pointed to by the content of CH10_SSTATAR
// register and store it in CH10_SSTAT register if CH10_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH10_SSTAT location of linked list at end of each block transfer if DMAX_CH10_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH10_SRC_STAT_EN 0


// Name:         DMAX_CH10_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 10 pointed to by the content of
// CHx_DSTATAR register and store it in CH10_DSTAT register if CH10_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH10_DSTAT location of linked list at end of each block transfer if DMAX_CH10_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH10_DST_STAT_EN 0


// Name:         DMAX_CH10_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH10_MULTI_BLK_TYPE == 0 || DMAX_CH10_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH10_CTL, CH10_LLP_STATUS, CH10_SSTAT and CH10_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH10_LLI_WB_EN 0


// Name:         DMAX_CH10_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH10_RD_UID_EN 0


// Name:         DMAX_CH10_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH10_WR_UID_EN 0


// Name:         DMAX_CH10_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH10_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH10_RD_UID 2


// Name:         DMAX_CH10_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH10_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH10_WR_UID 2


// Name:         DMAX_CH10_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH10_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH10_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH10_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH10_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=10) && (DMAX_CH10_RD_UID_EN==0) &&
//               (DMAX_CH10_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH10_CRC_EN 0


// Name:         DMAX_CH11_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 11 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH11_FIFO_DEPTH 8


// Name:         DMAX_CH11_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 11 (CH11_CTL.SRC_MSIZE and
// CH11_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH11_MAX_MSIZE 8


// Name:         DMAX_CH11_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH11_BLOCK_TS.BLOCK_TS), that can be programmed for channel 11. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH11_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH11_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH11_MAX_BLOCK_TS 31


// Name:         DMAX_CH11_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 11. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH11_MAX_AMBA_BURST_LENGTH <= DMAX_CH11_MAX_BLOCK_TS
//  - DMAX_CH11_MAX_AMBA_BURST_LENGTH <= DMAX_CH11_MAX_MSIZE
`define APU_DMAX_CH11_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH11_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 11. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH11_LOCK_EN 0


// Name:         DMAX_CH11_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 11. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH11_TT_FC 4'h8


// Name:         DMAX_CH11_FC
// Default:      No Hardcode (DMAX_CH11_TT_FC == 8 ? 0 : (DMAX_CH11_TT_FC <= 3 ? 1 :
//               (DMAX_CH11_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 11 Flow Controller
`define APU_DMAX_CH11_FC 0


// Name:         DMAX_CH11_TT
// Default:      No Hardcode (DMAX_CH11_TT_FC == 8 ? 0 : (DMAX_CH11_TT_FC == 0 ? 1 :
//               (DMAX_CH11_TT_FC == 1 || DMAX_CH11_TT_FC == 6 ? 3: (DMAX_CH11_TT_FC
//               == 2 || DMAX_CH11_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 11 Transfer Type
`define APU_DMAX_CH11_TT 0


// Name:         DMAX_CH11_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 11. If this is not hardcoded, software can program
// the source of channel 11 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH11_SMS 2'h0


// Name:         DMAX_CH11_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 11 destination. If this is not hardcoded, then software can
// program the destination of channel 11 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH11_DMS 2'h0


// Name:         DMAX_CH11_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 11. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH11_STW 32


// Name:         DMAX_CH11_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 11. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH11_DTW 32


// Name:         DMAX_CH11_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH11_MULTI_BLK_EN==1) && ((DMAX_CH11_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH11_MULTI_BLK_TYPE ==2) || (DMAX_CH11_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH11_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 11. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH11_SHADOW_REG_EN 0


// Name:         DMAX_CH11_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 11. If this option is set to 0, then hardware
// hardwires channel 11 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH11_MULTI_BLK_EN 0


// Name:         DMAX_CH11_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH11_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 11. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH11_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH11_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH11_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 6 || DMAX_CH11_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH11_MULTI_BLK_TYPE == 1 || DMAX_CH11_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 7 || DMAX_CH11_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH11_MULTI_BLK_TYPE == 2 || DMAX_CH11_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH11_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 10 || DMAX_CH11_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 11 Destination MultiBlock Type
`define APU_DMAX_CH11_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH11_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH11_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 2 || DMAX_CH11_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH11_MULTI_BLK_TYPE == 3 || DMAX_CH11_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 5 || DMAX_CH11_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH11_MULTI_BLK_TYPE == 6 || DMAX_CH11_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH11_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH11_MULTI_BLK_TYPE == 12 || DMAX_CH11_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 11 Source MultiBlock Type
`define APU_DMAX_CH11_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH11_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH11_MULTI_BLK_EN==1) && (DMAX_CH11_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH11_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 11. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH11_LLI_PREFETCH_EN 0


// Name:         DMAX_CH11_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH11_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH11_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 11. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 11
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH11_LMS 2'h0


// Name:         DMAX_CH11_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 11 pointed to by the content of CH11_SSTATAR
// register and store it in CH11_SSTAT register if CH11_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH11_SSTAT location of linked list at end of each block transfer if DMAX_CH11_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH11_SRC_STAT_EN 0


// Name:         DMAX_CH11_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 11 pointed to by the content of
// CHx_DSTATAR register and store it in CH11_DSTAT register if CH11_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH11_DSTAT location of linked list at end of each block transfer if DMAX_CH11_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH11_DST_STAT_EN 0


// Name:         DMAX_CH11_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH11_MULTI_BLK_TYPE == 0 || DMAX_CH11_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH11_CTL, CH11_LLP_STATUS, CH11_SSTAT and CH11_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH11_LLI_WB_EN 0


// Name:         DMAX_CH11_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH11_RD_UID_EN 0


// Name:         DMAX_CH11_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH11_WR_UID_EN 0


// Name:         DMAX_CH11_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH11_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH11_RD_UID 2


// Name:         DMAX_CH11_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH11_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH11_WR_UID 2


// Name:         DMAX_CH11_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH11_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH11_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH11_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH11_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=11) && (DMAX_CH11_RD_UID_EN==0) &&
//               (DMAX_CH11_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH11_CRC_EN 0


// Name:         DMAX_CH12_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 12 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH12_FIFO_DEPTH 8


// Name:         DMAX_CH12_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 12 (CH12_CTL.SRC_MSIZE and
// CH12_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH12_MAX_MSIZE 8


// Name:         DMAX_CH12_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH12_BLOCK_TS.BLOCK_TS), that can be programmed for channel 12. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH12_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH12_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH12_MAX_BLOCK_TS 31


// Name:         DMAX_CH12_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 12. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH12_MAX_AMBA_BURST_LENGTH <= DMAX_CH12_MAX_BLOCK_TS
//  - DMAX_CH12_MAX_AMBA_BURST_LENGTH <= DMAX_CH12_MAX_MSIZE
`define APU_DMAX_CH12_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH12_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 12. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH12_LOCK_EN 0


// Name:         DMAX_CH12_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 12. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH12_TT_FC 4'h8


// Name:         DMAX_CH12_FC
// Default:      No Hardcode (DMAX_CH12_TT_FC == 8 ? 0 : (DMAX_CH12_TT_FC <= 3 ? 1 :
//               (DMAX_CH12_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 12 Flow Controller
`define APU_DMAX_CH12_FC 0


// Name:         DMAX_CH12_TT
// Default:      No Hardcode (DMAX_CH12_TT_FC == 8 ? 0 : (DMAX_CH12_TT_FC == 0 ? 1 :
//               (DMAX_CH12_TT_FC == 1 || DMAX_CH12_TT_FC == 6 ? 3: (DMAX_CH12_TT_FC
//               == 2 || DMAX_CH12_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 12 Transfer Type
`define APU_DMAX_CH12_TT 0


// Name:         DMAX_CH12_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 12. If this is not hardcoded, software can program
// the source of channel 12 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH12_SMS 2'h0


// Name:         DMAX_CH12_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 12 destination. If this is not hardcoded, then software can
// program the destination of channel 12 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH12_DMS 2'h0


// Name:         DMAX_CH12_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 12. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH12_STW 32


// Name:         DMAX_CH12_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 12. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH12_DTW 32


// Name:         DMAX_CH12_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH12_MULTI_BLK_EN==1) && ((DMAX_CH12_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH12_MULTI_BLK_TYPE ==2) || (DMAX_CH12_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH12_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 12. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH12_SHADOW_REG_EN 0


// Name:         DMAX_CH12_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 12. If this option is set to 0, then hardware
// hardwires channel 12 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH12_MULTI_BLK_EN 0


// Name:         DMAX_CH12_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH12_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 12. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH12_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH12_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH12_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 6 || DMAX_CH12_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH12_MULTI_BLK_TYPE == 1 || DMAX_CH12_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 7 || DMAX_CH12_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH12_MULTI_BLK_TYPE == 2 || DMAX_CH12_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH12_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 10 || DMAX_CH12_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 12 Destination MultiBlock Type
`define APU_DMAX_CH12_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH12_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH12_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 2 || DMAX_CH12_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH12_MULTI_BLK_TYPE == 3 || DMAX_CH12_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 5 || DMAX_CH12_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH12_MULTI_BLK_TYPE == 6 || DMAX_CH12_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH12_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH12_MULTI_BLK_TYPE == 12 || DMAX_CH12_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 12 Source MultiBlock Type
`define APU_DMAX_CH12_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH12_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH12_MULTI_BLK_EN==1) && (DMAX_CH12_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH12_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 12. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH12_LLI_PREFETCH_EN 0


// Name:         DMAX_CH12_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH12_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH12_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 12. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 12
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH12_LMS 2'h0


// Name:         DMAX_CH12_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 12 pointed to by the content of CH12_SSTATAR
// register and store it in CH12_SSTAT register if CH12_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH12_SSTAT location of linked list at end of each block transfer if DMAX_CH12_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH12_SRC_STAT_EN 0


// Name:         DMAX_CH12_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 12 pointed to by the content of
// CHx_DSTATAR register and store it in CH12_DSTAT register if CH12_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH12_DSTAT location of linked list at end of each block transfer if DMAX_CH12_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH12_DST_STAT_EN 0


// Name:         DMAX_CH12_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH12_MULTI_BLK_TYPE == 0 || DMAX_CH12_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH12_CTL, CH12_LLP_STATUS, CH12_SSTAT and CH12_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH12_LLI_WB_EN 0


// Name:         DMAX_CH12_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH12_RD_UID_EN 0


// Name:         DMAX_CH12_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH12_WR_UID_EN 0


// Name:         DMAX_CH12_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH12_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH12_RD_UID 2


// Name:         DMAX_CH12_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH12_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH12_WR_UID 2


// Name:         DMAX_CH12_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH12_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH12_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH12_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH12_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=12) && (DMAX_CH12_RD_UID_EN==0) &&
//               (DMAX_CH12_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH12_CRC_EN 0


// Name:         DMAX_CH13_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 13 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH13_FIFO_DEPTH 8


// Name:         DMAX_CH13_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 13 (CH13_CTL.SRC_MSIZE and
// CH13_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH13_MAX_MSIZE 8


// Name:         DMAX_CH13_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH13_BLOCK_TS.BLOCK_TS), that can be programmed for channel 13. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH13_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH13_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH13_MAX_BLOCK_TS 31


// Name:         DMAX_CH13_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 13. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH13_MAX_AMBA_BURST_LENGTH <= DMAX_CH13_MAX_BLOCK_TS
//  - DMAX_CH13_MAX_AMBA_BURST_LENGTH <= DMAX_CH13_MAX_MSIZE
`define APU_DMAX_CH13_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH13_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 13. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH13_LOCK_EN 0


// Name:         DMAX_CH13_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 13. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH13_TT_FC 4'h8


// Name:         DMAX_CH13_FC
// Default:      No Hardcode (DMAX_CH13_TT_FC == 8 ? 0 : (DMAX_CH13_TT_FC <= 3 ? 1 :
//               (DMAX_CH13_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 13 Flow Controller
`define APU_DMAX_CH13_FC 0


// Name:         DMAX_CH13_TT
// Default:      No Hardcode (DMAX_CH13_TT_FC == 8 ? 0 : (DMAX_CH13_TT_FC == 0 ? 1 :
//               (DMAX_CH13_TT_FC == 1 || DMAX_CH13_TT_FC == 6 ? 3: (DMAX_CH13_TT_FC
//               == 2 || DMAX_CH13_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 13 Transfer Type
`define APU_DMAX_CH13_TT 0


// Name:         DMAX_CH13_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 13. If this is not hardcoded, software can program
// the source of channel 13 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH13_SMS 2'h0


// Name:         DMAX_CH13_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 13 destination. If this is not hardcoded, then software can
// program the destination of channel 13 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH13_DMS 2'h0


// Name:         DMAX_CH13_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 13. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH13_STW 32


// Name:         DMAX_CH13_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 13. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH13_DTW 32


// Name:         DMAX_CH13_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH13_MULTI_BLK_EN==1) && ((DMAX_CH13_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH13_MULTI_BLK_TYPE ==2) || (DMAX_CH13_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH13_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 13. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH13_SHADOW_REG_EN 0


// Name:         DMAX_CH13_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 13. If this option is set to 0, then hardware
// hardwires channel 13 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH13_MULTI_BLK_EN 0


// Name:         DMAX_CH13_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH13_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 13. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH13_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH13_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH13_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 6 || DMAX_CH13_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH13_MULTI_BLK_TYPE == 1 || DMAX_CH13_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 7 || DMAX_CH13_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH13_MULTI_BLK_TYPE == 2 || DMAX_CH13_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH13_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 10 || DMAX_CH13_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 13 Destination MultiBlock Type
`define APU_DMAX_CH13_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH13_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH13_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 2 || DMAX_CH13_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH13_MULTI_BLK_TYPE == 3 || DMAX_CH13_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 5 || DMAX_CH13_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH13_MULTI_BLK_TYPE == 6 || DMAX_CH13_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH13_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH13_MULTI_BLK_TYPE == 12 || DMAX_CH13_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 13 Source MultiBlock Type
`define APU_DMAX_CH13_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH13_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH13_MULTI_BLK_EN==1) && (DMAX_CH13_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH13_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 13. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH13_LLI_PREFETCH_EN 0


// Name:         DMAX_CH13_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH13_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH13_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 13. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 13
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH13_LMS 2'h0


// Name:         DMAX_CH13_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 13 pointed to by the content of CH13_SSTATAR
// register and store it in CH13_SSTAT register if CH13_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH13_SSTAT location of linked list at end of each block transfer if DMAX_CH13_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH13_SRC_STAT_EN 0


// Name:         DMAX_CH13_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 13 pointed to by the content of
// CHx_DSTATAR register and store it in CH13_DSTAT register if CH13_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH13_DSTAT location of linked list at end of each block transfer if DMAX_CH13_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH13_DST_STAT_EN 0


// Name:         DMAX_CH13_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH13_MULTI_BLK_TYPE == 0 || DMAX_CH13_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH13_CTL, CH13_LLP_STATUS, CH13_SSTAT and CH13_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH13_LLI_WB_EN 0


// Name:         DMAX_CH13_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH13_RD_UID_EN 0


// Name:         DMAX_CH13_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH13_WR_UID_EN 0


// Name:         DMAX_CH13_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH13_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH13_RD_UID 2


// Name:         DMAX_CH13_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH13_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH13_WR_UID 2


// Name:         DMAX_CH13_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH13_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH13_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH13_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH13_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=13) && (DMAX_CH13_RD_UID_EN==0) &&
//               (DMAX_CH13_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH13_CRC_EN 0


// Name:         DMAX_CH14_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 14 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH14_FIFO_DEPTH 8


// Name:         DMAX_CH14_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 14 (CH14_CTL.SRC_MSIZE and
// CH14_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH14_MAX_MSIZE 8


// Name:         DMAX_CH14_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH14_BLOCK_TS.BLOCK_TS), that can be programmed for channel 14. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH14_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH14_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH14_MAX_BLOCK_TS 31


// Name:         DMAX_CH14_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 14. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH14_MAX_AMBA_BURST_LENGTH <= DMAX_CH14_MAX_BLOCK_TS
//  - DMAX_CH14_MAX_AMBA_BURST_LENGTH <= DMAX_CH14_MAX_MSIZE
`define APU_DMAX_CH14_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH14_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 14. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH14_LOCK_EN 0


// Name:         DMAX_CH14_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 14. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH14_TT_FC 4'h8


// Name:         DMAX_CH14_FC
// Default:      No Hardcode (DMAX_CH14_TT_FC == 8 ? 0 : (DMAX_CH14_TT_FC <= 3 ? 1 :
//               (DMAX_CH14_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 14 Flow Controller
`define APU_DMAX_CH14_FC 0


// Name:         DMAX_CH14_TT
// Default:      No Hardcode (DMAX_CH14_TT_FC == 8 ? 0 : (DMAX_CH14_TT_FC == 0 ? 1 :
//               (DMAX_CH14_TT_FC == 1 || DMAX_CH14_TT_FC == 6 ? 3: (DMAX_CH14_TT_FC
//               == 2 || DMAX_CH14_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 14 Transfer Type
`define APU_DMAX_CH14_TT 0


// Name:         DMAX_CH14_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 14. If this is not hardcoded, software can program
// the source of channel 14 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH14_SMS 2'h0


// Name:         DMAX_CH14_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 14 destination. If this is not hardcoded, then software can
// program the destination of channel 14 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH14_DMS 2'h0


// Name:         DMAX_CH14_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 14. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH14_STW 32


// Name:         DMAX_CH14_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 14. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH14_DTW 32


// Name:         DMAX_CH14_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH14_MULTI_BLK_EN==1) && ((DMAX_CH14_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH14_MULTI_BLK_TYPE ==2) || (DMAX_CH14_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH14_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 14. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH14_SHADOW_REG_EN 0


// Name:         DMAX_CH14_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 14. If this option is set to 0, then hardware
// hardwires channel 14 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH14_MULTI_BLK_EN 0


// Name:         DMAX_CH14_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH14_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 14. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH14_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH14_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH14_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 6 || DMAX_CH14_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH14_MULTI_BLK_TYPE == 1 || DMAX_CH14_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 7 || DMAX_CH14_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH14_MULTI_BLK_TYPE == 2 || DMAX_CH14_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH14_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 10 || DMAX_CH14_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 14 Destination MultiBlock Type
`define APU_DMAX_CH14_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH14_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH14_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 2 || DMAX_CH14_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH14_MULTI_BLK_TYPE == 3 || DMAX_CH14_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 5 || DMAX_CH14_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH14_MULTI_BLK_TYPE == 6 || DMAX_CH14_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH14_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH14_MULTI_BLK_TYPE == 12 || DMAX_CH14_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 14 Source MultiBlock Type
`define APU_DMAX_CH14_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH14_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH14_MULTI_BLK_EN==1) && (DMAX_CH14_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH14_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 14. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH14_LLI_PREFETCH_EN 0


// Name:         DMAX_CH14_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH14_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH14_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 14. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 14
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH14_LMS 2'h0


// Name:         DMAX_CH14_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 14 pointed to by the content of CH14_SSTATAR
// register and store it in CH14_SSTAT register if CH14_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH14_SSTAT location of linked list at end of each block transfer if DMAX_CH14_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH14_SRC_STAT_EN 0


// Name:         DMAX_CH14_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 14 pointed to by the content of
// CHx_DSTATAR register and store it in CH14_DSTAT register if CH14_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH14_DSTAT location of linked list at end of each block transfer if DMAX_CH14_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH14_DST_STAT_EN 0


// Name:         DMAX_CH14_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH14_MULTI_BLK_TYPE == 0 || DMAX_CH14_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH14_CTL, CH14_LLP_STATUS, CH14_SSTAT and CH14_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH14_LLI_WB_EN 0


// Name:         DMAX_CH14_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH14_RD_UID_EN 0


// Name:         DMAX_CH14_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH14_WR_UID_EN 0


// Name:         DMAX_CH14_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH14_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH14_RD_UID 2


// Name:         DMAX_CH14_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH14_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH14_WR_UID 2


// Name:         DMAX_CH14_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH14_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH14_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH14_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH14_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=14) && (DMAX_CH14_RD_UID_EN==0) &&
//               (DMAX_CH14_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH14_CRC_EN 0


// Name:         DMAX_CH15_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 15 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH15_FIFO_DEPTH 8


// Name:         DMAX_CH15_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 15 (CH15_CTL.SRC_MSIZE and
// CH15_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH15_MAX_MSIZE 8


// Name:         DMAX_CH15_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH15_BLOCK_TS.BLOCK_TS), that can be programmed for channel 15. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH15_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH15_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH15_MAX_BLOCK_TS 31


// Name:         DMAX_CH15_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 15. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH15_MAX_AMBA_BURST_LENGTH <= DMAX_CH15_MAX_BLOCK_TS
//  - DMAX_CH15_MAX_AMBA_BURST_LENGTH <= DMAX_CH15_MAX_MSIZE
`define APU_DMAX_CH15_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH15_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 15. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH15_LOCK_EN 0


// Name:         DMAX_CH15_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 15. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH15_TT_FC 4'h8


// Name:         DMAX_CH15_FC
// Default:      No Hardcode (DMAX_CH15_TT_FC == 8 ? 0 : (DMAX_CH15_TT_FC <= 3 ? 1 :
//               (DMAX_CH15_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 15 Flow Controller
`define APU_DMAX_CH15_FC 0


// Name:         DMAX_CH15_TT
// Default:      No Hardcode (DMAX_CH15_TT_FC == 8 ? 0 : (DMAX_CH15_TT_FC == 0 ? 1 :
//               (DMAX_CH15_TT_FC == 1 || DMAX_CH15_TT_FC == 6 ? 3: (DMAX_CH15_TT_FC
//               == 2 || DMAX_CH15_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 15 Transfer Type
`define APU_DMAX_CH15_TT 0


// Name:         DMAX_CH15_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 15. If this is not hardcoded, software can program
// the source of channel 15 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH15_SMS 2'h0


// Name:         DMAX_CH15_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 15 destination. If this is not hardcoded, then software can
// program the destination of channel 15 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH15_DMS 2'h0


// Name:         DMAX_CH15_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 15. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH15_STW 32


// Name:         DMAX_CH15_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 15. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH15_DTW 32


// Name:         DMAX_CH15_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH15_MULTI_BLK_EN==1) && ((DMAX_CH15_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH15_MULTI_BLK_TYPE ==2) || (DMAX_CH15_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH15_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 15. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH15_SHADOW_REG_EN 0


// Name:         DMAX_CH15_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 15. If this option is set to 0, then hardware
// hardwires channel 15 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH15_MULTI_BLK_EN 0


// Name:         DMAX_CH15_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH15_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 15. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH15_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH15_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH15_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 6 || DMAX_CH15_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH15_MULTI_BLK_TYPE == 1 || DMAX_CH15_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 7 || DMAX_CH15_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH15_MULTI_BLK_TYPE == 2 || DMAX_CH15_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH15_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 10 || DMAX_CH15_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 15 Destination MultiBlock Type
`define APU_DMAX_CH15_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH15_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH15_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 2 || DMAX_CH15_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH15_MULTI_BLK_TYPE == 3 || DMAX_CH15_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 5 || DMAX_CH15_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH15_MULTI_BLK_TYPE == 6 || DMAX_CH15_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH15_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH15_MULTI_BLK_TYPE == 12 || DMAX_CH15_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 15 Source MultiBlock Type
`define APU_DMAX_CH15_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH15_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH15_MULTI_BLK_EN==1) && (DMAX_CH15_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH15_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 15. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH15_LLI_PREFETCH_EN 0


// Name:         DMAX_CH15_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH15_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH15_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 15. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 15
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH15_LMS 2'h0


// Name:         DMAX_CH15_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 15 pointed to by the content of CH15_SSTATAR
// register and store it in CH15_SSTAT register if CH15_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH15_SSTAT location of linked list at end of each block transfer if DMAX_CH15_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH15_SRC_STAT_EN 0


// Name:         DMAX_CH15_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 15 pointed to by the content of
// CHx_DSTATAR register and store it in CH15_DSTAT register if CH15_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH15_DSTAT location of linked list at end of each block transfer if DMAX_CH15_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH15_DST_STAT_EN 0


// Name:         DMAX_CH15_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH15_MULTI_BLK_TYPE == 0 || DMAX_CH15_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH15_CTL, CH15_LLP_STATUS, CH15_SSTAT and CH15_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH15_LLI_WB_EN 0


// Name:         DMAX_CH15_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH15_RD_UID_EN 0


// Name:         DMAX_CH15_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH15_WR_UID_EN 0


// Name:         DMAX_CH15_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH15_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH15_RD_UID 2


// Name:         DMAX_CH15_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH15_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH15_WR_UID 2


// Name:         DMAX_CH15_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH15_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH15_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH15_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH15_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=15) && (DMAX_CH15_RD_UID_EN==0) &&
//               (DMAX_CH15_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH15_CRC_EN 0


// Name:         DMAX_CH16_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 16 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH16_FIFO_DEPTH 8


// Name:         DMAX_CH16_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 16 (CH16_CTL.SRC_MSIZE and
// CH16_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH16_MAX_MSIZE 8


// Name:         DMAX_CH16_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH16_BLOCK_TS.BLOCK_TS), that can be programmed for channel 16. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH16_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH16_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH16_MAX_BLOCK_TS 31


// Name:         DMAX_CH16_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 16. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH16_MAX_AMBA_BURST_LENGTH <= DMAX_CH16_MAX_BLOCK_TS
//  - DMAX_CH16_MAX_AMBA_BURST_LENGTH <= DMAX_CH16_MAX_MSIZE
`define APU_DMAX_CH16_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH16_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 16. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH16_LOCK_EN 0


// Name:         DMAX_CH16_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 16. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH16_TT_FC 4'h8


// Name:         DMAX_CH16_FC
// Default:      No Hardcode (DMAX_CH16_TT_FC == 8 ? 0 : (DMAX_CH16_TT_FC <= 3 ? 1 :
//               (DMAX_CH16_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 16 Flow Controller
`define APU_DMAX_CH16_FC 0


// Name:         DMAX_CH16_TT
// Default:      No Hardcode (DMAX_CH16_TT_FC == 8 ? 0 : (DMAX_CH16_TT_FC == 0 ? 1 :
//               (DMAX_CH16_TT_FC == 1 || DMAX_CH16_TT_FC == 6 ? 3: (DMAX_CH16_TT_FC
//               == 2 || DMAX_CH16_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 16 Transfer Type
`define APU_DMAX_CH16_TT 0


// Name:         DMAX_CH16_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 16. If this is not hardcoded, software can program
// the source of channel 16 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH16_SMS 2'h0


// Name:         DMAX_CH16_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 16 destination. If this is not hardcoded, then software can
// program the destination of channel 16 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH16_DMS 2'h0


// Name:         DMAX_CH16_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 16. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH16_STW 32


// Name:         DMAX_CH16_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 16. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH16_DTW 32


// Name:         DMAX_CH16_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH16_MULTI_BLK_EN==1) && ((DMAX_CH16_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH16_MULTI_BLK_TYPE ==2) || (DMAX_CH16_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH16_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 16. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH16_SHADOW_REG_EN 0


// Name:         DMAX_CH16_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 16. If this option is set to 0, then hardware
// hardwires channel 16 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH16_MULTI_BLK_EN 0


// Name:         DMAX_CH16_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH16_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 16. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH16_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH16_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH16_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 6 || DMAX_CH16_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH16_MULTI_BLK_TYPE == 1 || DMAX_CH16_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 7 || DMAX_CH16_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH16_MULTI_BLK_TYPE == 2 || DMAX_CH16_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH16_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 10 || DMAX_CH16_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 16 Destination MultiBlock Type
`define APU_DMAX_CH16_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH16_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH16_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 2 || DMAX_CH16_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH16_MULTI_BLK_TYPE == 3 || DMAX_CH16_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 5 || DMAX_CH16_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH16_MULTI_BLK_TYPE == 6 || DMAX_CH16_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH16_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH16_MULTI_BLK_TYPE == 12 || DMAX_CH16_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 16 Source MultiBlock Type
`define APU_DMAX_CH16_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH16_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH16_MULTI_BLK_EN==1) && (DMAX_CH16_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH16_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 16. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH16_LLI_PREFETCH_EN 0


// Name:         DMAX_CH16_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH16_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH16_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 16. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 16
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH16_LMS 2'h0


// Name:         DMAX_CH16_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 16 pointed to by the content of CH16_SSTATAR
// register and store it in CH16_SSTAT register if CH16_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH16_SSTAT location of linked list at end of each block transfer if DMAX_CH16_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH16_SRC_STAT_EN 0


// Name:         DMAX_CH16_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 16 pointed to by the content of
// CHx_DSTATAR register and store it in CH16_DSTAT register if CH16_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH16_DSTAT location of linked list at end of each block transfer if DMAX_CH16_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH16_DST_STAT_EN 0


// Name:         DMAX_CH16_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH16_MULTI_BLK_TYPE == 0 || DMAX_CH16_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH16_CTL, CH16_LLP_STATUS, CH16_SSTAT and CH16_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH16_LLI_WB_EN 0


// Name:         DMAX_CH16_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH16_RD_UID_EN 0


// Name:         DMAX_CH16_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH16_WR_UID_EN 0


// Name:         DMAX_CH16_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH16_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH16_RD_UID 2


// Name:         DMAX_CH16_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH16_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH16_WR_UID 2


// Name:         DMAX_CH16_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH16_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH16_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH16_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH16_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=16) && (DMAX_CH16_RD_UID_EN==0) &&
//               (DMAX_CH16_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH16_CRC_EN 0


// Name:         DMAX_CH17_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 17 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH17_FIFO_DEPTH 8


// Name:         DMAX_CH17_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 17 (CH17_CTL.SRC_MSIZE and
// CH17_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH17_MAX_MSIZE 8


// Name:         DMAX_CH17_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH17_BLOCK_TS.BLOCK_TS), that can be programmed for channel 17. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH17_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH17_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH17_MAX_BLOCK_TS 31


// Name:         DMAX_CH17_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 17. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH17_MAX_AMBA_BURST_LENGTH <= DMAX_CH17_MAX_BLOCK_TS
//  - DMAX_CH17_MAX_AMBA_BURST_LENGTH <= DMAX_CH17_MAX_MSIZE
`define APU_DMAX_CH17_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH17_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 17. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH17_LOCK_EN 0


// Name:         DMAX_CH17_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 17. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH17_TT_FC 4'h8


// Name:         DMAX_CH17_FC
// Default:      No Hardcode (DMAX_CH17_TT_FC == 8 ? 0 : (DMAX_CH17_TT_FC <= 3 ? 1 :
//               (DMAX_CH17_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 17 Flow Controller
`define APU_DMAX_CH17_FC 0


// Name:         DMAX_CH17_TT
// Default:      No Hardcode (DMAX_CH17_TT_FC == 8 ? 0 : (DMAX_CH17_TT_FC == 0 ? 1 :
//               (DMAX_CH17_TT_FC == 1 || DMAX_CH17_TT_FC == 6 ? 3: (DMAX_CH17_TT_FC
//               == 2 || DMAX_CH17_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 17 Transfer Type
`define APU_DMAX_CH17_TT 0


// Name:         DMAX_CH17_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 17. If this is not hardcoded, software can program
// the source of channel 17 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH17_SMS 2'h0


// Name:         DMAX_CH17_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 17 destination. If this is not hardcoded, then software can
// program the destination of channel 17 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH17_DMS 2'h0


// Name:         DMAX_CH17_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 17. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH17_STW 32


// Name:         DMAX_CH17_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 17. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH17_DTW 32


// Name:         DMAX_CH17_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH17_MULTI_BLK_EN==1) && ((DMAX_CH17_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH17_MULTI_BLK_TYPE ==2) || (DMAX_CH17_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH17_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 17. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH17_SHADOW_REG_EN 0


// Name:         DMAX_CH17_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 17. If this option is set to 0, then hardware
// hardwires channel 17 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH17_MULTI_BLK_EN 0


// Name:         DMAX_CH17_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH17_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 17. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH17_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH17_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH17_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 6 || DMAX_CH17_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH17_MULTI_BLK_TYPE == 1 || DMAX_CH17_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 7 || DMAX_CH17_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH17_MULTI_BLK_TYPE == 2 || DMAX_CH17_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH17_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 10 || DMAX_CH17_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 17 Destination MultiBlock Type
`define APU_DMAX_CH17_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH17_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH17_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 2 || DMAX_CH17_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH17_MULTI_BLK_TYPE == 3 || DMAX_CH17_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 5 || DMAX_CH17_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH17_MULTI_BLK_TYPE == 6 || DMAX_CH17_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH17_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH17_MULTI_BLK_TYPE == 12 || DMAX_CH17_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 17 Source MultiBlock Type
`define APU_DMAX_CH17_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH17_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH17_MULTI_BLK_EN==1) && (DMAX_CH17_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH17_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 17. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH17_LLI_PREFETCH_EN 0


// Name:         DMAX_CH17_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH17_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH17_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 17. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 17
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH17_LMS 2'h0


// Name:         DMAX_CH17_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 17 pointed to by the content of CH17_SSTATAR
// register and store it in CH17_SSTAT register if CH17_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH17_SSTAT location of linked list at end of each block transfer if DMAX_CH17_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH17_SRC_STAT_EN 0


// Name:         DMAX_CH17_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 17 pointed to by the content of
// CHx_DSTATAR register and store it in CH17_DSTAT register if CH17_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH17_DSTAT location of linked list at end of each block transfer if DMAX_CH17_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH17_DST_STAT_EN 0


// Name:         DMAX_CH17_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH17_MULTI_BLK_TYPE == 0 || DMAX_CH17_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH17_CTL, CH17_LLP_STATUS, CH17_SSTAT and CH17_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH17_LLI_WB_EN 0


// Name:         DMAX_CH17_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH17_RD_UID_EN 0


// Name:         DMAX_CH17_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH17_WR_UID_EN 0


// Name:         DMAX_CH17_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH17_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH17_RD_UID 2


// Name:         DMAX_CH17_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH17_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH17_WR_UID 2


// Name:         DMAX_CH17_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH17_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH17_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH17_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH17_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=17) && (DMAX_CH17_RD_UID_EN==0) &&
//               (DMAX_CH17_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH17_CRC_EN 0


// Name:         DMAX_CH18_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 18 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH18_FIFO_DEPTH 8


// Name:         DMAX_CH18_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 18 (CH18_CTL.SRC_MSIZE and
// CH18_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH18_MAX_MSIZE 8


// Name:         DMAX_CH18_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH18_BLOCK_TS.BLOCK_TS), that can be programmed for channel 18. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH18_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH18_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH18_MAX_BLOCK_TS 31


// Name:         DMAX_CH18_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 18. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH18_MAX_AMBA_BURST_LENGTH <= DMAX_CH18_MAX_BLOCK_TS
//  - DMAX_CH18_MAX_AMBA_BURST_LENGTH <= DMAX_CH18_MAX_MSIZE
`define APU_DMAX_CH18_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH18_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 18. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH18_LOCK_EN 0


// Name:         DMAX_CH18_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 18. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH18_TT_FC 4'h8


// Name:         DMAX_CH18_FC
// Default:      No Hardcode (DMAX_CH18_TT_FC == 8 ? 0 : (DMAX_CH18_TT_FC <= 3 ? 1 :
//               (DMAX_CH18_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 18 Flow Controller
`define APU_DMAX_CH18_FC 0


// Name:         DMAX_CH18_TT
// Default:      No Hardcode (DMAX_CH18_TT_FC == 8 ? 0 : (DMAX_CH18_TT_FC == 0 ? 1 :
//               (DMAX_CH18_TT_FC == 1 || DMAX_CH18_TT_FC == 6 ? 3: (DMAX_CH18_TT_FC
//               == 2 || DMAX_CH18_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 18 Transfer Type
`define APU_DMAX_CH18_TT 0


// Name:         DMAX_CH18_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 18. If this is not hardcoded, software can program
// the source of channel 18 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH18_SMS 2'h0


// Name:         DMAX_CH18_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 18 destination. If this is not hardcoded, then software can
// program the destination of channel 18 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH18_DMS 2'h0


// Name:         DMAX_CH18_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 18. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH18_STW 32


// Name:         DMAX_CH18_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 18. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH18_DTW 32


// Name:         DMAX_CH18_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH18_MULTI_BLK_EN==1) && ((DMAX_CH18_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH18_MULTI_BLK_TYPE ==2) || (DMAX_CH18_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH18_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 18. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH18_SHADOW_REG_EN 0


// Name:         DMAX_CH18_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 18. If this option is set to 0, then hardware
// hardwires channel 18 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH18_MULTI_BLK_EN 0


// Name:         DMAX_CH18_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH18_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 18. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH18_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH18_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH18_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 6 || DMAX_CH18_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH18_MULTI_BLK_TYPE == 1 || DMAX_CH18_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 7 || DMAX_CH18_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH18_MULTI_BLK_TYPE == 2 || DMAX_CH18_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH18_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 10 || DMAX_CH18_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 18 Destination MultiBlock Type
`define APU_DMAX_CH18_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH18_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH18_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 2 || DMAX_CH18_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH18_MULTI_BLK_TYPE == 3 || DMAX_CH18_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 5 || DMAX_CH18_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH18_MULTI_BLK_TYPE == 6 || DMAX_CH18_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH18_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH18_MULTI_BLK_TYPE == 12 || DMAX_CH18_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 18 Source MultiBlock Type
`define APU_DMAX_CH18_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH18_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH18_MULTI_BLK_EN==1) && (DMAX_CH18_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH18_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 18. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH18_LLI_PREFETCH_EN 0


// Name:         DMAX_CH18_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH18_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH18_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 18. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 18
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH18_LMS 2'h0


// Name:         DMAX_CH18_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 18 pointed to by the content of CH18_SSTATAR
// register and store it in CH18_SSTAT register if CH18_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH18_SSTAT location of linked list at end of each block transfer if DMAX_CH18_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH18_SRC_STAT_EN 0


// Name:         DMAX_CH18_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 18 pointed to by the content of
// CHx_DSTATAR register and store it in CH18_DSTAT register if CH18_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH18_DSTAT location of linked list at end of each block transfer if DMAX_CH18_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH18_DST_STAT_EN 0


// Name:         DMAX_CH18_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH18_MULTI_BLK_TYPE == 0 || DMAX_CH18_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH18_CTL, CH18_LLP_STATUS, CH18_SSTAT and CH18_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH18_LLI_WB_EN 0


// Name:         DMAX_CH18_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH18_RD_UID_EN 0


// Name:         DMAX_CH18_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH18_WR_UID_EN 0


// Name:         DMAX_CH18_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH18_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH18_RD_UID 2


// Name:         DMAX_CH18_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH18_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH18_WR_UID 2


// Name:         DMAX_CH18_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH18_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH18_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH18_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH18_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=18) && (DMAX_CH18_RD_UID_EN==0) &&
//               (DMAX_CH18_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH18_CRC_EN 0


// Name:         DMAX_CH19_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 19 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH19_FIFO_DEPTH 8


// Name:         DMAX_CH19_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 19 (CH19_CTL.SRC_MSIZE and
// CH19_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH19_MAX_MSIZE 8


// Name:         DMAX_CH19_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH19_BLOCK_TS.BLOCK_TS), that can be programmed for channel 19. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH19_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH19_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH19_MAX_BLOCK_TS 31


// Name:         DMAX_CH19_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 19. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH19_MAX_AMBA_BURST_LENGTH <= DMAX_CH19_MAX_BLOCK_TS
//  - DMAX_CH19_MAX_AMBA_BURST_LENGTH <= DMAX_CH19_MAX_MSIZE
`define APU_DMAX_CH19_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH19_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 19. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH19_LOCK_EN 0


// Name:         DMAX_CH19_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 19. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH19_TT_FC 4'h8


// Name:         DMAX_CH19_FC
// Default:      No Hardcode (DMAX_CH19_TT_FC == 8 ? 0 : (DMAX_CH19_TT_FC <= 3 ? 1 :
//               (DMAX_CH19_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 19 Flow Controller
`define APU_DMAX_CH19_FC 0


// Name:         DMAX_CH19_TT
// Default:      No Hardcode (DMAX_CH19_TT_FC == 8 ? 0 : (DMAX_CH19_TT_FC == 0 ? 1 :
//               (DMAX_CH19_TT_FC == 1 || DMAX_CH19_TT_FC == 6 ? 3: (DMAX_CH19_TT_FC
//               == 2 || DMAX_CH19_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 19 Transfer Type
`define APU_DMAX_CH19_TT 0


// Name:         DMAX_CH19_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 19. If this is not hardcoded, software can program
// the source of channel 19 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH19_SMS 2'h0


// Name:         DMAX_CH19_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 19 destination. If this is not hardcoded, then software can
// program the destination of channel 19 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH19_DMS 2'h0


// Name:         DMAX_CH19_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 19. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH19_STW 32


// Name:         DMAX_CH19_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 19. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH19_DTW 32


// Name:         DMAX_CH19_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH19_MULTI_BLK_EN==1) && ((DMAX_CH19_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH19_MULTI_BLK_TYPE ==2) || (DMAX_CH19_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH19_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 19. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH19_SHADOW_REG_EN 0


// Name:         DMAX_CH19_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 19. If this option is set to 0, then hardware
// hardwires channel 19 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH19_MULTI_BLK_EN 0


// Name:         DMAX_CH19_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH19_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 19. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH19_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH19_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH19_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 6 || DMAX_CH19_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH19_MULTI_BLK_TYPE == 1 || DMAX_CH19_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 7 || DMAX_CH19_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH19_MULTI_BLK_TYPE == 2 || DMAX_CH19_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH19_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 10 || DMAX_CH19_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 19 Destination MultiBlock Type
`define APU_DMAX_CH19_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH19_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH19_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 2 || DMAX_CH19_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH19_MULTI_BLK_TYPE == 3 || DMAX_CH19_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 5 || DMAX_CH19_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH19_MULTI_BLK_TYPE == 6 || DMAX_CH19_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH19_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH19_MULTI_BLK_TYPE == 12 || DMAX_CH19_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 19 Source MultiBlock Type
`define APU_DMAX_CH19_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH19_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH19_MULTI_BLK_EN==1) && (DMAX_CH19_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH19_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 19. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH19_LLI_PREFETCH_EN 0


// Name:         DMAX_CH19_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH19_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH19_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 19. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 19
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH19_LMS 2'h0


// Name:         DMAX_CH19_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 19 pointed to by the content of CH19_SSTATAR
// register and store it in CH19_SSTAT register if CH19_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH19_SSTAT location of linked list at end of each block transfer if DMAX_CH19_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH19_SRC_STAT_EN 0


// Name:         DMAX_CH19_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 19 pointed to by the content of
// CHx_DSTATAR register and store it in CH19_DSTAT register if CH19_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH19_DSTAT location of linked list at end of each block transfer if DMAX_CH19_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH19_DST_STAT_EN 0


// Name:         DMAX_CH19_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH19_MULTI_BLK_TYPE == 0 || DMAX_CH19_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH19_CTL, CH19_LLP_STATUS, CH19_SSTAT and CH19_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH19_LLI_WB_EN 0


// Name:         DMAX_CH19_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH19_RD_UID_EN 0


// Name:         DMAX_CH19_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH19_WR_UID_EN 0


// Name:         DMAX_CH19_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH19_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH19_RD_UID 2


// Name:         DMAX_CH19_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH19_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH19_WR_UID 2


// Name:         DMAX_CH19_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH19_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH19_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH19_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH19_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=19) && (DMAX_CH19_RD_UID_EN==0) &&
//               (DMAX_CH19_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH19_CRC_EN 0


// Name:         DMAX_CH20_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 20 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH20_FIFO_DEPTH 8


// Name:         DMAX_CH20_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 20 (CH20_CTL.SRC_MSIZE and
// CH20_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH20_MAX_MSIZE 8


// Name:         DMAX_CH20_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH20_BLOCK_TS.BLOCK_TS), that can be programmed for channel 20. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH20_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH20_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH20_MAX_BLOCK_TS 31


// Name:         DMAX_CH20_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 20. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH20_MAX_AMBA_BURST_LENGTH <= DMAX_CH20_MAX_BLOCK_TS
//  - DMAX_CH20_MAX_AMBA_BURST_LENGTH <= DMAX_CH20_MAX_MSIZE
`define APU_DMAX_CH20_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH20_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 20. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH20_LOCK_EN 0


// Name:         DMAX_CH20_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 20. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH20_TT_FC 4'h8


// Name:         DMAX_CH20_FC
// Default:      No Hardcode (DMAX_CH20_TT_FC == 8 ? 0 : (DMAX_CH20_TT_FC <= 3 ? 1 :
//               (DMAX_CH20_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 20 Flow Controller
`define APU_DMAX_CH20_FC 0


// Name:         DMAX_CH20_TT
// Default:      No Hardcode (DMAX_CH20_TT_FC == 8 ? 0 : (DMAX_CH20_TT_FC == 0 ? 1 :
//               (DMAX_CH20_TT_FC == 1 || DMAX_CH20_TT_FC == 6 ? 3: (DMAX_CH20_TT_FC
//               == 2 || DMAX_CH20_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 20 Transfer Type
`define APU_DMAX_CH20_TT 0


// Name:         DMAX_CH20_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 20. If this is not hardcoded, software can program
// the source of channel 20 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH20_SMS 2'h0


// Name:         DMAX_CH20_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 20 destination. If this is not hardcoded, then software can
// program the destination of channel 20 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH20_DMS 2'h0


// Name:         DMAX_CH20_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 20. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH20_STW 32


// Name:         DMAX_CH20_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 20. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH20_DTW 32


// Name:         DMAX_CH20_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH20_MULTI_BLK_EN==1) && ((DMAX_CH20_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH20_MULTI_BLK_TYPE ==2) || (DMAX_CH20_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH20_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 20. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH20_SHADOW_REG_EN 0


// Name:         DMAX_CH20_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 20. If this option is set to 0, then hardware
// hardwires channel 20 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH20_MULTI_BLK_EN 0


// Name:         DMAX_CH20_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH20_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 20. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH20_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH20_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH20_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 6 || DMAX_CH20_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH20_MULTI_BLK_TYPE == 1 || DMAX_CH20_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 7 || DMAX_CH20_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH20_MULTI_BLK_TYPE == 2 || DMAX_CH20_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH20_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 10 || DMAX_CH20_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 20 Destination MultiBlock Type
`define APU_DMAX_CH20_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH20_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH20_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 2 || DMAX_CH20_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH20_MULTI_BLK_TYPE == 3 || DMAX_CH20_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 5 || DMAX_CH20_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH20_MULTI_BLK_TYPE == 6 || DMAX_CH20_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH20_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH20_MULTI_BLK_TYPE == 12 || DMAX_CH20_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 20 Source MultiBlock Type
`define APU_DMAX_CH20_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH20_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH20_MULTI_BLK_EN==1) && (DMAX_CH20_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH20_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 20. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH20_LLI_PREFETCH_EN 0


// Name:         DMAX_CH20_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH20_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH20_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 20. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 20
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH20_LMS 2'h0


// Name:         DMAX_CH20_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 20 pointed to by the content of CH20_SSTATAR
// register and store it in CH20_SSTAT register if CH20_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH20_SSTAT location of linked list at end of each block transfer if DMAX_CH20_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH20_SRC_STAT_EN 0


// Name:         DMAX_CH20_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 20 pointed to by the content of
// CHx_DSTATAR register and store it in CH20_DSTAT register if CH20_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH20_DSTAT location of linked list at end of each block transfer if DMAX_CH20_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH20_DST_STAT_EN 0


// Name:         DMAX_CH20_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH20_MULTI_BLK_TYPE == 0 || DMAX_CH20_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH20_CTL, CH20_LLP_STATUS, CH20_SSTAT and CH20_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH20_LLI_WB_EN 0


// Name:         DMAX_CH20_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH20_RD_UID_EN 0


// Name:         DMAX_CH20_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH20_WR_UID_EN 0


// Name:         DMAX_CH20_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH20_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH20_RD_UID 2


// Name:         DMAX_CH20_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH20_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH20_WR_UID 2


// Name:         DMAX_CH20_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH20_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH20_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH20_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH20_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=20) && (DMAX_CH20_RD_UID_EN==0) &&
//               (DMAX_CH20_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH20_CRC_EN 0


// Name:         DMAX_CH21_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 21 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH21_FIFO_DEPTH 8


// Name:         DMAX_CH21_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 21 (CH21_CTL.SRC_MSIZE and
// CH21_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH21_MAX_MSIZE 8


// Name:         DMAX_CH21_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH21_BLOCK_TS.BLOCK_TS), that can be programmed for channel 21. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH21_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH21_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH21_MAX_BLOCK_TS 31


// Name:         DMAX_CH21_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 21. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH21_MAX_AMBA_BURST_LENGTH <= DMAX_CH21_MAX_BLOCK_TS
//  - DMAX_CH21_MAX_AMBA_BURST_LENGTH <= DMAX_CH21_MAX_MSIZE
`define APU_DMAX_CH21_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH21_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 21. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH21_LOCK_EN 0


// Name:         DMAX_CH21_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 21. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH21_TT_FC 4'h8


// Name:         DMAX_CH21_FC
// Default:      No Hardcode (DMAX_CH21_TT_FC == 8 ? 0 : (DMAX_CH21_TT_FC <= 3 ? 1 :
//               (DMAX_CH21_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 21 Flow Controller
`define APU_DMAX_CH21_FC 0


// Name:         DMAX_CH21_TT
// Default:      No Hardcode (DMAX_CH21_TT_FC == 8 ? 0 : (DMAX_CH21_TT_FC == 0 ? 1 :
//               (DMAX_CH21_TT_FC == 1 || DMAX_CH21_TT_FC == 6 ? 3: (DMAX_CH21_TT_FC
//               == 2 || DMAX_CH21_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 21 Transfer Type
`define APU_DMAX_CH21_TT 0


// Name:         DMAX_CH21_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 21. If this is not hardcoded, software can program
// the source of channel 21 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH21_SMS 2'h0


// Name:         DMAX_CH21_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 21 destination. If this is not hardcoded, then software can
// program the destination of channel 21 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH21_DMS 2'h0


// Name:         DMAX_CH21_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 21. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH21_STW 32


// Name:         DMAX_CH21_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 21. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH21_DTW 32


// Name:         DMAX_CH21_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH21_MULTI_BLK_EN==1) && ((DMAX_CH21_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH21_MULTI_BLK_TYPE ==2) || (DMAX_CH21_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH21_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 21. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH21_SHADOW_REG_EN 0


// Name:         DMAX_CH21_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 21. If this option is set to 0, then hardware
// hardwires channel 21 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH21_MULTI_BLK_EN 0


// Name:         DMAX_CH21_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH21_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 21. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH21_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH21_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH21_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 6 || DMAX_CH21_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH21_MULTI_BLK_TYPE == 1 || DMAX_CH21_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 7 || DMAX_CH21_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH21_MULTI_BLK_TYPE == 2 || DMAX_CH21_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH21_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 10 || DMAX_CH21_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 21 Destination MultiBlock Type
`define APU_DMAX_CH21_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH21_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH21_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 2 || DMAX_CH21_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH21_MULTI_BLK_TYPE == 3 || DMAX_CH21_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 5 || DMAX_CH21_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH21_MULTI_BLK_TYPE == 6 || DMAX_CH21_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH21_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH21_MULTI_BLK_TYPE == 12 || DMAX_CH21_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 21 Source MultiBlock Type
`define APU_DMAX_CH21_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH21_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH21_MULTI_BLK_EN==1) && (DMAX_CH21_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH21_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 21. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH21_LLI_PREFETCH_EN 0


// Name:         DMAX_CH21_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH21_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH21_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 21. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 21
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH21_LMS 2'h0


// Name:         DMAX_CH21_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 21 pointed to by the content of CH21_SSTATAR
// register and store it in CH21_SSTAT register if CH21_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH21_SSTAT location of linked list at end of each block transfer if DMAX_CH21_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH21_SRC_STAT_EN 0


// Name:         DMAX_CH21_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 21 pointed to by the content of
// CHx_DSTATAR register and store it in CH21_DSTAT register if CH21_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH21_DSTAT location of linked list at end of each block transfer if DMAX_CH21_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH21_DST_STAT_EN 0


// Name:         DMAX_CH21_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH21_MULTI_BLK_TYPE == 0 || DMAX_CH21_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH21_CTL, CH21_LLP_STATUS, CH21_SSTAT and CH21_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH21_LLI_WB_EN 0


// Name:         DMAX_CH21_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH21_RD_UID_EN 0


// Name:         DMAX_CH21_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH21_WR_UID_EN 0


// Name:         DMAX_CH21_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH21_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH21_RD_UID 2


// Name:         DMAX_CH21_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH21_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH21_WR_UID 2


// Name:         DMAX_CH21_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH21_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH21_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH21_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH21_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=21) && (DMAX_CH21_RD_UID_EN==0) &&
//               (DMAX_CH21_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH21_CRC_EN 0


// Name:         DMAX_CH22_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 22 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH22_FIFO_DEPTH 8


// Name:         DMAX_CH22_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 22 (CH22_CTL.SRC_MSIZE and
// CH22_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH22_MAX_MSIZE 8


// Name:         DMAX_CH22_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH22_BLOCK_TS.BLOCK_TS), that can be programmed for channel 22. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH22_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH22_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH22_MAX_BLOCK_TS 31


// Name:         DMAX_CH22_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 22. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH22_MAX_AMBA_BURST_LENGTH <= DMAX_CH22_MAX_BLOCK_TS
//  - DMAX_CH22_MAX_AMBA_BURST_LENGTH <= DMAX_CH22_MAX_MSIZE
`define APU_DMAX_CH22_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH22_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 22. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH22_LOCK_EN 0


// Name:         DMAX_CH22_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 22. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH22_TT_FC 4'h8


// Name:         DMAX_CH22_FC
// Default:      No Hardcode (DMAX_CH22_TT_FC == 8 ? 0 : (DMAX_CH22_TT_FC <= 3 ? 1 :
//               (DMAX_CH22_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 22 Flow Controller
`define APU_DMAX_CH22_FC 0


// Name:         DMAX_CH22_TT
// Default:      No Hardcode (DMAX_CH22_TT_FC == 8 ? 0 : (DMAX_CH22_TT_FC == 0 ? 1 :
//               (DMAX_CH22_TT_FC == 1 || DMAX_CH22_TT_FC == 6 ? 3: (DMAX_CH22_TT_FC
//               == 2 || DMAX_CH22_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 22 Transfer Type
`define APU_DMAX_CH22_TT 0


// Name:         DMAX_CH22_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 22. If this is not hardcoded, software can program
// the source of channel 22 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH22_SMS 2'h0


// Name:         DMAX_CH22_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 22 destination. If this is not hardcoded, then software can
// program the destination of channel 22 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH22_DMS 2'h0


// Name:         DMAX_CH22_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 22. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH22_STW 32


// Name:         DMAX_CH22_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 22. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH22_DTW 32


// Name:         DMAX_CH22_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH22_MULTI_BLK_EN==1) && ((DMAX_CH22_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH22_MULTI_BLK_TYPE ==2) || (DMAX_CH22_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH22_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 22. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH22_SHADOW_REG_EN 0


// Name:         DMAX_CH22_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 22. If this option is set to 0, then hardware
// hardwires channel 22 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH22_MULTI_BLK_EN 0


// Name:         DMAX_CH22_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH22_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 22. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH22_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH22_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH22_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 6 || DMAX_CH22_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH22_MULTI_BLK_TYPE == 1 || DMAX_CH22_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 7 || DMAX_CH22_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH22_MULTI_BLK_TYPE == 2 || DMAX_CH22_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH22_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 10 || DMAX_CH22_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 22 Destination MultiBlock Type
`define APU_DMAX_CH22_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH22_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH22_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 2 || DMAX_CH22_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH22_MULTI_BLK_TYPE == 3 || DMAX_CH22_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 5 || DMAX_CH22_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH22_MULTI_BLK_TYPE == 6 || DMAX_CH22_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH22_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH22_MULTI_BLK_TYPE == 12 || DMAX_CH22_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 22 Source MultiBlock Type
`define APU_DMAX_CH22_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH22_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH22_MULTI_BLK_EN==1) && (DMAX_CH22_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH22_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 22. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH22_LLI_PREFETCH_EN 0


// Name:         DMAX_CH22_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH22_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH22_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 22. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 22
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH22_LMS 2'h0


// Name:         DMAX_CH22_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 22 pointed to by the content of CH22_SSTATAR
// register and store it in CH22_SSTAT register if CH22_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH22_SSTAT location of linked list at end of each block transfer if DMAX_CH22_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH22_SRC_STAT_EN 0


// Name:         DMAX_CH22_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 22 pointed to by the content of
// CHx_DSTATAR register and store it in CH22_DSTAT register if CH22_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH22_DSTAT location of linked list at end of each block transfer if DMAX_CH22_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH22_DST_STAT_EN 0


// Name:         DMAX_CH22_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH22_MULTI_BLK_TYPE == 0 || DMAX_CH22_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH22_CTL, CH22_LLP_STATUS, CH22_SSTAT and CH22_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH22_LLI_WB_EN 0


// Name:         DMAX_CH22_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH22_RD_UID_EN 0


// Name:         DMAX_CH22_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH22_WR_UID_EN 0


// Name:         DMAX_CH22_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH22_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH22_RD_UID 2


// Name:         DMAX_CH22_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH22_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH22_WR_UID 2


// Name:         DMAX_CH22_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH22_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH22_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH22_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH22_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=22) && (DMAX_CH22_RD_UID_EN==0) &&
//               (DMAX_CH22_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH22_CRC_EN 0


// Name:         DMAX_CH23_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 23 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH23_FIFO_DEPTH 8


// Name:         DMAX_CH23_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 23 (CH23_CTL.SRC_MSIZE and
// CH23_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH23_MAX_MSIZE 8


// Name:         DMAX_CH23_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH23_BLOCK_TS.BLOCK_TS), that can be programmed for channel 23. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH23_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH23_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH23_MAX_BLOCK_TS 31


// Name:         DMAX_CH23_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 23. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH23_MAX_AMBA_BURST_LENGTH <= DMAX_CH23_MAX_BLOCK_TS
//  - DMAX_CH23_MAX_AMBA_BURST_LENGTH <= DMAX_CH23_MAX_MSIZE
`define APU_DMAX_CH23_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH23_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 23. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH23_LOCK_EN 0


// Name:         DMAX_CH23_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 23. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH23_TT_FC 4'h8


// Name:         DMAX_CH23_FC
// Default:      No Hardcode (DMAX_CH23_TT_FC == 8 ? 0 : (DMAX_CH23_TT_FC <= 3 ? 1 :
//               (DMAX_CH23_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 23 Flow Controller
`define APU_DMAX_CH23_FC 0


// Name:         DMAX_CH23_TT
// Default:      No Hardcode (DMAX_CH23_TT_FC == 8 ? 0 : (DMAX_CH23_TT_FC == 0 ? 1 :
//               (DMAX_CH23_TT_FC == 1 || DMAX_CH23_TT_FC == 6 ? 3: (DMAX_CH23_TT_FC
//               == 2 || DMAX_CH23_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 23 Transfer Type
`define APU_DMAX_CH23_TT 0


// Name:         DMAX_CH23_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 23. If this is not hardcoded, software can program
// the source of channel 23 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH23_SMS 2'h0


// Name:         DMAX_CH23_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 23 destination. If this is not hardcoded, then software can
// program the destination of channel 23 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH23_DMS 2'h0


// Name:         DMAX_CH23_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 23. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH23_STW 32


// Name:         DMAX_CH23_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 23. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH23_DTW 32


// Name:         DMAX_CH23_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH23_MULTI_BLK_EN==1) && ((DMAX_CH23_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH23_MULTI_BLK_TYPE ==2) || (DMAX_CH23_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH23_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 23. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH23_SHADOW_REG_EN 0


// Name:         DMAX_CH23_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 23. If this option is set to 0, then hardware
// hardwires channel 23 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH23_MULTI_BLK_EN 0


// Name:         DMAX_CH23_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH23_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 23. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH23_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH23_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH23_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 6 || DMAX_CH23_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH23_MULTI_BLK_TYPE == 1 || DMAX_CH23_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 7 || DMAX_CH23_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH23_MULTI_BLK_TYPE == 2 || DMAX_CH23_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH23_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 10 || DMAX_CH23_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 23 Destination MultiBlock Type
`define APU_DMAX_CH23_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH23_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH23_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 2 || DMAX_CH23_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH23_MULTI_BLK_TYPE == 3 || DMAX_CH23_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 5 || DMAX_CH23_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH23_MULTI_BLK_TYPE == 6 || DMAX_CH23_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH23_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH23_MULTI_BLK_TYPE == 12 || DMAX_CH23_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 23 Source MultiBlock Type
`define APU_DMAX_CH23_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH23_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH23_MULTI_BLK_EN==1) && (DMAX_CH23_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH23_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 23. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH23_LLI_PREFETCH_EN 0


// Name:         DMAX_CH23_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH23_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH23_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 23. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 23
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH23_LMS 2'h0


// Name:         DMAX_CH23_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 23 pointed to by the content of CH23_SSTATAR
// register and store it in CH23_SSTAT register if CH23_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH23_SSTAT location of linked list at end of each block transfer if DMAX_CH23_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH23_SRC_STAT_EN 0


// Name:         DMAX_CH23_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 23 pointed to by the content of
// CHx_DSTATAR register and store it in CH23_DSTAT register if CH23_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH23_DSTAT location of linked list at end of each block transfer if DMAX_CH23_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH23_DST_STAT_EN 0


// Name:         DMAX_CH23_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH23_MULTI_BLK_TYPE == 0 || DMAX_CH23_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH23_CTL, CH23_LLP_STATUS, CH23_SSTAT and CH23_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH23_LLI_WB_EN 0


// Name:         DMAX_CH23_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH23_RD_UID_EN 0


// Name:         DMAX_CH23_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH23_WR_UID_EN 0


// Name:         DMAX_CH23_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH23_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH23_RD_UID 2


// Name:         DMAX_CH23_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH23_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH23_WR_UID 2


// Name:         DMAX_CH23_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH23_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH23_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH23_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH23_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=23) && (DMAX_CH23_RD_UID_EN==0) &&
//               (DMAX_CH23_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH23_CRC_EN 0


// Name:         DMAX_CH24_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 24 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH24_FIFO_DEPTH 8


// Name:         DMAX_CH24_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 24 (CH24_CTL.SRC_MSIZE and
// CH24_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH24_MAX_MSIZE 8


// Name:         DMAX_CH24_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH24_BLOCK_TS.BLOCK_TS), that can be programmed for channel 24. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH24_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH24_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH24_MAX_BLOCK_TS 31


// Name:         DMAX_CH24_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 24. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH24_MAX_AMBA_BURST_LENGTH <= DMAX_CH24_MAX_BLOCK_TS
//  - DMAX_CH24_MAX_AMBA_BURST_LENGTH <= DMAX_CH24_MAX_MSIZE
`define APU_DMAX_CH24_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH24_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 24. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH24_LOCK_EN 0


// Name:         DMAX_CH24_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 24. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH24_TT_FC 4'h8


// Name:         DMAX_CH24_FC
// Default:      No Hardcode (DMAX_CH24_TT_FC == 8 ? 0 : (DMAX_CH24_TT_FC <= 3 ? 1 :
//               (DMAX_CH24_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 24 Flow Controller
`define APU_DMAX_CH24_FC 0


// Name:         DMAX_CH24_TT
// Default:      No Hardcode (DMAX_CH24_TT_FC == 8 ? 0 : (DMAX_CH24_TT_FC == 0 ? 1 :
//               (DMAX_CH24_TT_FC == 1 || DMAX_CH24_TT_FC == 6 ? 3: (DMAX_CH24_TT_FC
//               == 2 || DMAX_CH24_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 24 Transfer Type
`define APU_DMAX_CH24_TT 0


// Name:         DMAX_CH24_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 24. If this is not hardcoded, software can program
// the source of channel 24 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH24_SMS 2'h0


// Name:         DMAX_CH24_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 24 destination. If this is not hardcoded, then software can
// program the destination of channel 24 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH24_DMS 2'h0


// Name:         DMAX_CH24_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 24. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH24_STW 32


// Name:         DMAX_CH24_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 24. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH24_DTW 32


// Name:         DMAX_CH24_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH24_MULTI_BLK_EN==1) && ((DMAX_CH24_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH24_MULTI_BLK_TYPE ==2) || (DMAX_CH24_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH24_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 24. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH24_SHADOW_REG_EN 0


// Name:         DMAX_CH24_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 24. If this option is set to 0, then hardware
// hardwires channel 24 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH24_MULTI_BLK_EN 0


// Name:         DMAX_CH24_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH24_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 24. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH24_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH24_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH24_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 6 || DMAX_CH24_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH24_MULTI_BLK_TYPE == 1 || DMAX_CH24_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 7 || DMAX_CH24_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH24_MULTI_BLK_TYPE == 2 || DMAX_CH24_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH24_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 10 || DMAX_CH24_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 24 Destination MultiBlock Type
`define APU_DMAX_CH24_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH24_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH24_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 2 || DMAX_CH24_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH24_MULTI_BLK_TYPE == 3 || DMAX_CH24_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 5 || DMAX_CH24_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH24_MULTI_BLK_TYPE == 6 || DMAX_CH24_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH24_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH24_MULTI_BLK_TYPE == 12 || DMAX_CH24_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 24 Source MultiBlock Type
`define APU_DMAX_CH24_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH24_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH24_MULTI_BLK_EN==1) && (DMAX_CH24_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH24_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 24. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH24_LLI_PREFETCH_EN 0


// Name:         DMAX_CH24_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH24_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH24_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 24. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 24
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH24_LMS 2'h0


// Name:         DMAX_CH24_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 24 pointed to by the content of CH24_SSTATAR
// register and store it in CH24_SSTAT register if CH24_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH24_SSTAT location of linked list at end of each block transfer if DMAX_CH24_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH24_SRC_STAT_EN 0


// Name:         DMAX_CH24_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 24 pointed to by the content of
// CHx_DSTATAR register and store it in CH24_DSTAT register if CH24_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH24_DSTAT location of linked list at end of each block transfer if DMAX_CH24_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH24_DST_STAT_EN 0


// Name:         DMAX_CH24_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH24_MULTI_BLK_TYPE == 0 || DMAX_CH24_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH24_CTL, CH24_LLP_STATUS, CH24_SSTAT and CH24_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH24_LLI_WB_EN 0


// Name:         DMAX_CH24_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH24_RD_UID_EN 0


// Name:         DMAX_CH24_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH24_WR_UID_EN 0


// Name:         DMAX_CH24_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH24_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH24_RD_UID 2


// Name:         DMAX_CH24_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH24_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH24_WR_UID 2


// Name:         DMAX_CH24_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH24_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH24_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH24_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH24_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=24) && (DMAX_CH24_RD_UID_EN==0) &&
//               (DMAX_CH24_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH24_CRC_EN 0


// Name:         DMAX_CH25_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 25 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH25_FIFO_DEPTH 8


// Name:         DMAX_CH25_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 25 (CH25_CTL.SRC_MSIZE and
// CH25_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH25_MAX_MSIZE 8


// Name:         DMAX_CH25_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH25_BLOCK_TS.BLOCK_TS), that can be programmed for channel 25. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH25_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH25_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH25_MAX_BLOCK_TS 31


// Name:         DMAX_CH25_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 25. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH25_MAX_AMBA_BURST_LENGTH <= DMAX_CH25_MAX_BLOCK_TS
//  - DMAX_CH25_MAX_AMBA_BURST_LENGTH <= DMAX_CH25_MAX_MSIZE
`define APU_DMAX_CH25_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH25_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 25. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH25_LOCK_EN 0


// Name:         DMAX_CH25_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 25. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH25_TT_FC 4'h8


// Name:         DMAX_CH25_FC
// Default:      No Hardcode (DMAX_CH25_TT_FC == 8 ? 0 : (DMAX_CH25_TT_FC <= 3 ? 1 :
//               (DMAX_CH25_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 25 Flow Controller
`define APU_DMAX_CH25_FC 0


// Name:         DMAX_CH25_TT
// Default:      No Hardcode (DMAX_CH25_TT_FC == 8 ? 0 : (DMAX_CH25_TT_FC == 0 ? 1 :
//               (DMAX_CH25_TT_FC == 1 || DMAX_CH25_TT_FC == 6 ? 3: (DMAX_CH25_TT_FC
//               == 2 || DMAX_CH25_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 25 Transfer Type
`define APU_DMAX_CH25_TT 0


// Name:         DMAX_CH25_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 25. If this is not hardcoded, software can program
// the source of channel 25 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH25_SMS 2'h0


// Name:         DMAX_CH25_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 25 destination. If this is not hardcoded, then software can
// program the destination of channel 25 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH25_DMS 2'h0


// Name:         DMAX_CH25_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 25. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH25_STW 32


// Name:         DMAX_CH25_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 25. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH25_DTW 32


// Name:         DMAX_CH25_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH25_MULTI_BLK_EN==1) && ((DMAX_CH25_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH25_MULTI_BLK_TYPE ==2) || (DMAX_CH25_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH25_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 25. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH25_SHADOW_REG_EN 0


// Name:         DMAX_CH25_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 25. If this option is set to 0, then hardware
// hardwires channel 25 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH25_MULTI_BLK_EN 0


// Name:         DMAX_CH25_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH25_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 25. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH25_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH25_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH25_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 6 || DMAX_CH25_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH25_MULTI_BLK_TYPE == 1 || DMAX_CH25_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 7 || DMAX_CH25_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH25_MULTI_BLK_TYPE == 2 || DMAX_CH25_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH25_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 10 || DMAX_CH25_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 25 Destination MultiBlock Type
`define APU_DMAX_CH25_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH25_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH25_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 2 || DMAX_CH25_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH25_MULTI_BLK_TYPE == 3 || DMAX_CH25_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 5 || DMAX_CH25_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH25_MULTI_BLK_TYPE == 6 || DMAX_CH25_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH25_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH25_MULTI_BLK_TYPE == 12 || DMAX_CH25_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 25 Source MultiBlock Type
`define APU_DMAX_CH25_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH25_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH25_MULTI_BLK_EN==1) && (DMAX_CH25_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH25_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 25. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH25_LLI_PREFETCH_EN 0


// Name:         DMAX_CH25_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH25_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH25_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 25. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 25
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH25_LMS 2'h0


// Name:         DMAX_CH25_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 25 pointed to by the content of CH25_SSTATAR
// register and store it in CH25_SSTAT register if CH25_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH25_SSTAT location of linked list at end of each block transfer if DMAX_CH25_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH25_SRC_STAT_EN 0


// Name:         DMAX_CH25_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 25 pointed to by the content of
// CHx_DSTATAR register and store it in CH25_DSTAT register if CH25_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH25_DSTAT location of linked list at end of each block transfer if DMAX_CH25_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH25_DST_STAT_EN 0


// Name:         DMAX_CH25_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH25_MULTI_BLK_TYPE == 0 || DMAX_CH25_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH25_CTL, CH25_LLP_STATUS, CH25_SSTAT and CH25_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH25_LLI_WB_EN 0


// Name:         DMAX_CH25_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH25_RD_UID_EN 0


// Name:         DMAX_CH25_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH25_WR_UID_EN 0


// Name:         DMAX_CH25_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH25_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH25_RD_UID 2


// Name:         DMAX_CH25_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH25_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH25_WR_UID 2


// Name:         DMAX_CH25_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH25_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH25_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH25_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH25_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=25) && (DMAX_CH25_RD_UID_EN==0) &&
//               (DMAX_CH25_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH25_CRC_EN 0


// Name:         DMAX_CH26_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 26 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH26_FIFO_DEPTH 8


// Name:         DMAX_CH26_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 26 (CH26_CTL.SRC_MSIZE and
// CH26_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH26_MAX_MSIZE 8


// Name:         DMAX_CH26_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH26_BLOCK_TS.BLOCK_TS), that can be programmed for channel 26. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH26_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH26_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH26_MAX_BLOCK_TS 31


// Name:         DMAX_CH26_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 26. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH26_MAX_AMBA_BURST_LENGTH <= DMAX_CH26_MAX_BLOCK_TS
//  - DMAX_CH26_MAX_AMBA_BURST_LENGTH <= DMAX_CH26_MAX_MSIZE
`define APU_DMAX_CH26_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH26_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 26. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH26_LOCK_EN 0


// Name:         DMAX_CH26_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 26. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH26_TT_FC 4'h8


// Name:         DMAX_CH26_FC
// Default:      No Hardcode (DMAX_CH26_TT_FC == 8 ? 0 : (DMAX_CH26_TT_FC <= 3 ? 1 :
//               (DMAX_CH26_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 26 Flow Controller
`define APU_DMAX_CH26_FC 0


// Name:         DMAX_CH26_TT
// Default:      No Hardcode (DMAX_CH26_TT_FC == 8 ? 0 : (DMAX_CH26_TT_FC == 0 ? 1 :
//               (DMAX_CH26_TT_FC == 1 || DMAX_CH26_TT_FC == 6 ? 3: (DMAX_CH26_TT_FC
//               == 2 || DMAX_CH26_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 26 Transfer Type
`define APU_DMAX_CH26_TT 0


// Name:         DMAX_CH26_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 26. If this is not hardcoded, software can program
// the source of channel 26 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH26_SMS 2'h0


// Name:         DMAX_CH26_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 26 destination. If this is not hardcoded, then software can
// program the destination of channel 26 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH26_DMS 2'h0


// Name:         DMAX_CH26_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 26. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH26_STW 32


// Name:         DMAX_CH26_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 26. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH26_DTW 32


// Name:         DMAX_CH26_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH26_MULTI_BLK_EN==1) && ((DMAX_CH26_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH26_MULTI_BLK_TYPE ==2) || (DMAX_CH26_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH26_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 26. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH26_SHADOW_REG_EN 0


// Name:         DMAX_CH26_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 26. If this option is set to 0, then hardware
// hardwires channel 26 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH26_MULTI_BLK_EN 0


// Name:         DMAX_CH26_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH26_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 26. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH26_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH26_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH26_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 6 || DMAX_CH26_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH26_MULTI_BLK_TYPE == 1 || DMAX_CH26_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 7 || DMAX_CH26_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH26_MULTI_BLK_TYPE == 2 || DMAX_CH26_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH26_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 10 || DMAX_CH26_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 26 Destination MultiBlock Type
`define APU_DMAX_CH26_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH26_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH26_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 2 || DMAX_CH26_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH26_MULTI_BLK_TYPE == 3 || DMAX_CH26_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 5 || DMAX_CH26_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH26_MULTI_BLK_TYPE == 6 || DMAX_CH26_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH26_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH26_MULTI_BLK_TYPE == 12 || DMAX_CH26_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 26 Source MultiBlock Type
`define APU_DMAX_CH26_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH26_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH26_MULTI_BLK_EN==1) && (DMAX_CH26_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH26_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 26. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH26_LLI_PREFETCH_EN 0


// Name:         DMAX_CH26_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH26_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH26_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 26. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 26
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH26_LMS 2'h0


// Name:         DMAX_CH26_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 26 pointed to by the content of CH26_SSTATAR
// register and store it in CH26_SSTAT register if CH26_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH26_SSTAT location of linked list at end of each block transfer if DMAX_CH26_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH26_SRC_STAT_EN 0


// Name:         DMAX_CH26_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 26 pointed to by the content of
// CHx_DSTATAR register and store it in CH26_DSTAT register if CH26_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH26_DSTAT location of linked list at end of each block transfer if DMAX_CH26_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH26_DST_STAT_EN 0


// Name:         DMAX_CH26_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH26_MULTI_BLK_TYPE == 0 || DMAX_CH26_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH26_CTL, CH26_LLP_STATUS, CH26_SSTAT and CH26_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH26_LLI_WB_EN 0


// Name:         DMAX_CH26_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH26_RD_UID_EN 0


// Name:         DMAX_CH26_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH26_WR_UID_EN 0


// Name:         DMAX_CH26_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH26_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH26_RD_UID 2


// Name:         DMAX_CH26_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH26_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH26_WR_UID 2


// Name:         DMAX_CH26_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH26_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH26_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH26_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH26_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=26) && (DMAX_CH26_RD_UID_EN==0) &&
//               (DMAX_CH26_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH26_CRC_EN 0


// Name:         DMAX_CH27_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 27 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH27_FIFO_DEPTH 8


// Name:         DMAX_CH27_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 27 (CH27_CTL.SRC_MSIZE and
// CH27_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH27_MAX_MSIZE 8


// Name:         DMAX_CH27_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH27_BLOCK_TS.BLOCK_TS), that can be programmed for channel 27. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH27_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH27_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH27_MAX_BLOCK_TS 31


// Name:         DMAX_CH27_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 27. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH27_MAX_AMBA_BURST_LENGTH <= DMAX_CH27_MAX_BLOCK_TS
//  - DMAX_CH27_MAX_AMBA_BURST_LENGTH <= DMAX_CH27_MAX_MSIZE
`define APU_DMAX_CH27_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH27_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 27. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH27_LOCK_EN 0


// Name:         DMAX_CH27_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 27. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH27_TT_FC 4'h8


// Name:         DMAX_CH27_FC
// Default:      No Hardcode (DMAX_CH27_TT_FC == 8 ? 0 : (DMAX_CH27_TT_FC <= 3 ? 1 :
//               (DMAX_CH27_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 27 Flow Controller
`define APU_DMAX_CH27_FC 0


// Name:         DMAX_CH27_TT
// Default:      No Hardcode (DMAX_CH27_TT_FC == 8 ? 0 : (DMAX_CH27_TT_FC == 0 ? 1 :
//               (DMAX_CH27_TT_FC == 1 || DMAX_CH27_TT_FC == 6 ? 3: (DMAX_CH27_TT_FC
//               == 2 || DMAX_CH27_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 27 Transfer Type
`define APU_DMAX_CH27_TT 0


// Name:         DMAX_CH27_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 27. If this is not hardcoded, software can program
// the source of channel 27 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH27_SMS 2'h0


// Name:         DMAX_CH27_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 27 destination. If this is not hardcoded, then software can
// program the destination of channel 27 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH27_DMS 2'h0


// Name:         DMAX_CH27_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 27. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH27_STW 32


// Name:         DMAX_CH27_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 27. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH27_DTW 32


// Name:         DMAX_CH27_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH27_MULTI_BLK_EN==1) && ((DMAX_CH27_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH27_MULTI_BLK_TYPE ==2) || (DMAX_CH27_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH27_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 27. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH27_SHADOW_REG_EN 0


// Name:         DMAX_CH27_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 27. If this option is set to 0, then hardware
// hardwires channel 27 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH27_MULTI_BLK_EN 0


// Name:         DMAX_CH27_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH27_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 27. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH27_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH27_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH27_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 6 || DMAX_CH27_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH27_MULTI_BLK_TYPE == 1 || DMAX_CH27_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 7 || DMAX_CH27_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH27_MULTI_BLK_TYPE == 2 || DMAX_CH27_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH27_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 10 || DMAX_CH27_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 27 Destination MultiBlock Type
`define APU_DMAX_CH27_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH27_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH27_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 2 || DMAX_CH27_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH27_MULTI_BLK_TYPE == 3 || DMAX_CH27_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 5 || DMAX_CH27_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH27_MULTI_BLK_TYPE == 6 || DMAX_CH27_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH27_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH27_MULTI_BLK_TYPE == 12 || DMAX_CH27_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 27 Source MultiBlock Type
`define APU_DMAX_CH27_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH27_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH27_MULTI_BLK_EN==1) && (DMAX_CH27_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH27_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 27. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH27_LLI_PREFETCH_EN 0


// Name:         DMAX_CH27_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH27_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH27_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 27. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 27
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH27_LMS 2'h0


// Name:         DMAX_CH27_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 27 pointed to by the content of CH27_SSTATAR
// register and store it in CH27_SSTAT register if CH27_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH27_SSTAT location of linked list at end of each block transfer if DMAX_CH27_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH27_SRC_STAT_EN 0


// Name:         DMAX_CH27_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 27 pointed to by the content of
// CHx_DSTATAR register and store it in CH27_DSTAT register if CH27_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH27_DSTAT location of linked list at end of each block transfer if DMAX_CH27_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH27_DST_STAT_EN 0


// Name:         DMAX_CH27_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH27_MULTI_BLK_TYPE == 0 || DMAX_CH27_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH27_CTL, CH27_LLP_STATUS, CH27_SSTAT and CH27_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH27_LLI_WB_EN 0


// Name:         DMAX_CH27_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH27_RD_UID_EN 0


// Name:         DMAX_CH27_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH27_WR_UID_EN 0


// Name:         DMAX_CH27_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH27_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH27_RD_UID 2


// Name:         DMAX_CH27_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH27_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH27_WR_UID 2


// Name:         DMAX_CH27_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH27_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH27_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH27_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH27_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=27) && (DMAX_CH27_RD_UID_EN==0) &&
//               (DMAX_CH27_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH27_CRC_EN 0


// Name:         DMAX_CH28_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 28 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH28_FIFO_DEPTH 8


// Name:         DMAX_CH28_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 28 (CH28_CTL.SRC_MSIZE and
// CH28_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH28_MAX_MSIZE 8


// Name:         DMAX_CH28_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH28_BLOCK_TS.BLOCK_TS), that can be programmed for channel 28. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH28_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH28_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH28_MAX_BLOCK_TS 31


// Name:         DMAX_CH28_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 28. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH28_MAX_AMBA_BURST_LENGTH <= DMAX_CH28_MAX_BLOCK_TS
//  - DMAX_CH28_MAX_AMBA_BURST_LENGTH <= DMAX_CH28_MAX_MSIZE
`define APU_DMAX_CH28_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH28_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 28. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH28_LOCK_EN 0


// Name:         DMAX_CH28_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 28. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH28_TT_FC 4'h8


// Name:         DMAX_CH28_FC
// Default:      No Hardcode (DMAX_CH28_TT_FC == 8 ? 0 : (DMAX_CH28_TT_FC <= 3 ? 1 :
//               (DMAX_CH28_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 28 Flow Controller
`define APU_DMAX_CH28_FC 0


// Name:         DMAX_CH28_TT
// Default:      No Hardcode (DMAX_CH28_TT_FC == 8 ? 0 : (DMAX_CH28_TT_FC == 0 ? 1 :
//               (DMAX_CH28_TT_FC == 1 || DMAX_CH28_TT_FC == 6 ? 3: (DMAX_CH28_TT_FC
//               == 2 || DMAX_CH28_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 28 Transfer Type
`define APU_DMAX_CH28_TT 0


// Name:         DMAX_CH28_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 28. If this is not hardcoded, software can program
// the source of channel 28 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH28_SMS 2'h0


// Name:         DMAX_CH28_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 28 destination. If this is not hardcoded, then software can
// program the destination of channel 28 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH28_DMS 2'h0


// Name:         DMAX_CH28_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 28. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH28_STW 32


// Name:         DMAX_CH28_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 28. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH28_DTW 32


// Name:         DMAX_CH28_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH28_MULTI_BLK_EN==1) && ((DMAX_CH28_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH28_MULTI_BLK_TYPE ==2) || (DMAX_CH28_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH28_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 28. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH28_SHADOW_REG_EN 0


// Name:         DMAX_CH28_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 28. If this option is set to 0, then hardware
// hardwires channel 28 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH28_MULTI_BLK_EN 0


// Name:         DMAX_CH28_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH28_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 28. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH28_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH28_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH28_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 6 || DMAX_CH28_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH28_MULTI_BLK_TYPE == 1 || DMAX_CH28_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 7 || DMAX_CH28_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH28_MULTI_BLK_TYPE == 2 || DMAX_CH28_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH28_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 10 || DMAX_CH28_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 28 Destination MultiBlock Type
`define APU_DMAX_CH28_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH28_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH28_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 2 || DMAX_CH28_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH28_MULTI_BLK_TYPE == 3 || DMAX_CH28_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 5 || DMAX_CH28_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH28_MULTI_BLK_TYPE == 6 || DMAX_CH28_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH28_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH28_MULTI_BLK_TYPE == 12 || DMAX_CH28_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 28 Source MultiBlock Type
`define APU_DMAX_CH28_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH28_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH28_MULTI_BLK_EN==1) && (DMAX_CH28_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH28_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 28. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH28_LLI_PREFETCH_EN 0


// Name:         DMAX_CH28_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH28_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH28_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 28. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 28
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH28_LMS 2'h0


// Name:         DMAX_CH28_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 28 pointed to by the content of CH28_SSTATAR
// register and store it in CH28_SSTAT register if CH28_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH28_SSTAT location of linked list at end of each block transfer if DMAX_CH28_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH28_SRC_STAT_EN 0


// Name:         DMAX_CH28_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 28 pointed to by the content of
// CHx_DSTATAR register and store it in CH28_DSTAT register if CH28_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH28_DSTAT location of linked list at end of each block transfer if DMAX_CH28_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH28_DST_STAT_EN 0


// Name:         DMAX_CH28_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH28_MULTI_BLK_TYPE == 0 || DMAX_CH28_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH28_CTL, CH28_LLP_STATUS, CH28_SSTAT and CH28_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH28_LLI_WB_EN 0


// Name:         DMAX_CH28_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH28_RD_UID_EN 0


// Name:         DMAX_CH28_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH28_WR_UID_EN 0


// Name:         DMAX_CH28_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH28_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH28_RD_UID 2


// Name:         DMAX_CH28_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH28_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH28_WR_UID 2


// Name:         DMAX_CH28_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH28_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH28_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH28_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH28_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=28) && (DMAX_CH28_RD_UID_EN==0) &&
//               (DMAX_CH28_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH28_CRC_EN 0


// Name:         DMAX_CH29_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 29 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH29_FIFO_DEPTH 8


// Name:         DMAX_CH29_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 29 (CH29_CTL.SRC_MSIZE and
// CH29_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH29_MAX_MSIZE 8


// Name:         DMAX_CH29_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH29_BLOCK_TS.BLOCK_TS), that can be programmed for channel 29. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH29_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH29_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH29_MAX_BLOCK_TS 31


// Name:         DMAX_CH29_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 29. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH29_MAX_AMBA_BURST_LENGTH <= DMAX_CH29_MAX_BLOCK_TS
//  - DMAX_CH29_MAX_AMBA_BURST_LENGTH <= DMAX_CH29_MAX_MSIZE
`define APU_DMAX_CH29_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH29_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 29. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH29_LOCK_EN 0


// Name:         DMAX_CH29_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 29. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH29_TT_FC 4'h8


// Name:         DMAX_CH29_FC
// Default:      No Hardcode (DMAX_CH29_TT_FC == 8 ? 0 : (DMAX_CH29_TT_FC <= 3 ? 1 :
//               (DMAX_CH29_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 29 Flow Controller
`define APU_DMAX_CH29_FC 0


// Name:         DMAX_CH29_TT
// Default:      No Hardcode (DMAX_CH29_TT_FC == 8 ? 0 : (DMAX_CH29_TT_FC == 0 ? 1 :
//               (DMAX_CH29_TT_FC == 1 || DMAX_CH29_TT_FC == 6 ? 3: (DMAX_CH29_TT_FC
//               == 2 || DMAX_CH29_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 29 Transfer Type
`define APU_DMAX_CH29_TT 0


// Name:         DMAX_CH29_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 29. If this is not hardcoded, software can program
// the source of channel 29 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH29_SMS 2'h0


// Name:         DMAX_CH29_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 29 destination. If this is not hardcoded, then software can
// program the destination of channel 29 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH29_DMS 2'h0


// Name:         DMAX_CH29_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 29. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH29_STW 32


// Name:         DMAX_CH29_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 29. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH29_DTW 32


// Name:         DMAX_CH29_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH29_MULTI_BLK_EN==1) && ((DMAX_CH29_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH29_MULTI_BLK_TYPE ==2) || (DMAX_CH29_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH29_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 29. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH29_SHADOW_REG_EN 0


// Name:         DMAX_CH29_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 29. If this option is set to 0, then hardware
// hardwires channel 29 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH29_MULTI_BLK_EN 0


// Name:         DMAX_CH29_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH29_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 29. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH29_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH29_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH29_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 6 || DMAX_CH29_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH29_MULTI_BLK_TYPE == 1 || DMAX_CH29_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 7 || DMAX_CH29_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH29_MULTI_BLK_TYPE == 2 || DMAX_CH29_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH29_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 10 || DMAX_CH29_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 29 Destination MultiBlock Type
`define APU_DMAX_CH29_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH29_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH29_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 2 || DMAX_CH29_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH29_MULTI_BLK_TYPE == 3 || DMAX_CH29_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 5 || DMAX_CH29_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH29_MULTI_BLK_TYPE == 6 || DMAX_CH29_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH29_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH29_MULTI_BLK_TYPE == 12 || DMAX_CH29_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 29 Source MultiBlock Type
`define APU_DMAX_CH29_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH29_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH29_MULTI_BLK_EN==1) && (DMAX_CH29_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH29_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 29. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH29_LLI_PREFETCH_EN 0


// Name:         DMAX_CH29_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH29_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH29_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 29. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 29
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH29_LMS 2'h0


// Name:         DMAX_CH29_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 29 pointed to by the content of CH29_SSTATAR
// register and store it in CH29_SSTAT register if CH29_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH29_SSTAT location of linked list at end of each block transfer if DMAX_CH29_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH29_SRC_STAT_EN 0


// Name:         DMAX_CH29_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 29 pointed to by the content of
// CHx_DSTATAR register and store it in CH29_DSTAT register if CH29_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH29_DSTAT location of linked list at end of each block transfer if DMAX_CH29_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH29_DST_STAT_EN 0


// Name:         DMAX_CH29_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH29_MULTI_BLK_TYPE == 0 || DMAX_CH29_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH29_CTL, CH29_LLP_STATUS, CH29_SSTAT and CH29_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH29_LLI_WB_EN 0


// Name:         DMAX_CH29_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH29_RD_UID_EN 0


// Name:         DMAX_CH29_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH29_WR_UID_EN 0


// Name:         DMAX_CH29_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH29_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH29_RD_UID 2


// Name:         DMAX_CH29_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH29_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH29_WR_UID 2


// Name:         DMAX_CH29_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH29_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH29_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH29_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH29_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=29) && (DMAX_CH29_RD_UID_EN==0) &&
//               (DMAX_CH29_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH29_CRC_EN 0


// Name:         DMAX_CH30_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 30 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH30_FIFO_DEPTH 8


// Name:         DMAX_CH30_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 30 (CH30_CTL.SRC_MSIZE and
// CH30_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH30_MAX_MSIZE 8


// Name:         DMAX_CH30_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH30_BLOCK_TS.BLOCK_TS), that can be programmed for channel 30. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH30_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH30_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH30_MAX_BLOCK_TS 31


// Name:         DMAX_CH30_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 30. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH30_MAX_AMBA_BURST_LENGTH <= DMAX_CH30_MAX_BLOCK_TS
//  - DMAX_CH30_MAX_AMBA_BURST_LENGTH <= DMAX_CH30_MAX_MSIZE
`define APU_DMAX_CH30_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH30_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 30. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH30_LOCK_EN 0


// Name:         DMAX_CH30_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 30. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH30_TT_FC 4'h8


// Name:         DMAX_CH30_FC
// Default:      No Hardcode (DMAX_CH30_TT_FC == 8 ? 0 : (DMAX_CH30_TT_FC <= 3 ? 1 :
//               (DMAX_CH30_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 30 Flow Controller
`define APU_DMAX_CH30_FC 0


// Name:         DMAX_CH30_TT
// Default:      No Hardcode (DMAX_CH30_TT_FC == 8 ? 0 : (DMAX_CH30_TT_FC == 0 ? 1 :
//               (DMAX_CH30_TT_FC == 1 || DMAX_CH30_TT_FC == 6 ? 3: (DMAX_CH30_TT_FC
//               == 2 || DMAX_CH30_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 30 Transfer Type
`define APU_DMAX_CH30_TT 0


// Name:         DMAX_CH30_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 30. If this is not hardcoded, software can program
// the source of channel 30 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH30_SMS 2'h0


// Name:         DMAX_CH30_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 30 destination. If this is not hardcoded, then software can
// program the destination of channel 30 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH30_DMS 2'h0


// Name:         DMAX_CH30_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 30. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH30_STW 32


// Name:         DMAX_CH30_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 30. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH30_DTW 32


// Name:         DMAX_CH30_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH30_MULTI_BLK_EN==1) && ((DMAX_CH30_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH30_MULTI_BLK_TYPE ==2) || (DMAX_CH30_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH30_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 30. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH30_SHADOW_REG_EN 0


// Name:         DMAX_CH30_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 30. If this option is set to 0, then hardware
// hardwires channel 30 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH30_MULTI_BLK_EN 0


// Name:         DMAX_CH30_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH30_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 30. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH30_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH30_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH30_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 6 || DMAX_CH30_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH30_MULTI_BLK_TYPE == 1 || DMAX_CH30_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 7 || DMAX_CH30_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH30_MULTI_BLK_TYPE == 2 || DMAX_CH30_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH30_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 10 || DMAX_CH30_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 30 Destination MultiBlock Type
`define APU_DMAX_CH30_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH30_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH30_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 2 || DMAX_CH30_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH30_MULTI_BLK_TYPE == 3 || DMAX_CH30_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 5 || DMAX_CH30_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH30_MULTI_BLK_TYPE == 6 || DMAX_CH30_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH30_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH30_MULTI_BLK_TYPE == 12 || DMAX_CH30_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 30 Source MultiBlock Type
`define APU_DMAX_CH30_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH30_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH30_MULTI_BLK_EN==1) && (DMAX_CH30_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH30_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 30. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH30_LLI_PREFETCH_EN 0


// Name:         DMAX_CH30_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH30_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH30_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 30. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 30
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH30_LMS 2'h0


// Name:         DMAX_CH30_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 30 pointed to by the content of CH30_SSTATAR
// register and store it in CH30_SSTAT register if CH30_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH30_SSTAT location of linked list at end of each block transfer if DMAX_CH30_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH30_SRC_STAT_EN 0


// Name:         DMAX_CH30_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 30 pointed to by the content of
// CHx_DSTATAR register and store it in CH30_DSTAT register if CH30_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH30_DSTAT location of linked list at end of each block transfer if DMAX_CH30_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH30_DST_STAT_EN 0


// Name:         DMAX_CH30_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH30_MULTI_BLK_TYPE == 0 || DMAX_CH30_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH30_CTL, CH30_LLP_STATUS, CH30_SSTAT and CH30_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH30_LLI_WB_EN 0


// Name:         DMAX_CH30_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH30_RD_UID_EN 0


// Name:         DMAX_CH30_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH30_WR_UID_EN 0


// Name:         DMAX_CH30_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH30_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH30_RD_UID 2


// Name:         DMAX_CH30_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH30_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH30_WR_UID 2


// Name:         DMAX_CH30_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH30_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH30_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH30_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH30_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=30) && (DMAX_CH30_RD_UID_EN==0) &&
//               (DMAX_CH30_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH30_CRC_EN 0


// Name:         DMAX_CH31_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 31 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH31_FIFO_DEPTH 8


// Name:         DMAX_CH31_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 31 (CH31_CTL.SRC_MSIZE and
// CH31_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH31_MAX_MSIZE 8


// Name:         DMAX_CH31_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH31_BLOCK_TS.BLOCK_TS), that can be programmed for channel 31. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH31_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH31_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH31_MAX_BLOCK_TS 31


// Name:         DMAX_CH31_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 31. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH31_MAX_AMBA_BURST_LENGTH <= DMAX_CH31_MAX_BLOCK_TS
//  - DMAX_CH31_MAX_AMBA_BURST_LENGTH <= DMAX_CH31_MAX_MSIZE
`define APU_DMAX_CH31_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH31_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 31. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH31_LOCK_EN 0


// Name:         DMAX_CH31_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 31. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH31_TT_FC 4'h8


// Name:         DMAX_CH31_FC
// Default:      No Hardcode (DMAX_CH31_TT_FC == 8 ? 0 : (DMAX_CH31_TT_FC <= 3 ? 1 :
//               (DMAX_CH31_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 31 Flow Controller
`define APU_DMAX_CH31_FC 0


// Name:         DMAX_CH31_TT
// Default:      No Hardcode (DMAX_CH31_TT_FC == 8 ? 0 : (DMAX_CH31_TT_FC == 0 ? 1 :
//               (DMAX_CH31_TT_FC == 1 || DMAX_CH31_TT_FC == 6 ? 3: (DMAX_CH31_TT_FC
//               == 2 || DMAX_CH31_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 31 Transfer Type
`define APU_DMAX_CH31_TT 0


// Name:         DMAX_CH31_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 31. If this is not hardcoded, software can program
// the source of channel 31 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH31_SMS 2'h0


// Name:         DMAX_CH31_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 31 destination. If this is not hardcoded, then software can
// program the destination of channel 31 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH31_DMS 2'h0


// Name:         DMAX_CH31_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 31. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH31_STW 32


// Name:         DMAX_CH31_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 31. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH31_DTW 32


// Name:         DMAX_CH31_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH31_MULTI_BLK_EN==1) && ((DMAX_CH31_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH31_MULTI_BLK_TYPE ==2) || (DMAX_CH31_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH31_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 31. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH31_SHADOW_REG_EN 0


// Name:         DMAX_CH31_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 31. If this option is set to 0, then hardware
// hardwires channel 31 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH31_MULTI_BLK_EN 0


// Name:         DMAX_CH31_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH31_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 31. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH31_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH31_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH31_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 6 || DMAX_CH31_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH31_MULTI_BLK_TYPE == 1 || DMAX_CH31_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 7 || DMAX_CH31_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH31_MULTI_BLK_TYPE == 2 || DMAX_CH31_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH31_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 10 || DMAX_CH31_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 31 Destination MultiBlock Type
`define APU_DMAX_CH31_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH31_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH31_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 2 || DMAX_CH31_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH31_MULTI_BLK_TYPE == 3 || DMAX_CH31_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 5 || DMAX_CH31_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH31_MULTI_BLK_TYPE == 6 || DMAX_CH31_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH31_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH31_MULTI_BLK_TYPE == 12 || DMAX_CH31_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 31 Source MultiBlock Type
`define APU_DMAX_CH31_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH31_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH31_MULTI_BLK_EN==1) && (DMAX_CH31_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH31_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 31. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH31_LLI_PREFETCH_EN 0


// Name:         DMAX_CH31_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH31_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH31_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 31. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 31
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH31_LMS 2'h0


// Name:         DMAX_CH31_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 31 pointed to by the content of CH31_SSTATAR
// register and store it in CH31_SSTAT register if CH31_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH31_SSTAT location of linked list at end of each block transfer if DMAX_CH31_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH31_SRC_STAT_EN 0


// Name:         DMAX_CH31_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 31 pointed to by the content of
// CHx_DSTATAR register and store it in CH31_DSTAT register if CH31_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH31_DSTAT location of linked list at end of each block transfer if DMAX_CH31_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH31_DST_STAT_EN 0


// Name:         DMAX_CH31_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH31_MULTI_BLK_TYPE == 0 || DMAX_CH31_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH31_CTL, CH31_LLP_STATUS, CH31_SSTAT and CH31_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH31_LLI_WB_EN 0


// Name:         DMAX_CH31_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH31_RD_UID_EN 0


// Name:         DMAX_CH31_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH31_WR_UID_EN 0


// Name:         DMAX_CH31_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH31_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH31_RD_UID 2


// Name:         DMAX_CH31_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH31_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH31_WR_UID 2


// Name:         DMAX_CH31_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH31_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH31_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH31_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH31_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=31) && (DMAX_CH31_RD_UID_EN==0) &&
//               (DMAX_CH31_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH31_CRC_EN 0


// Name:         DMAX_CH32_FIFO_DEPTH
// Default:      8
// Values:       4 8 16 32 64 128 256
//
// Channel 32 FIFO depth. Setting appropriate value based on the system requirement allows some logic optimization of the
// implementation.
`define APU_DMAX_CH32_FIFO_DEPTH 8


// Name:         DMAX_CH32_MAX_MSIZE
// Default:      8
// Values:       1 4 8 16 32 64 128 256 512 1024
//
// Maximum value of burst transaction size that can be programmed for channel 32 (CH32_CTL.SRC_MSIZE and
// CH32_CTL.DST_MSIZE).
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH32_MAX_MSIZE 8


// Name:         DMAX_CH32_MAX_BLOCK_TS
// Default:      31
// Values:       3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
//               32767, 65535, 131071, 262143, 524287, 1048575, 2097151, 4194303
//
// The description of this parameter is dependent on what is assigned as the flow controller.
//  - If DW_axi_dmac is the flow controller: Maximum block size, in multiples of source transfer width
//  (CH32_BLOCK_TS.BLOCK_TS), that can be programmed for channel 32. A programmed value greater than this results in inconsistent behavior.
//  - If source/destination peripheral assigned as flow controller: In this case, the blocks can be greater than
//  DMAX_CH32_MAX_BLOCK_TS in size, but the logic that keeps track of the size of a block saturates at DMAX_CH32_MAX_BLOCK_TS. This
//  does not result in erroneous behavior, but a read back by software of the block size is incorrect when the block size exceeds
//  the saturated value.
// Setting appropriate value based on the system requirement allows some logic optimization of the implementation.
`define APU_DMAX_CH32_MAX_BLOCK_TS 31


// Name:         DMAX_CH32_MAX_AMBA_BURST_LENGTH
// Default:      8
// Values:       1 4 8 16 32 64 128 256
//
// Maximum AMBA Burst Length for Channel 32. Setting appropriate value based on the system requirement allows some logic
// optimization of the implementation by reducing the internal FIFO depth requirement.
//
// Dependencies:
//  - DMAX_CH32_MAX_AMBA_BURST_LENGTH <= DMAX_CH32_MAX_BLOCK_TS
//  - DMAX_CH32_MAX_AMBA_BURST_LENGTH <= DMAX_CH32_MAX_MSIZE
`define APU_DMAX_CH32_MAX_AMBA_BURST_LENGTH 8


// Name:         DMAX_CH32_LOCK_EN
// Default:      No
// Values:       No (0), Yes (1)
//
// When set to Yes (1), includes logic to enable channel locking on channel 32. When set to 1, the software can program the
// DW_axi_dmac to lock the arbitration for the manager bus interface over the DMA transfer, block transfer, or transaction.
// When set to No (0), this option allows some logic optimization of the implementation.
`define APU_DMAX_CH32_LOCK_EN 0


// Name:         DMAX_CH32_TT_FC
// Default:      0x8
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
//
// Hardcodes the transfer type and flow control peripheral for the channel 32. If NO_HARDCODE is selected, then the
// transfer type and flow control device is not hardcoded, and software selects the transfer type and flow control device for a DMA
// transfer.
// Hardcoding the transfer type and flow control device allows some logic optimization of the implementation.
//
// TT_FC Flow Controller Transfer Type
//
// 0x0      DMAC              Memory to Memory
//
// 0x1      DMAC              Memory to Peripheral
//
// 0x2      DMAC              Peripheral to Memory
//
// 0x3      DMAC              Peripheral to Peripheral
//
// 0x4      Source            Peripheral to Memory
//
// 0x5      Source            Peripheral to Peripheral
//
// 0x6      Destination       Memory to Peripheral
//
// 0x7      Destination       Peripheral to Peripheral
//
// 0x8      No Hardcode       No Hardcode
//
`define APU_DMAX_CH32_TT_FC 4'h8


// Name:         DMAX_CH32_FC
// Default:      No Hardcode (DMAX_CH32_TT_FC == 8 ? 0 : (DMAX_CH32_TT_FC <= 3 ? 1 :
//               (DMAX_CH32_TT_FC <= 5 ? 2: 3)))
// Values:       No Hardcode (0), DMAC (1), Source (2), Destination (3)
// Enabled:      0
//
// Hardcoded Value of Channel 32 Flow Controller
`define APU_DMAX_CH32_FC 0


// Name:         DMAX_CH32_TT
// Default:      No Hardcode (DMAX_CH32_TT_FC == 8 ? 0 : (DMAX_CH32_TT_FC == 0 ? 1 :
//               (DMAX_CH32_TT_FC == 1 || DMAX_CH32_TT_FC == 6 ? 3: (DMAX_CH32_TT_FC
//               == 2 || DMAX_CH32_TT_FC == 4 ? 2 : 4))))
// Values:       No Hardcode (0), Memory to Memory (1), Peripheral to Memory (2),
//               Memory to Peripheral (3), Peripheral to Peripheral (4)
// Enabled:      0
//
// Hardcoded Value of Channel 32 Transfer Type
`define APU_DMAX_CH32_TT 0


// Name:         DMAX_CH32_SMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the source of channel 32. If this is not hardcoded, software can program
// the source of channel 32 to be attached to any of the configured layers. Hardcoding this value allows some logic
// optimization of the implementation
`define APU_DMAX_CH32_SMS 2'h0


// Name:         DMAX_CH32_DMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1
//
// Hardcode the AXI manager interface attached to the channel 32 destination. If this is not hardcoded, then software can
// program the destination of channel 32 to be attached to any of the configured layers. Hardcoding this value allows some
// logic optimization of the implementation.
`define APU_DMAX_CH32_DMS 2'h0


// Name:         DMAX_CH32_STW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the source transfer width for transfers from the source of channel 32. If this is not hardcoded, then software
// can program the source transfer width. Hardcoding the source transfer width allows some logic optimization of the
// implementation.
`define APU_DMAX_CH32_STW 32


// Name:         DMAX_CH32_DTW
// Default:      Word
// Values:       No Hardcode (0), Byte (8), Half Word (16), Word (32), Two Word
//               (64), Four Word (128), Eight Word (256), Sixteen Word (512), Thirty-two
//               Word (1024)
//
// Hardcode the destination transfer width for transfers to the destination of channel 32. If this is not hardcoded, then
// software can program the destination transfer width. Hardcoding the destination transfer width allows some logic
// optimization of the implementation.
`define APU_DMAX_CH32_DTW 32


// Name:         DMAX_CH32_SHADOW_REG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH32_MULTI_BLK_EN==1) && ((DMAX_CH32_MULTI_BLK_TYPE == 0) ||
//               (DMAX_CH32_MULTI_BLK_TYPE ==2) || (DMAX_CH32_MULTI_BLK_TYPE >=5 &&
//               DMAX_CH32_MULTI_BLK_TYPE <=8))
//
// Set this parameter to 1 to include shadow registers on channel 32. This parameter needs to be enabled only if shadow
// register based multi-block transfer is used. Setting this parameter to 0 allows some logic optimization of the
// implementation.
`define APU_DMAX_CH32_SHADOW_REG_EN 0


// Name:         DMAX_CH32_MULTI_BLK_EN
// Default:      false
// Values:       false (0), true (1)
//
// Includes or excludes logic to enable multi-block DMA transfers on channel 32. If this option is set to 0, then hardware
// hardwires channel 32 to perform only single block transfers. Setting this parameter to 0 allows some logic optimization of
// the implementation.
`define APU_DMAX_CH32_MULTI_BLK_EN 0


// Name:         DMAX_CH32_MULTI_BLK_TYPE
// Default:      0x0
// Values:       0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xa, 0xb, 0xc,
//               0xd
// Enabled:      DMAX_CH32_MULTI_BLK_EN==1
//
// This parameter allows to hardcode the type of multi-block transfers DW_axi_dmac can perform on channel 32. This results
// in some logic optimization of the implementation.
//
// MULTI_BLK_TYPE   Source Multi Block Type    Destination Multi Block Type
//
// 0x0                  No Hardcode                 No Hardcode
//
// 0x1                  Contiguous                  Auto Reloading
//
// 0x2                  Contiguous                  Shadow Register
//
// 0x3                  Auto Reloading              Contiguous
//
// 0x4                  Auto Reloading              Auto Reloading
//
// 0x5                  Auto Reloading              Shadow Register
//
// 0x6                  Shadow Register             Contiguous
//
// 0x7                  Shadow Register             Auto Reloading
//
// 0x8                  Shadow Register             Shadow Register
//
// 0x9                  Contiguous                  Linked List
//
// 0xa                  Auto Reloading              Linked List
//
// 0xb                  Linked List                 Contiguous
//
// 0xc                  Linked List                 Auto Reloading
//
// 0xd                  Linked List                 Linked List
//
`define APU_DMAX_CH32_MULTI_BLK_TYPE 4'h0


// Name:         DMAX_CH32_DST_MULTI_BLK_TYPE
// Default:      No Hardcode ( (DMAX_CH32_MULTI_BLK_TYPE == 3 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 6 || DMAX_CH32_MULTI_BLK_TYPE == 11) ? 0 : (
//               (DMAX_CH32_MULTI_BLK_TYPE == 1 || DMAX_CH32_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 7 || DMAX_CH32_MULTI_BLK_TYPE == 12) ? 1 : (
//               (DMAX_CH32_MULTI_BLK_TYPE == 2 || DMAX_CH32_MULTI_BLK_TYPE == 5 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH32_MULTI_BLK_TYPE == 9 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 10 || DMAX_CH32_MULTI_BLK_TYPE == 13) ? 3: 4 ))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 32 Destination MultiBlock Type
`define APU_DMAX_CH32_DST_MULTI_BLK_TYPE 4


// Name:         DMAX_CH32_SRC_MULTI_BLK_TYPE
// Default:      No Hardcode ( ( (DMAX_CH32_MULTI_BLK_TYPE == 1 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 2 || DMAX_CH32_MULTI_BLK_TYPE == 9) ? 0 : (
//               (DMAX_CH32_MULTI_BLK_TYPE == 3 || DMAX_CH32_MULTI_BLK_TYPE == 4 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 5 || DMAX_CH32_MULTI_BLK_TYPE == 10) ? 1 : (
//               (DMAX_CH32_MULTI_BLK_TYPE == 6 || DMAX_CH32_MULTI_BLK_TYPE == 7 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 8) ? 2 : ( (DMAX_CH32_MULTI_BLK_TYPE == 11 ||
//               DMAX_CH32_MULTI_BLK_TYPE == 12 || DMAX_CH32_MULTI_BLK_TYPE == 13) ? 3: 4 )))))
// Values:       Contiguous (0), Auto Reloading (1), Shadow Register (2), Linked
//               List (3), No Hardcode (4)
// Enabled:      0
//
// Hardcoded Value of Channel 32 Source MultiBlock Type
`define APU_DMAX_CH32_SRC_MULTI_BLK_TYPE 4


// Name:         DMAX_CH32_LLI_PREFETCH_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_CH32_MULTI_BLK_EN==1) && (DMAX_CH32_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH32_MULTI_BLK_TYPE >=9)
//
// Set this parameter to 1 to enable the LLI prefetching logic on channel 32. If this parameter is enabled, DW_axi_dmac
// tries to fetch one LLI in advance (while the data transfer corresponding to the previous LLI is in progress) and store
// internally and thus increases bus utilization. Enabling this parameter does not guarantee that LLI will be always pre-fetched.
// This parameter needs to be enabled only if linked-list-based multi-block transfer is used. Setting this parameter to 0
// allows some logic optimization of the implementation.
`define APU_DMAX_CH32_LLI_PREFETCH_EN 0


// Name:         DMAX_CH32_LMS
// Default:      Manager 1 (DMAX_NUM_MASTER_IF == 1 ? 0 : 2)
// Values:       Manager 1 (0x0), Manager 2 (0x1), No Hardcode (0x2)
// Enabled:      DMAX_NUM_MASTER_IF > 1 && (DMAX_CH32_MULTI_BLK_TYPE == 0 ||
//               DMAX_CH32_MULTI_BLK_TYPE >=9)
//
// Hardcode the AXI manager interface attached to the peripheral that stores the LLI information (Linked List Item) for
// channel 32. If this is not hardcoded, then software can program the peripheral that stores the LLI information of channel 32
// to be attached to any of the configured layers. Hardcoding this value allows some logic optimization of the
// implementation.
//  LLI access always uses the burst size (arsize/awsize) that is same as the data bus width. LLI access cannot be changed
//  or programmed to anything other than this value. Burst length (awlen/arlen) is chosen based on the data bus width so that
//  the access does not cross one complete LLI structure of 64 bytes. DW_axi_dmac fetches the entire LLI (40 bytes) in one
//  AXI burst if the burst length is not limited by other settings.
`define APU_DMAX_CH32_LMS 2'h0


// Name:         DMAX_CH32_SRC_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from source peripheral of channel 32 pointed to by the content of CH32_SSTATAR
// register and store it in CH32_SSTAT register if CH32_CTL.SRC_STAT_EN bit is set to 1. This value is written back to the
// CH32_SSTAT location of linked list at end of each block transfer if DMAX_CH32_LLI_WB_EN is set to 1 and if linked-list-based
// multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the
// implementation.
`define APU_DMAX_CH32_SRC_STAT_EN 0


// Name:         DMAX_CH32_DST_STAT_EN
// Default:      false
// Values:       false (0), true (1)
//
// Include or exclude logic to fetch status from destination peripheral of channel 32 pointed to by the content of
// CHx_DSTATAR register and store it in CH32_DSTAT register if CH32_CTL.DST_STAT_EN bit is set to 1. This value is written back to
// the CH32_DSTAT location of linked list at end of each block transfer if DMAX_CH32_LLI_WB_EN is set to 1 and if
// linked-list-based multiblock transfer is used by either source or destination peripheral. Setting this parameter to 0 allows some logic
// optimization of the implementation.
`define APU_DMAX_CH32_DST_STAT_EN 0


// Name:         DMAX_CH32_LLI_WB_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      DMAX_CH32_MULTI_BLK_TYPE == 0 || DMAX_CH32_MULTI_BLK_TYPE >=9
//
// Includes or excludes logic to enable write-back of the CH32_CTL, CH32_LLP_STATUS, CH32_SSTAT and CH32_DSTAT registers at
// the end of every block transfer. Write back happens only if linked-list-based multi-block transfer is used by either
// source or destination peripheral. Setting this parameter to 0 allows some logic optimization of the implementation.
`define APU_DMAX_CH32_LLI_WB_EN 0


// Name:         DMAX_CH32_RD_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Read Channel. If enabled, then AXI Read Address
// Channel will generate the AXI transfers with the unique AXI ID. This will allow Source memory to provide read data out of
// order.
`define APU_DMAX_CH32_RD_UID_EN 0


// Name:         DMAX_CH32_WR_UID_EN
// Default:      false
// Values:       false (0), true (1)
//
// This parameter allows user to include AXI Unique ID feature in the AXI Write Channel. If enabled, then AXI Write Address
// and Data Channel will generate the AXI transfers with the unique AXI ID. This will allow Destination memory to provide
// write response out of order.
`define APU_DMAX_CH32_WR_UID_EN 0


// Name:         DMAX_CH32_RD_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH32_RD_UID_EN==1
//
// This parameter allows user to select the number of AXI Read Channel Unique ID's supported. This parameter significantly
// affects the depth of the re-ordering buffer - hence area, so this feature and depth of the unique ID must be chosen
// carefully based on the requirement only for the required channel.
`define APU_DMAX_CH32_RD_UID 2


// Name:         DMAX_CH32_WR_UID
// Default:      2
// Values:       2 4 8
// Enabled:      DMAX_CH32_WR_UID_EN==1
//
// This parameter allows user to select the number of AXI Write Channel Unique ID's supported.
`define APU_DMAX_CH32_WR_UID 2


// Name:         DMAX_CH32_REORDER_BUFF_DEPTH
// Default:      8 (DMAX_CH32_FIFO_DEPTH)
// Values:       4 8 16 32 64 128 256
// Enabled:      DMAX_CH32_RD_UID_EN==1
//
// This parameter allows user to configure the re-ordering buffer depth. Setting appropriate value based on the system
// requirement allows some logic optimization of the implementation. The number of AXI Read unique ID's generated are limited by
// the Source Transfer Width, read burst length programmed, depth of the re-ordering buffer, and DMAX_CH(x)_RD_UID.
`define APU_DMAX_CH32_REORDER_BUFF_DEPTH 8


// Name:         DMAX_CH32_CRC_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      (DMAX_NUM_CHANNELS>=32) && (DMAX_CH32_RD_UID_EN==0) &&
//               (DMAX_CH32_WR_UID_EN==0) && ((<DWC-AXI-DMAC-CRC feature authorize>==1) &&
//               (<DWC-AXI-DMAC-GEN2 feature authorize> == 1)) && (DMAX_SAFETY_FEATURE_EN==0)
//
// This parameter is used to enable CRC feature for Channel x. When set to 1, CRC logic is included for Channel x.
`define APU_DMAX_CH32_CRC_EN 0


// Name:         DMAX_CRC_POLYNOMIAL
// Default:      0x1
// Values:       0x1, ..., 0x7f
// Enabled:      [<functionof>]==1
//
// This parameter is used to select the CRC polynomials that must be supported by the DW_axi_dmac. Each bit of this
// parameter is mapped to a CRC polynomial as below.
//  - DMAX_CRC_POLYNOMIAL[0] - 8-bit 0x1D Polynomial
//  - DMAX_CRC_POLYNOMIAL[1] - 8-bit 0x2F Polynomial
//  - DMAX_CRC_POLYNOMIAL[2] - 16-bit 0x1021 Polynomial
//  - DMAX_CRC_POLYNOMIAL[3] - 16-bit 0x8005 Polynomial
//  - DMAX_CRC_POLYNOMIAL[4] - 32-bit 0x04C1_1DB7 Polynomial
//  - DMAX_CRC_POLYNOMIAL[5] - 32-bit 0xF4AC_FB13 Polynomial
//  - DMAX_CRC_POLYNOMIAL[6] - 64-bit 0x42F0_E1EB_A9EA_3693 Polynomial
// To include the logic to support each polynomial, the corresponding bit must be set to 1.
// For example, if DMAX_CRC_POLYNOMIAL is set to 7'h25 (7'b010_0101), polynomials supported are 32-bit 0xF4AC_FB13, 16-bit
// 0x1021 and 8-bit 0x1D.
`define APU_DMAX_CRC_POLYNOMIAL 7'h1


// Name:         USE_FOUNDATION
// Default:      false
// Values:       false (0), true (1)
// Enabled:      [<functionof> %item]
//
// Use DesignWare Foundation parts by default for optimal Synthesis QoR. May be set to false (0) if you have an RTL source
// license in which case you may use source code for DesignWare Foundation Parts without the need for a DesignWare Foundation
// license. RTL source users, who also have a DesignWare Foundation key, may choose to retain the Foundation parts.
`define APU_USE_FOUNDATION 0

//Used to insert internal tests

//Used to insert internal tests

//Used to Enable updated - Completed Block Transfer Size and Data Left in FIFO


`define APU_SIM_RAND_SEED 1

//AXI DMAC has LLI Parameter
//DMAC will have LLI if at least one of the enabled channels has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_HAS_LLI_PARAM 1


//Log2(DMAX_NUM_CHANNELS)

`define APU_LOG2_DMAX_NUM_CHANNELS 1

//AXI DMAC CHANNEL-1 has LLI Parameter
//DMAC Channel-1 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH1_HAS_LLI 1

//AXI DMAC CHANNEL-2 has LLI Parameter
//DMAC Channel-2 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH2_HAS_LLI 1

//AXI DMAC CHANNEL-3 has LLI Parameter
//DMAC Channel-3 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH3_HAS_LLI 0

//AXI DMAC CHANNEL-4 has LLI Parameter
//DMAC Channel-4 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH4_HAS_LLI 0

//AXI DMAC CHANNEL-5 has LLI Parameter
//DMAC Channel-5 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH5_HAS_LLI 0

//AXI DMAC CHANNEL-6 has LLI Parameter
//DMAC Channel-6 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH6_HAS_LLI 0

//AXI DMAC CHANNEL-7 has LLI Parameter
//DMAC Channel-7 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH7_HAS_LLI 0

//AXI DMAC CHANNEL-8 has LLI Parameter
//DMAC Channel-8 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH8_HAS_LLI 0

//AXI DMAC CHANNEL-9 has LLI Parameter
//DMAC Channel-9 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH9_HAS_LLI 0

//AXI DMAC CHANNEL-10 has LLI Parameter
//DMAC Channel-10 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH10_HAS_LLI 0

//AXI DMAC CHANNEL-11 has LLI Parameter
//DMAC Channel-11 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH11_HAS_LLI 0

//AXI DMAC CHANNEL-12 has LLI Parameter
//DMAC Channel-12 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH12_HAS_LLI 0

//AXI DMAC CHANNEL-13 has LLI Parameter
//DMAC Channel-13 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH13_HAS_LLI 0

//AXI DMAC CHANNEL-14 has LLI Parameter
//DMAC Channel-14 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH14_HAS_LLI 0

//AXI DMAC CHANNEL-15 has LLI Parameter
//DMAC Channel-15 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH15_HAS_LLI 0

//AXI DMAC CHANNEL-16 has LLI Parameter
//DMAC Channel-16 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH16_HAS_LLI 0

//AXI DMAC CHANNEL-17 has LLI Parameter
//DMAC Channel-17 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH17_HAS_LLI 0

//AXI DMAC CHANNEL-18 has LLI Parameter
//DMAC Channel-18 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH18_HAS_LLI 0

//AXI DMAC CHANNEL-19 has LLI Parameter
//DMAC Channel-19 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH19_HAS_LLI 0

//AXI DMAC CHANNEL-20 has LLI Parameter
//DMAC Channel-20 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH20_HAS_LLI 0

//AXI DMAC CHANNEL-21 has LLI Parameter
//DMAC Channel-21 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH21_HAS_LLI 0

//AXI DMAC CHANNEL-22 has LLI Parameter
//DMAC Channel-22 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH22_HAS_LLI 0

//AXI DMAC CHANNEL-23 has LLI Parameter
//DMAC Channel-23 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH23_HAS_LLI 0

//AXI DMAC CHANNEL-24 has LLI Parameter
//DMAC Channel-24 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH24_HAS_LLI 0

//AXI DMAC CHANNEL-25 has LLI Parameter
//DMAC Channel-25 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH25_HAS_LLI 0

//AXI DMAC CHANNEL-26 has LLI Parameter
//DMAC Channel-26 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH26_HAS_LLI 0

//AXI DMAC CHANNEL-27 has LLI Parameter
//DMAC Channel-27 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH27_HAS_LLI 0

//AXI DMAC CHANNEL-28 has LLI Parameter
//DMAC Channel-28 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH28_HAS_LLI 0

//AXI DMAC CHANNEL-29 has LLI Parameter
//DMAC Channel-29 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH29_HAS_LLI 0

//AXI DMAC CHANNEL-30 has LLI Parameter
//DMAC Channel-30 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH30_HAS_LLI 0

//AXI DMAC CHANNEL-31 has LLI Parameter
//DMAC Channel-31 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH31_HAS_LLI 0

//AXI DMAC CHANNEL-32 has LLI Parameter
//DMAC Channel-32 will have LLI if the channel has DMAX_CHx_MULTI_BLK_TYPE >= 9 or DMAX_CHx_MULTI_BLK_TYPE == 0

`define APU_DMAX_CH32_HAS_LLI 0

//AXI DMAC has Read UID Parameter
//DMAC will have Read UID if at least one of the enabled channels has DMAX_CHx_RD_UID_EN == 1

`define APU_DMAX_HAS_RUID_PARAM 0

//AXI DMAC has Read UID Support


//Max. Read UID Parameter supported in DW_axi_dmac

`define APU_LOG2_DMAX_MAX_RUID 0

//Max. Read UID Parameter supported in DW_axi_dmac

`define APU_RD_UID_TBL_WIDTH 9

//AXI DMAC has Write UID Parameter
//DMAC will have Write UID if at least one of the enabled channels has DMAX_CHx_WR_UID_EN == 1

`define APU_DMAX_HAS_WUID_PARAM 0

//AXI DMAC has Write UID Support


//Max. Write UID Parameter supported in DW_axi_dmac

`define APU_LOG2_DMAX_MAX_WUID 0



`define APU_DMAX_HS_IF_UPDT 0

`define APU_DMAX_NO_BCM36_4SEMISTATIC 1

//Internal Verification Specific Parameters

`define APU_DMAX_S_2_C_VERIF_EN 1


`define APU_DMAX_C_2_S_VERIF_EN 1


`define APU_DMAX_M1_2_C_VERIF_EN 1


`define APU_DMAX_C_2_M1_VERIF_EN 1


`define APU_DMAX_M2_2_C_VERIF_EN 1


`define APU_DMAX_C_2_M2_VERIF_EN 1


`define APU_DMAX_HS_2_C_VERIF_EN 1


`define APU_DMAX_C_2_HS_VERIF_EN 1


`define APU_ECC_EI_MEM_WIDTH 4


`define APU_ECC_EI_CH_WIDTH 5


`define APU_ECC_EI_POINTS_WIDTH 3


`define APU_ECC_BIT_SEL_WIDTH 9


//==============================================================================
// End Guard
//==============================================================================
`endif
