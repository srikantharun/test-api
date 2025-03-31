// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
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
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

////////////////////////////////////////////////////////////////////////////////
// Project:
//
//    DWC IME
//
// Description:
//
//   This file provides cc-constants used in DWC IME.
//
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//
// Language:         SystemVerilog
// Type:             RTL
//
// Filename:         $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ime/DWC_ime_cc_constants.svh#3 $
// Current Revision: $Revision: #3 $
// Last Updated:     $DateTime: 2024/03/25 23:59:08 $
// Last Changed:     $Date: 2024/03/25 $
// Change:           $Change: 8826010 $
//
//
//---------------------------------------------------------------------

////////////////////////////////////////////////////////////////////////////////
`ifndef __GUARD__DWC_IME_CC_CONSTANTS__SVH__
`define __GUARD__DWC_IME_CC_CONSTANTS__SVH__ 


// Name:         DWC_IME_CFG_CIPHER
// Default:      AES
// Values:       AES (0), SM4 (1)
// Enabled:      0
// 
// Select between cipher AES and SM4.
`define DWC_IME_CFG_CIPHER 0


`define DWC_REUSE_SM4_ENABLE 0


// Name:         DWC_IME_AMBA_APB_VERSION
// Default:      APB3 ((DDRCTL_APB5_EN==1)? 5 : (DDRCTL_APB4_EN==1)? 4 : 3 )
// Values:       APB3 (3), APB4 (4), APB5-E (5)
// Enabled:      0
// 
// Select between AMBA APB 3, AMBA APB 4 or AMBA APB 5-E version.
`define DWC_IME_AMBA_APB_VERSION 3


// `define DWC_IME_AMBA_APB4_EN


// `define DWC_IME_AMBA_APB5_E_EN


// `define DWC_IME_AMBA_APB4_OR_APB5_E_EN


// Name:         DWC_IME_APB_ADDR_WIDTH
// Default:      12
// Values:       1, ..., 32
// 
// APB address width.
`define DWC_IME_APB_ADDR_WIDTH 12


// Name:         DWC_IME_APB_DATA_WIDTH
// Default:      32
// Values:       1, ..., 32
// 
// APB data width.
`define DWC_IME_APB_DATA_WIDTH 32


// Name:         DWC_IME_HOST_CLK_EN
// Default:      0 (UMCTL2_P_ASYNC)
// Values:       0 1
// Enabled:      0
// 
// Enable a separate clock domain for the host register interface which is Asynchronous to Core Clock.
// `define DWC_IME_HOST_CLK_EN


// Name:         DWC_IME_SYNC_DEPTH
// Default:      2 (UMCTL2_ASYNC_REG_N_SYNC)
// Values:       2 3 4
// Enabled:      0
// 
// Sets the number of flip-flops in the cross domain synchronizers.  Generally, this should be left at 2,  
// but can be increased up to 4 to provide greater metastability protection at the expense of  
// increased latency in the synchronizers.
`define DWC_IME_SYNC_DEPTH 2


// Name:         DWC_IME_RST_ASYNC
// Default:      Synchronous Reset per Clock Domain
// Values:       Synchronous Reset per Clock Domain (0), Single Asynchronous Reset 
//               (1)
// Enabled:      0
// 
// Select if the reset has a single asynchronous reset input, or a synchronous reset input per clock domain.
// `define DWC_IME_RST_ASYNC


// `define DWC_IME_RST_PCLK_EN


// Name:         DWC_IME_ECB_ENGINE
// Default:      ECB disabled
// Values:       ECB disabled (0), ECB only (1)
// 
// Selects between on-demand ECB and ECB encryption engine.
// `define DWC_IME_ECB_ENGINE


// `define DWC_IME_ECB_EN


// Name:         DWC_IME_SBOX_ARCH
// Default:      Look-up table
// Values:       Look-up table (0), Galois field (1)
// 
// Selects the architecture of the s-boxes for AES. 
// Galois field s-boxes require less logic area.  Look-up table based s-boxes are 
// larger but synthesizes to higher clock frequencies. 
// Caution: So far setting this parameter to 1 is not supported!
`define DWC_IME_SBOX_ARCH 0


// Name:         DWC_IME_KEY_INST_KEY_EXP_ARCH
// Default:      Area
// Values:       Area (1), Performance (2)
// 
// Select the architecture of the Key Expander engine for computation of decryption key within Cipher Key Install block.  
//  -1: 128-bit iterative key expander.  
//  -2: none. This option could be used with SW key loading, where SW provides the computed decryption key instead.
`define DWC_IME_KEY_INST_KEY_EXP_ARCH 1


// Name:         DWC_IME_AES_4_ROUNDS_PER_CYCLE_EN
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// This parameter enables 4 AES rounds per clock cycle enhanced pipeline.
`define DWC_IME_AES_4_ROUNDS_PER_CYCLE_EN 0


// Name:         DWC_IME_AES_2_ROUNDS_PER_CYCLE_EN
// Default:      1
// Values:       0, 1
// Enabled:      0
// 
// This parameter enables 2 AES rounds per clock cycle pipeline.
`define DWC_IME_AES_2_ROUNDS_PER_CYCLE_EN 1


// Name:         DWC_IME_AES_DP_PIPELINE_FACTOR
// Default:      2 rounds per clock cycle ((DWC_IME_AES_4_ROUNDS_PER_CYCLE_EN==1) ? 
//               4 : (DWC_IME_AES_2_ROUNDS_PER_CYCLE_EN==1) ? 2 : 1)
// Values:       half round per clock cycle (0), 1 round per clock cycle (1), 2 
//               rounds per clock cycle (2), 4 rounds per clock cycle (4)
// Enabled:      0
// 
// This parameter controls how many clock cycles are needed to perform a complete encrypt/decrypt round. Selecting 1 round 
// per cycle has higher latency but relaxes the timing budget for synthesis. On the contrary, selecting 2 rounds per cycle 
// reduces the latency but constraints more the timing for synthesis. 
//  - 0: Half AES round per clock cycle.  
//  - 1: 1 AES round per clock cycle.  
//  - 2: 2 AES rounds per clock cycle.  
//  - 4: 4 AES rounds per clock cycle.
`define DWC_IME_AES_DP_PIPELINE_FACTOR 2


// Name:         DWC_IME_SM4_4_ROUNDS_PER_CYCLE_EN
// Default:      0
// Values:       0, 1
// Enabled:      DWC_IME_CFG_CIPHER==1
// 
// This parameter enables 4 SM4 rounds per clock cycle enhanced pipeline.
`define DWC_IME_SM4_4_ROUNDS_PER_CYCLE_EN 0


// Name:         DWC_IME_SM4_2_ROUNDS_PER_CYCLE_EN
// Default:      0
// Values:       0, 1
// Enabled:      DWC_IME_CFG_CIPHER==1
// 
// This parameter enables 2 SM4 rounds per clock cycle pipeline.
`define DWC_IME_SM4_2_ROUNDS_PER_CYCLE_EN 0


// Name:         DWC_IME_SM4_DP_PIPELINE_FACTOR
// Default:      AES lead latency (same pipeline factor as AES) 
//               ((DWC_IME_CFG_CIPHER==0) ? 0 : (DWC_IME_SM4_4_ROUNDS_PER_CYCLE_EN==1) ? 4 : 
//               (DWC_IME_SM4_2_ROUNDS_PER_CYCLE_EN==1) ? 2 : 1)
// Values:       AES lead latency (same pipeline factor as AES) (0), SM4 lead 
//               latency: 1 round per pipeline stage (1), SM4 lead latency: 2 rounds per 
//               pipeline stage (2), SM4 lead latency: 4 rounds per pipeline stage (4), 
//               SM4 lead latency: 8 rounds per pipeline stage (8)
// Enabled:      DWC_IME_CFG_CIPHER==1
// 
// This parameter defines the datapath and the tweak SM4 pipeline factor in fully unfolded operations. 
// The AES lead latency option uses the predefined distribution of the number of rounds per cycle that corresponds to 
// parameter DWC_IME_AES_KEY_SIZE.
`define DWC_IME_SM4_DP_PIPELINE_FACTOR 0


`define DWC_IME_AES_LEAD_LATENCY_EN


// Name:         DWC_IME_INPUT_FLOP
// Default:      1
// Values:       0, 1
// 
// This parameter provides the user the option to opt having internal input flops on both the WR and RD Data Interfaces, 
// to support a particular application targetting a higher frequency. 
// Note: This parameter also adds internal input flops on the RMW Key Swap Interface, when RMW key swap is enabled.
`define DWC_IME_INPUT_FLOP 1


`define DWC_IME_INPUT_FLOP_EN


// Name:         DWC_IME_UAES_XTS_CFG_INPUT_FLOP
// Default:      0
// Values:       0, 1
// 
// This parameter provides the user the option to opt out of having internal datapath flops at the 
// input of both read and write channel, to support a particular latency sensitive application.
`define DWC_IME_UAES_XTS_CFG_INPUT_FLOP 0


// Name:         DWC_IME_UAES_XTS_CFG_OUTPUT_FLOP
// Default:      1
// Values:       0, 1
// 
// This parameter provides the user the option to opt out of having internal datapath flops at the 
// output of both the read and write channel, to support a particular latency sensitive application.
`define DWC_IME_UAES_XTS_CFG_OUTPUT_FLOP 1


// Name:         DWC_IME_TWKGEN_INPUT_FLOP
// Default:      1
// Values:       0, 1
// 
// This parameter provides the user the option to opt having internal input flops on both the WR and RD Tweak Generation 
// Interfaces, 
// to support a particular application targetting a higher frequency.
`define DWC_IME_TWKGEN_INPUT_FLOP 1


`define DWC_IME_TWKGEN_INPUT_FLOP_EN


// Name:         DWC_IME_OUTPUT_FLOP
// Default:      0
// Values:       0, 1
// 
// This parameter provides the user the option to opt having internal output flops on both the WR and RD Data Interfaces, 
// to support a particular application targetting a higher frequency.
`define DWC_IME_OUTPUT_FLOP 0


// `define DWC_IME_OUTPUT_FLOP_EN


// Name:         DWC_IME_MAX_DATA_UNIT_LEN
// Default:      512 (DDRCTL_SECURE==1 ? ((MEMC_BURST_LENGTH * MEMC_DRAM_DATA_WIDTH) 
//               == 128 ? 4 : (MEMC_BURST_LENGTH * MEMC_DRAM_DATA_WIDTH) == 256 ? 5 : 
//               (MEMC_BURST_LENGTH * MEMC_DRAM_DATA_WIDTH) == 512 ? 6 : 7) : 6)
// Values:       128 256 512 1024
// Enabled:      0
// 
// Defines the Data Unit Length (bits)
`define DWC_IME_MAX_DATA_UNIT_LEN 6


`define DWC_IME_DATA_UNIT_LEN_WIDTH 2


// `define DWC_IME_DATA_UNIT_LEN_IS_1024BITS


`define DWC_IME_DATA_UNIT_LEN_IS_512BITS


// `define DWC_IME_DATA_UNIT_LEN_IS_256BITS


// `define DWC_IME_DATA_UNIT_LEN_IS_128BITS


`define DWC_IME_DATA_UNIT_LEN_IN_BLK 4


// Name:         DWC_IME_AES_KEY_SIZE
// Default:      256-bit
// Values:       128-bit (0), 256-bit (1)
// Enabled:      DWC_IME_CFG_CIPHER==0
// 
// Selects the maximum AES key-size to be supported by the core. When 256-bit value is selected, the IP supports both  
// 128-bit key traffic and 256-bit key traffic for AES Cipher. 
// Note: 256-bit keys will require more memory resources and increases the usage area 
// -0: 128-bit ( 256 bits for CKEY and TKEY in AES-XTS, and 128 bits for  one CKEY in AES-ECB ) 
// -1: 256-bit ( 512 bits for CKEY and TKEY in AES-XTS, and 256 bits for  one CKEY in AES-ECB )
`define DWC_IME_AES_KEY_SIZE 1


// Name:         DWC_IME_LATENCY_OPTION
// Default:      Reduced latency ((DWC_IME_AES_KEY_SIZE==1) && 
//               (DWC_IME_CFG_CIPHER==0))
// Values:       Fixed latency (0), Reduced latency (1)
// 
// This parameter selects the option for the datapath latency: 
// 0: Fixed latency, based on Ckey 256-bit 
// 1: Reduced latency, based on either Ckey 128-bit or Ckey 256-bit
`define DWC_IME_LATENCY_OPTION 1


`define DWC_IME_LATENCY_OPTION1


`define DWC_IME_AES_KEY_WIDTH 256


`define DWC_IME_AES_KEY256_EN


// Name:         DWC_IME_DP_WIDTH
// Default:      256 (DDRCTL_SECURE==1 ? (MEMC_DRAM_DATA_WIDTH * MEMC_FREQ_RATIO * 
//               2) : 256)
// Values:       128 256 512
// Enabled:      0
// 
// IME Datapath Width
`define DWC_IME_DP_WIDTH 256


`define DWC_IME_DP_WIDTH_REG_VAL 1


// `define DWC_IME_DP_WIDTH_IS_128


`define DWC_IME_DP_WIDTH_IS_256


// `define DWC_IME_DP_WIDTH_IS_512


`define DWC_IME_OFFSET_EN


`define DWC_IME_RANDOM_BLK_SEQ_ACCESS_EN


`define DWC_IME_NUM_AES_BLOCKS 2


`define DWC_IME_ENC_OFFSET_WIDTH 1


`define DWC_IME_ENC_LENGTH_WIDTH 1


`define DWC_IME_ENC_BLK_LENGTH_WIDTH 2


// Name:         DWC_IME_WRCH_PASSTHRU_WIDTH
// Default:      7 ((DDRCTL_METADATA_EN==1) ? ((DDRCTL_KBD_SBECC_EN==1) ? 
//               (DDRCTL_HIF_METADATA_WIDTH + DDRCTL_HIF_KBD_WIDTH + UMCTL2_WDATARAM_AW) : 
//               (DDRCTL_HIF_METADATA_WIDTH + UMCTL2_WDATARAM_AW)) : 
//               ((DDRCTL_KBD_SBECC_EN==1) ? (DDRCTL_HIF_KBD_WIDTH + UMCTL2_WDATARAM_AW) : 
//               UMCTL2_WDATARAM_AW))
// Values:       0, ..., 128
// Enabled:      0
// 
// Selects a specific amount of sideband signals for write channel, that can be propagated through the IME, together with 
// the data. This signals are not encrypted/decrypted and are only pipelined in a way to match the  
// delay of the data that needs to be encrypted/decrypted. Note the sideband 
// signals for write channel don't exist if this parameter is set to 0
`define DWC_IME_WRCH_PASSTHRU_WIDTH 7


`define DWC_IME_WRCH_PASSTHRU_EN


// Name:         DWC_IME_RDCH_PASSTHRU_WIDTH
// Default:      0 ((DDRCTL_METADATA_EN==1) ? DDRCTL_HIF_METADATA_WIDTH :0)
// Values:       0, ..., 128
// Enabled:      0
// 
// Selects a specific amount of sideband signals for read channel, that can be propagated through the IME, together with 
// the data. This signals are not encrypted/decrypted and are only pipelined 
// in a way to match the delay of the data that needs to be encrypted/decrypted (bits). Note the sideband signals for read 
// channel don't exist if this parameter is set to 0
`define DWC_IME_RDCH_PASSTHRU_WIDTH 0


// `define DWC_IME_RDCH_PASSTHRU_EN



// Name:         DWC_IME_REGION_MGR_EN
// Default:      0 ((DDRCTL_CHB_RME_EN==1) ? 0 : ((DWC_IME_NUM_REGIONS>1) && 
//               (DWC_IME_NUM_REGIONS<=16)))
// Values:       0, 1
// Enabled:      0
// 
// This parameter that allows to select the type of region control: 
// Disabled - Tweak Index Region Control 
// Selects which key to use depending on the value passed by an input signal. This input signal is connected to the DDR 
// Controller or other Bus Components,  
// that can decode depending on sideband or system information which key will be used (for example,  this is used to have 
// different keys mapped to different secure realms). 
// Enabled - Address Range Region Control 
// The SoC configure up to 16 memory regions, that are defined based on address space, each region has independent keys. 
// This parameter is only enabled for configs with DWC_IME_NUM_REGIONS>1.
// `define DWC_IME_REGION_MGR_EN


`define DWC_IME_NUM_REGIONS_WIDTH 0


`define DWC_IME_NUM_REGIONS_IS_POW2


// `define DWC_IME_NUM_REGIONS_2_TO_16


// Name:         DWC_IME_KEY_SWAP
// Default:      no Key swap enabled
// Values:       no Key swap enabled (0), Key Swap enabled (1)
// Enabled:      0
// 
// Enables the Key-swap feature  
// Note: This can only be used for Address Region Management or if the number of regions is equal to 1 
// Note: Enabling this feature doubles the memory required for storing keys, as the double number of contexts is required 
// for the internal AES cores
`define DWC_IME_KEY_SWAP 0


// `define DWC_IME_KEY_SWAP_EN


// Name:         DWC_IME_RMW_KEY_SWAP_EN
// Default:      0 ((DWC_IME_KEY_SWAP==1) && (DWC_IME_TWKGEN_INPUT_FLOP==1) && 
//               (DWC_IME_INPUT_FLOP==1))
// Values:       0, 1
// 
// Enables the RMW Key-swap feature 
// Note: This can only be used for Address Region Management or if the number of regions is equal to 1 
// Enabling this feature will allow to use the scrubbing mechanism to swap a key for a given memory region. This allows an 
// application to refresh keys during mission mode without the need of making the DRAM unavailable to the system.
// `define DWC_IME_RMW_KEY_SWAP_EN


// Name:         DWC_IME_REGION_ADDR_EN
// Default:      0 (DWC_IME_REGION_MGR_EN || DWC_IME_RMW_KEY_SWAP_EN)
// Values:       0, 1
// 
// Enables the Region range configuration registers 
// These registers exist when region management is enabled or when RMW key swap is enabled
// `define DWC_IME_REGION_ADDR_EN


// Name:         DWC_IME_DDRC_INTEGRATION
// Default:      0 ((DWC_IME_REGION_MGR_EN || DWC_IME_RMW_KEY_SWAP_EN)==1)
// Values:       0 1
// Enabled:      0
// 
// Integrated with DDRC
`define DWC_IME_DDRC_INTEGRATION 0


// `define DWC_IME_DDRC_INTEGRATION_EN


// `define DWC_IME_RW_SOFTWARE_BW_REG_EN


`define DWC_IME_NUM_KEYS 1


// `define DWC_IME_NUM_KEYS_HIGHER_THAN_ONE


// Name:         DWC_IME_NO_KEY_SEC_TRAFFIC_BEH
// Default:      Encrypt with whatever Key values are in the memories
// Values:       Encrypt with whatever Key values are in the memories (0), Bypass 
//               traffic, i.e. do not encrypt/decrypt (1), Zeroize Write/Read data (2)
// 
// Defines the behavior of the IME core when no Key is programmed for a given region/context 
// 0: Encrypt with whatever Key values are in the memories 
// 1: Bypass traffic, i.e. do not encrypt/decrypt 
// 2: Zeroize Write/Read data
`define DWC_IME_NO_KEY_SEC_TRAFFIC_BEH 0


`define DWC_IME_NO_KEY_SEC_TRAFFIC_BEH_IS_0


// `define DWC_IME_NO_KEY_SEC_TRAFFIC_BEH_IS_1


// `define DWC_IME_NO_KEY_SEC_TRAFFIC_BEH_IS_2


// Name:         DWC_IME_FIPS_TEST_MODE_EN
// Default:      1
// Values:       0 1
// 
// Enable IME FIPS Test Mode support
`define DWC_IME_FIPS_TEST_MODE_EN


// Name:         DWC_IME_SYNTH_CKEY_MEM
// Default:      1
// Values:       0 1
// Enabled:      0
// 
// If enabled, The cipher key memory is synthesized as flip-flops. 
// Otherwise an external SRAM needs to be connected by the integrator by the specific in/out ports available at the IP 
// boundary.
`define DWC_IME_SYNTH_CKEY_MEM

//x// ORIGINAL ENABLED CONDITION Enabled (@DWC_IME_ECB_ENGINE==0)

// Name:         DWC_IME_SYNTH_TKEY_MEM
// Default:      1
// Values:       0 1
// Enabled:      0
// 
// If enabled, the tweak key memory is synthesized as flip-flops. 
// Otherwise an external SRAM is connected by the integrator by the specific in/out ports available at the IP boundary.
`define DWC_IME_SYNTH_TKEY_MEM

//x// ORIGINAL ENABLED CONDITION Enabled (@DWC_IME_ECB_ENGINE==0)

// Name:         DWC_IME_SYNTH_TVAL_MEM
// Default:      1
// Values:       0 1
// Enabled:      0
// 
// If enabled, the tweak value memory is synthesized as flip-flops. 
// Otherwise an external SRAM is connected by the integrator by the specific in/out ports available at the IP boundary.
`define DWC_IME_SYNTH_TVAL_MEM


`define DWC_IME_SYNTH_MEM_EN


// Name:         DWC_IME_SRAM_ECC_EN
// Default:      0
// Values:       0, 1
// Enabled:      ((DWC_IME_SYNTH_CKEY_MEM==0) || ((DWC_IME_SYNTH_TKEY_MEM==0) && 
//               (DWC_IME_ECB_ENGINE==0)) || ((DWC_IME_SYNTH_TVAL_MEM==0) && 
//               (DWC_IME_ECB_ENGINE==0)))
// 
// Enable ECC support for external SRAMs.
// `define DWC_IME_SRAM_ECC_EN


// `define DWC_IME_TKEY_ECC_EN


// `define DWC_IME_CKEY_ECC_EN


// `define DWC_IME_TVAL_ECC_EN


// `define DWC_IME_CKEY_TKEY_ECC_EN


// `define DWC_IME_TKEY_TVAL_ECC_EN


// `define DWC_IME_CKEY_NTKEY_TVAL_ECC_EN


// `define DWC_IME_ECC_REGS_EN


// Name:         DWC_IME_MEM_WR_LATENCY
// Default:      1
// Values:       1 2
// Enabled:      ((DWC_IME_SYNTH_CKEY_MEM==0) || ((DWC_IME_SYNTH_TKEY_MEM==0) && 
//               (DWC_IME_ECB_ENGINE==0)) || ((DWC_IME_SYNTH_TVAL_MEM==0) && 
//               (DWC_IME_ECB_ENGINE==0)))
// 
// Sets the memory write latency for the CKEY,TKEY and TWEAK-VAL memories
`define DWC_IME_MEM_WR_LATENCY 1


// `define DWC_IME_MEM_WR_LATENCY_GT_1


// Name:         DWC_IME_MEM_RD_LATENCY
// Default:      1
// Values:       1 2 3 4
// Enabled:      ((DWC_IME_SYNTH_CKEY_MEM==0) || ((DWC_IME_SYNTH_TKEY_MEM==0) && 
//               (DWC_IME_ECB_ENGINE==0)) || ((DWC_IME_SYNTH_TVAL_MEM==0) && 
//               (DWC_IME_ECB_ENGINE==0)))
// 
// Sets the memory read latency for the CKEY,TKEY and TWEAK-VAL memories
`define DWC_IME_MEM_RD_LATENCY 1


// `define DWC_IME_MEM_RD_LATENCY_GT_1



// `define DWC_IME_MEM_RD_LATENCY_GT_2



// `define DWC_IME_MEM_RD_LATENCY_GT_3


// Name:         DWC_IME_HW_INIT_EN
// Default:      0
// Values:       0, 1
// 
// Enables the hardware initialization feature used for memory initialization  
// by hardware mechanisms.
// `define DWC_IME_HW_INIT_EN


// Name:         DWC_IME_KEY_INVALIDATION_EN
// Default:      1 ((DWC_IME_HW_INIT_EN==1) || ((DWC_IME_SYNTH_CKEY_MEM==1) && 
//               (DWC_IME_SYNTH_TKEY_MEM==1)))
// Values:       0, 1
// 
// Enables the invalidation of a key that has been previously installed.  
// Enabled if hardware initialization is enabled or if the Cipher and Tweak key memories are both synthesized as 
// flip-flops. 
// Note: Both the Primary and Secondary Key slots respective to each region can be invalidated if Key Swapping is 
// supported.
`define DWC_IME_KEY_INVALIDATION_EN


// Name:         DWC_IME_DEBUG_MODE_EN
// Default:      0
// Values:       0, 1
// 
// Enables IME Debug Mode support.
// `define DWC_IME_DEBUG_MODE_EN


// Name:         DWC_IME_WRCH_NUM_TWEAK_VAL
// Default:      64 (MEMC_NO_OF_ENTRY)
// Values:       2, ..., 64
// Enabled:      0
// 
// The max number of tweak value that tweak value memory can hold for write channel. This parameter should be properly 
// chosen to match the number of outstanding transactions.
`define DWC_IME_WRCH_NUM_TWEAK_VAL 64


`define DWC_IME_WRCH_NUM_TWEAK_VAL_WIDTH 6


// Name:         DWC_IME_RDCH_NUM_TWEAK_VAL
// Default:      32 (MEMC_RT_FIFO_DEPTH)
// Values:       2, ..., 64
// Enabled:      0
// 
// The max number of tweak value that tweak value memory can hold for read channel. This parameter should be properly 
// chosen to match the number of outstanding transactions.
`define DWC_IME_RDCH_NUM_TWEAK_VAL 32


`define DWC_IME_RDCH_NUM_TWEAK_VAL_WIDTH 5


// Name:         DWC_IME_BUS_ADDR_WIDTH
// Default:      29 (MEMC_HIF_ADDR_WIDTH - ((MEMC_BURST_LENGTH==8)? 3 : 
//               (MEMC_BURST_LENGTH==16)? 4 : 5))
// Values:       32-DWC_IME_MAX_DATA_UNIT_LEN, ..., 64-DWC_IME_MAX_DATA_UNIT_LEN
// Enabled:      0
// 
// Controller Bus address width (for example, for DDRC corresponds to the HIF Bus Address Width).
`define DWC_IME_BUS_ADDR_WIDTH 29


`define DWC_IME_BYTE_ADDR_WIDTH 35



// Name:         DWC_IME_BUS_ADDR_WIDTH_GT_32
// Default:      0 (DWC_IME_BUS_ADDR_WIDTH > 32? 1:0)
// Values:       0, 1
// 
// This derived parameter defines if Bus Address Width Is Greater Than 32
// `define DWC_IME_BUS_ADDR_WIDTH_GT_32


// Name:         DWC_IME_BYTE_ADDR_WIDTH_GT_32
// Default:      1 (DWC_IME_BYTE_ADDR_WIDTH > 32? 1:0)
// Values:       0, 1
// 
// This derived parameter defines if Byte Address Width Is Greater Than 32
`define DWC_IME_BYTE_ADDR_WIDTH_GT_32


// Name:         DWC_IME_NUM_REGIONS_GT_1
// Default:      0 ((DWC_IME_NUM_REGIONS > 1 && DWC_IME_NUM_REGIONS <= 16) ? 1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 1
// `define DWC_IME_NUM_REGIONS_GT_1


// Name:         DWC_IME_NUM_REGIONS_GT_2
// Default:      0 ((DWC_IME_NUM_REGIONS > 2 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 2
// `define DWC_IME_NUM_REGIONS_GT_2


// Name:         DWC_IME_NUM_REGIONS_GT_3
// Default:      0 ((DWC_IME_NUM_REGIONS > 3 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 3
// `define DWC_IME_NUM_REGIONS_GT_3


// Name:         DWC_IME_NUM_REGIONS_GT_4
// Default:      0 ((DWC_IME_NUM_REGIONS > 4 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 4
// `define DWC_IME_NUM_REGIONS_GT_4


// Name:         DWC_IME_NUM_REGIONS_GT_5
// Default:      0 ((DWC_IME_NUM_REGIONS > 5 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 5
// `define DWC_IME_NUM_REGIONS_GT_5


// Name:         DWC_IME_NUM_REGIONS_GT_6
// Default:      0 ((DWC_IME_NUM_REGIONS > 6 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 6
// `define DWC_IME_NUM_REGIONS_GT_6


// Name:         DWC_IME_NUM_REGIONS_GT_7
// Default:      0 ((DWC_IME_NUM_REGIONS > 7 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 7
// `define DWC_IME_NUM_REGIONS_GT_7


// Name:         DWC_IME_NUM_REGIONS_GT_8
// Default:      0 ((DWC_IME_NUM_REGIONS > 8 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 8
// `define DWC_IME_NUM_REGIONS_GT_8


// Name:         DWC_IME_NUM_REGIONS_GT_9
// Default:      0 ((DWC_IME_NUM_REGIONS > 9 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 9
// `define DWC_IME_NUM_REGIONS_GT_9


// Name:         DWC_IME_NUM_REGIONS_GT_10
// Default:      0 ((DWC_IME_NUM_REGIONS > 10 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 10
// `define DWC_IME_NUM_REGIONS_GT_10


// Name:         DWC_IME_NUM_REGIONS_GT_11
// Default:      0 ((DWC_IME_NUM_REGIONS > 11 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 11
// `define DWC_IME_NUM_REGIONS_GT_11


// Name:         DWC_IME_NUM_REGIONS_GT_12
// Default:      0 ((DWC_IME_NUM_REGIONS > 12 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 12
// `define DWC_IME_NUM_REGIONS_GT_12


// Name:         DWC_IME_NUM_REGIONS_GT_13
// Default:      0 ((DWC_IME_NUM_REGIONS > 13 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 13
// `define DWC_IME_NUM_REGIONS_GT_13


// Name:         DWC_IME_NUM_REGIONS_GT_14
// Default:      0 ((DWC_IME_NUM_REGIONS > 14 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 14
// `define DWC_IME_NUM_REGIONS_GT_14


// Name:         DWC_IME_NUM_REGIONS_GT_15
// Default:      0 ((DWC_IME_NUM_REGIONS > 15 && DWC_IME_NUM_REGIONS <= 16) ?  1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions Greater Than 15
// `define DWC_IME_NUM_REGIONS_GT_15


// Name:         DWC_IME_NUM_REGIONS_GT_16
// Default:      0 ((DWC_IME_NUM_REGIONS > 16) ? 1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions is Greater than 16
// `define DWC_IME_NUM_REGIONS_GT_16


// Name:         DWC_IME_NUM_REGIONS_GT_512
// Default:      0 ((DWC_IME_NUM_REGIONS > 512) ? 1:0)
// Values:       0, 1
// 
// This derived parameter defines if  Number of Available regions is Greater than 512
// `define DWC_IME_NUM_REGIONS_GT_512


// Name:         DWC_IME_BREAK_REGION_SEL_PATH
// Default:      0 ((DWC_IME_NUM_REGIONS_GT_512==1)? 1:0)
// Values:       0, 1
// Enabled:      DWC_IME_NUM_REGIONS_GT_512==0
// 
// This parameter provides the user the option to break critical path by inserting an internal flop. This parameter will be 
// set to 1  
// automatically when number of key is set to 1 K.
`define DWC_IME_BREAK_REGION_SEL_PATH 0


// `define DWC_IME_BREAK_REGION_SEL_PATH_EN


// `define DWC_IME_NUM_REGIONS_HIGHER_THAN_ONE


// Name:         DWC_IME_TWKGEN_KEY_INDEX_EN
// Default:      0 (((DWC_IME_NUM_REGIONS_2_TO_16) && (DWC_IME_REGION_MGR_EN==0)) || 
//               (DWC_IME_NUM_REGIONS_GT_16==1))
// Values:       0, 1
// 
// This derived parameter enables the I_wr_twkgen_key_index/I_rd_twkgen_key_index IME input ports
// `define DWC_IME_TWKGEN_KEY_INDEX_EN


// Name:         DWC_IME_VER_NUM_VAL
// Default:      0x103
// Values:       0x0, ..., 0xffffffff
// Enabled:      0
// 
// This parameter defines the Core Version field.
`define DWC_IME_VER_NUM_VAL 16'h103


// Name:         DWC_IME_TYPE_NUM_VAL
// Default:      0x2
// Values:       0x0, ..., 0xffffffff
// Enabled:      0
// 
// This parameter defines the Core Type field.
`define DWC_IME_TYPE_NUM_VAL 8'h2


// Name:         DWC_IME_PKG_NUM_VAL
// Default:      0xa
// Values:       0x0, ..., 0xffffffff
// Enabled:      0
// 
// This parameter defines the Core Package field.
`define DWC_IME_PKG_NUM_VAL 4'ha


// Name:         DWC_IME_TYPE_ENUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// Enabled:      0
// 
// This parameter defines the Core Type enumerated field.
`define DWC_IME_TYPE_ENUM_VAL 4'h0

/////////////////////////////////////////////////////////////////////////////////////////////////////
//AES XTS WRCH
////////////////////////////////////////////////////////////////////////////////////////////////////


`define DWC_IME_WRCH_ULTRA_AES_XTS_DP_UNLIMITED 1


// `define DWC_IME_WRCH_ULTRA_AES_XTS_DP_LIMITED


`define DWC_IME_WRCH_UAES_XTS_CFG_DP_SLICES 2


`define DWC_IME_WRCH_UAES_XTS_CFG_CIPHER 2'h0


`define DWC_IME_WRCH_UAES_XTS_CFG_OP_MODE 2'h0


`define DWC_IME_WRCH_UAES_XTS_CFG_MAX_KEY_SIZE 1


// `define DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_FIPS_SELF_TEST 2'h2


`define DWC_IME_WRCH_UAES_XTS_CFG_INHIBIT_DEFAULT 1'h0


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_BIST_EN 1'h0


`define DWC_IME_WRCH_UAES_XTS_CFG_IDLE_BYPASS_DEFAULT 1'h1


// `define DWC_IME_WRCH_UAES_XTS_CFG_FIPS_TEST_ENA_SRC


`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_BP_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_CTS_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_CTS_IN_ORDER


`define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR 3'h2


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR 4'h0


// Name:         DWC_IME_WRCH_UAES_XTS_CFG_INPUT_FLOP
// Default:      0 (DWC_IME_UAES_XTS_CFG_INPUT_FLOP)
// Values:       0, 1
// 
// This parameter provides the user the option to opt out of having internal datapath flops at the 
// input of the Write Channel AES-XTS core, to support a particular latency sensitive application.
`define DWC_IME_WRCH_UAES_XTS_CFG_INPUT_FLOP 0


// Name:         DWC_IME_WRCH_UAES_XTS_CFG_OUTPUT_FLOP
// Default:      1 (DWC_IME_UAES_XTS_CFG_OUTPUT_FLOP)
// Values:       0, 1
// 
// This parameter provides the user the option to opt out of having internal datapath flops at the, 
// output of the Write Channel AES-XTS core, to support a particular latency sensitive application.
`define DWC_IME_WRCH_UAES_XTS_CFG_OUTPUT_FLOP 1


// Name:         DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP
// Default:      0
// Values:       0, 1
// 
// Defines whether the input TWK Gen has internal input flops. 
// A latency sensitive application may require you to disable these flops.
`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP 0


// Name:         DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP
// Default:      0
// Values:       0, 1
// 
// Defines whether the internal TWK Gen has internal output flops. 
// A latency sensitive application may require you to disable these flops.
`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP 0


`define DWC_IME_WRCH_UAES_XTS_CFG_LATENCY_OPTION 1


`define DWC_IME_WRCH_UAES_XTS_CFG_PIPE_BYPASS_LATENCY

//---------------------------------------------------------------------

`define DWC_IME_WRCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_DATA_UNIT_LEN 6


`define DWC_IME_WRCH_UAES_XTS_CFG_PRE_TWEAK_CNT 1


`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_ARCH 0


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_TWK_GEN_ARCH 0


`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GMULT_STAGES_GUI 1

//---------------------------------------------------------------------


`define DWC_IME_WRCH_UAES_XTS_CFG_SBOX_ARCH 0


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_INST_KEY_EXP_ARCH 1


// `define DWC_IME_WRCH_UAES_XTS_CFG_ENABLE_SW_DEC_INSTALL

//---------------------------------------------------------------------


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_IF_TYPE 0


// `define DWC_IME_WRCH_UAES_XTS_CFG_SKP_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_PASSTHRU_WIDTH 7


// `define DWC_IME_WRCH_UAES_XTS_CFG_HOST_CLK_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_SKP_CLK_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_MULTI_CLK_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_SYNC_DEPTH 2


// `define DWC_IME_WRCH_UAES_XTS_CFG_RST_ASYNC

//---------------------------------------------------------------------


// `define DWC_IME_WRCH_UAES_XTS_CFG_HW_INIT_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_NUM_CTX_GUI 1


`define DWC_IME_WRCH_UAES_XTS_CFG_NUM_TWK_CTX_GUI 64


`define DWC_IME_WRCH_UAES_XTS_CFG_SYNTH_CKEY_MEM


`define DWC_IME_WRCH_UAES_XTS_CFG_SYNTH_TKEY_MEM


`define DWC_IME_WRCH_UAES_XTS_CFG_SYNTH_TVAL_MEM


// `define DWC_IME_WRCH_UAES_XTS_CFG_SP_CKEY_MEM


// `define DWC_IME_WRCH_UAES_XTS_CFG_SP_TKEY_MEM


// `define DWC_IME_WRCH_UAES_XTS_CFG_SP_TVAL_MEM


`define DWC_IME_WRCH_UAES_XTS_CFG_MEM_WR_LATENCY 1


`define DWC_IME_WRCH_UAES_XTS_CFG_MEM_RD_LATENCY_GUI 1


//---------------------------------------------------------------------
// Some derived parameters


`define DWC_IME_WRCH_UAES_XTS_CFG_OUTPUT_FLOP_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_INPUT_FLOP_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_LATENCY_OPTION0


`define DWC_IME_WRCH_UAES_XTS_CFG_LATENCY_OPTION1


// `define DWC_IME_WRCH_UAES_XTS_CFG_LATENCY_OPTION2


`define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_1


`define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_2


// `define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_3


// `define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_4


// `define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_5


// `define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_6


// `define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_7


// `define DWC_IME_WRCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_8


`define DWC_IME_WRCH_UAES_XTS_CFG_DP_WIDTH 13'h100


`define DWC_IME_WRCH_UAES_XTS_CFG_DP_PIPE_NUM 13'h7


`define DWC_IME_WRCH_UAES_XTS_CFG_AES_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_SM4_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_AES_AND_SM4_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_ENC_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_DEC_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_ENC_ONLY_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_DEC_ONLY_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_ENC_AND_DEC_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY128_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY256_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_WIDTH 512


`define DWC_IME_WRCH_UAES_XTS_CFG_CIPHER_KEY_WIDTH 256


`define DWC_IME_WRCH_UAES_XTS_CFG_SK_ADDR_WIDTH 4


`define DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN_BIT 0


`define DWC_IME_WRCH_UAES_XTS_CFG_CTS_EN_BIT 0


`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_ARCH_10_14


// `define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_ARCH_5_7


// `define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_ARCH_2_2


// `define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_ARCH_1_1


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_TWK_GEN_ARCH_PIPELINED


// `define DWC_IME_WRCH_UAES_XTS_CFG_SM4_TWK_GEN_ARCH_ITERATED


// `define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR_HALF_OR_1


// `define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR_HALF


// `define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR1


// `define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR01


`define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR2


// `define DWC_IME_WRCH_UAES_XTS_CFG_PIPELINE_FACTOR4


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR_SAME_AS_AES


// `define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR1


// `define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR2


// `define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR4


// `define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR8


`define DWC_IME_WRCH_UAES_XTS_CFG_BSEQ_WIDTH 2


// `define DWC_IME_WRCH_UAES_XTS_CFG_SINGLE_BLK_DATA_UNIT


`define DWC_IME_WRCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS 1


`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_GMULT_STAGES 2'h1


// `define DWC_IME_WRCH_UAES_XTS_CFG_SW_KEY_DEC_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_HW_KEY_DEC_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_IF_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_SKP_EN_BIT 0


`define DWC_IME_WRCH_UAES_XTS_CFG_PASSTHRU_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_NUM_CTX 17'h1


`define DWC_IME_WRCH_UAES_XTS_CFG_NUM_TWK_CTX 17'h40


`define DWC_IME_WRCH_UAES_XTS_CFG_CTX_WIDTH 1


`define DWC_IME_WRCH_UAES_XTS_CFG_NUM_CTX_IS_POW2



`define DWC_IME_WRCH_UAES_XTS_CFG_TWK_CTX_WIDTH 6


`define DWC_IME_WRCH_UAES_XTS_CFG_NUM_TWK_CTX_IS_POW2


// `define DWC_IME_WRCH_UAES_XTS_CFG_CTX_IS_POW2


`define DWC_IME_WRCH_UAES_XTS_CFG_CKEY_ADDR_WIDTH 1


`define DWC_IME_WRCH_UAES_XTS_CFG_TKEY_ADDR_WIDTH 1


`define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_ADDR_WIDTH 6


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_INVALIDATE_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_INVALIDATE_ENA 1


`define DWC_IME_WRCH_UAES_XTS_CFG_KEY_MEM_DATA_WIDTH 258


`define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_MEM_DATA_WIDTH 128


`define DWC_IME_WRCH_UAES_XTS_CFG_TPRAM_USED 1


`define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_MEM0_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_MEM1_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_INT_TVAL_MEM1_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_MEM2_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_MEM3_EN


// `define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_SEQ_MEM_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_MEM_RD_LATENCY 3'h1


`define DWC_IME_WRCH_UAES_XTS_CFG_PASSTHRU_LATENCY 21


// Name:         DWC_IME_WRCH_UAES_XTS_CFG_CMD_DATA_DELAY
// Default:      2 (DWC_IME_WRCH_UAES_XTS_CFG_INPUT_FLOP + 
//               DWC_IME_WRCH_UAES_XTS_CFG_MEM_RD_LATENCY + ((DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN==0) ? 
//               DWC_IME_WRCH_UAES_XTS_CFG_TWK_GMULT_STAGES : 1))
// Values:       1, ..., (DWC_IME_WRCH_UAES_XTS_CFG_INPUT_FLOP + 
//               DWC_IME_WRCH_UAES_XTS_CFG_MEM_RD_LATENCY + ((DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN==0) ? 
//               DWC_IME_WRCH_UAES_XTS_CFG_TWK_GMULT_STAGES : 1))
// 
// Maximum acceptable time delay from command to data request on write channel. 
//  Data load can be received on the same cycle with command request, or delayed up to 
//  this number of cycles later than the command request.
`define DWC_IME_WRCH_UAES_XTS_CFG_CMD_DATA_DELAY 2


`define DWC_IME_WRCH_UAES_XTS_CFG_FIPS_SELF_TEST_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_FIPS_SELF_TEST_INT_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_AES_PIPE_NUM_DEPTH 7


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_PIPE_NUM_DEPTH 4


`define DWC_IME_WRCH_UAES_XTS_CFG_PIPE_NUM_DEPTH 7


`define DWC_IME_WRCH_UAES_XTS_CFG_CTS_IN_ORDER_CALC 0


`define DWC_IME_WRCH_UAES_XTS_CFG_AES_DP_PIPE_NUM_DEPTH 7


`define DWC_IME_WRCH_UAES_XTS_CFG_SM4_DP_PIPE_NUM_DEPTH 4


`define DWC_IME_WRCH_UAES_XTS_CFG_DP_PIPE_NUM_DEPTH 7


`define DWC_IME_WRCH_UAES_XTS_CFG_CTS_PIPE_NUM_DEPTH 7


// Name:         DWC_IME_WRCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN
// Default:      10 (DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP + 
//               DWC_IME_WRCH_UAES_XTS_CFG_MEM_RD_LATENCY + 
//               DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP + DWC_IME_WRCH_UAES_XTS_CFG_PIPE_NUM_DEPTH + (1 + 
//               DWC_IME_WRCH_UAES_XTS_CFG_MEM_WR_LATENCY))
// Values:       1, ..., (DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP + 
//               DWC_IME_WRCH_UAES_XTS_CFG_MEM_RD_LATENCY + 
//               DWC_IME_WRCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP + DWC_IME_WRCH_UAES_XTS_CFG_PIPE_NUM_DEPTH + (1 + 
//               DWC_IME_WRCH_UAES_XTS_CFG_MEM_WR_LATENCY))
// 
// AES-XTS Tweak Generation Latency for write channel.
`define DWC_IME_WRCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN 10


// Name:         DWC_IME_WRCH_TWKGEN_LATENCY
// Default:      11 (DWC_IME_WRCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN + 
//               DWC_IME_TWKGEN_INPUT_FLOP)
// Values:       1, ..., (DWC_IME_WRCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN + 
//               DWC_IME_TWKGEN_INPUT_FLOP)
// 
// IME Tweak Generation Latency for write channel.
`define DWC_IME_WRCH_TWKGEN_LATENCY 11


`define DWC_IME_WRCH_UAES_XTS_CFG_PIPE_NUM_WIDTH 1


// `define DWC_IME_WRCH_UAES_XTS_CFG_RST_PCLK_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_RST_PCLK_EN_BIT 0


// `define DWC_IME_WRCH_UAES_XTS_CFG_RST_SKP_EN


`define DWC_IME_WRCH_UAES_XTS_CFG_RST_SKP_EN_BIT 0


// Name:         DWC_IME_WRCH_UAES_XTS_VER_NUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Version field.
`define DWC_IME_WRCH_UAES_XTS_VER_NUM_VAL 16'h0


// Name:         DWC_IME_WRCH_UAES_XTS_TYPE_NUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Type field.
`define DWC_IME_WRCH_UAES_XTS_TYPE_NUM_VAL 8'h0


// Name:         DWC_IME_WRCH_UAES_XTS_PKG_NUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Package field.
`define DWC_IME_WRCH_UAES_XTS_PKG_NUM_VAL 4'h0


// Name:         DWC_IME_WRCH_UAES_XTS_TYPE_ENUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Type enumerated field.
`define DWC_IME_WRCH_UAES_XTS_TYPE_ENUM_VAL 4'h0


// `define DWC_IME_WRCH_UAES_XTS_CFG_APB4


// `define DWC_IME_WRCH_UAES_XTS_CFG_APB5

/////////////////////////////////////////////////////////////////////////////////////////////////////
//AES XTS RDCH
////////////////////////////////////////////////////////////////////////////////////////////////////


`define DWC_IME_RDCH_ULTRA_AES_XTS_DP_UNLIMITED 1


// `define DWC_IME_RDCH_ULTRA_AES_XTS_DP_LIMITED


`define DWC_IME_RDCH_UAES_XTS_CFG_DP_SLICES 2


`define DWC_IME_RDCH_UAES_XTS_CFG_CIPHER 2'h0


`define DWC_IME_RDCH_UAES_XTS_CFG_OP_MODE 2'h1


`define DWC_IME_RDCH_UAES_XTS_CFG_MAX_KEY_SIZE 1


// `define DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_FIPS_SELF_TEST 2'h2


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_BIST_EN 1'h0


`define DWC_IME_RDCH_UAES_XTS_CFG_INHIBIT_DEFAULT 1'h0


`define DWC_IME_RDCH_UAES_XTS_CFG_IDLE_BYPASS_DEFAULT 1'h1


// `define DWC_IME_RDCH_UAES_XTS_CFG_FIPS_TEST_ENA_SRC


`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_BP_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_CTS_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_CTS_IN_ORDER


`define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR 3'h2


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR 4'h0


// Name:         DWC_IME_RDCH_UAES_XTS_CFG_INPUT_FLOP
// Default:      0 (DWC_IME_UAES_XTS_CFG_INPUT_FLOP)
// Values:       0, 1
// 
// This parameter provides the user the option to opt out of having internal datapath flops at the 
// input of the Read Channel AES-XTS core, to support a particular latency sensitive application.
`define DWC_IME_RDCH_UAES_XTS_CFG_INPUT_FLOP 0


// Name:         DWC_IME_RDCH_UAES_XTS_CFG_OUTPUT_FLOP
// Default:      1 (DWC_IME_UAES_XTS_CFG_OUTPUT_FLOP)
// Values:       0, 1
// 
// This parameter provides the user the option to opt out of having internal datapath flops at the, 
// output of the Read Channel AES-XTS core, to support a particular latency sensitive application.
`define DWC_IME_RDCH_UAES_XTS_CFG_OUTPUT_FLOP 1


// Name:         DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP
// Default:      0
// Values:       0, 1
// 
// Defines whether the input TWK Gen has internal input flops. 
// A latency sensitive application may require you to disable these flops.
`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP 0


// Name:         DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP
// Default:      0
// Values:       0, 1
// 
// Defines whether the internal TWK Gen has internal output flops. 
// A latency sensitive application may require you to disable these flops.
`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP 0


`define DWC_IME_RDCH_UAES_XTS_CFG_LATENCY_OPTION 1


`define DWC_IME_RDCH_UAES_XTS_CFG_PIPE_BYPASS_LATENCY

//---------------------------------------------------------------------


`define DWC_IME_RDCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_DATA_UNIT_LEN 6


`define DWC_IME_RDCH_UAES_XTS_CFG_PRE_TWEAK_CNT 1


`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_ARCH 0


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_TWK_GEN_ARCH 0


`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GMULT_STAGES_GUI 1

//---------------------------------------------------------------------


`define DWC_IME_RDCH_UAES_XTS_CFG_SBOX_ARCH 0


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_INST_KEY_EXP_ARCH 1


// `define DWC_IME_RDCH_UAES_XTS_CFG_ENABLE_SW_DEC_INSTALL

//---------------------------------------------------------------------


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_IF_TYPE 0


// `define DWC_IME_RDCH_UAES_XTS_CFG_SKP_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_PASSTHRU_WIDTH 0


// `define DWC_IME_RDCH_UAES_XTS_CFG_HOST_CLK_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_SKP_CLK_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_MULTI_CLK_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_SYNC_DEPTH 2


// `define DWC_IME_RDCH_UAES_XTS_CFG_RST_ASYNC

//---------------------------------------------------------------------


// `define DWC_IME_RDCH_UAES_XTS_CFG_HW_INIT_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_NUM_CTX_GUI 1


`define DWC_IME_RDCH_UAES_XTS_CFG_NUM_TWK_CTX_GUI 32


`define DWC_IME_RDCH_UAES_XTS_CFG_SYNTH_CKEY_MEM


`define DWC_IME_RDCH_UAES_XTS_CFG_SYNTH_TKEY_MEM


`define DWC_IME_RDCH_UAES_XTS_CFG_SYNTH_TVAL_MEM


// `define DWC_IME_RDCH_UAES_XTS_CFG_SP_CKEY_MEM


// `define DWC_IME_RDCH_UAES_XTS_CFG_SP_TKEY_MEM


// `define DWC_IME_RDCH_UAES_XTS_CFG_SP_TVAL_MEM


`define DWC_IME_RDCH_UAES_XTS_CFG_MEM_WR_LATENCY 1


`define DWC_IME_RDCH_UAES_XTS_CFG_MEM_RD_LATENCY_GUI 1


//---------------------------------------------------------------------
// Some derived parameters


`define DWC_IME_RDCH_UAES_XTS_CFG_OUTPUT_FLOP_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_INPUT_FLOP_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_LATENCY_OPTION0


`define DWC_IME_RDCH_UAES_XTS_CFG_LATENCY_OPTION1


// `define DWC_IME_RDCH_UAES_XTS_CFG_LATENCY_OPTION2


`define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_1


`define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_2


// `define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_3


// `define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_4


// `define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_5


// `define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_6


// `define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_7


// `define DWC_IME_RDCH_UAES_XTS_CFG_MEM_TOTAL_LATENCY_GTE_8


`define DWC_IME_RDCH_UAES_XTS_CFG_DP_WIDTH 13'h100


`define DWC_IME_RDCH_UAES_XTS_CFG_DP_PIPE_NUM 13'h7


`define DWC_IME_RDCH_UAES_XTS_CFG_AES_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_SM4_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_AES_AND_SM4_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_ENC_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_DEC_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_ENC_ONLY_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_DEC_ONLY_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_ENC_AND_DEC_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY128_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY256_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_WIDTH 512


`define DWC_IME_RDCH_UAES_XTS_CFG_CIPHER_KEY_WIDTH 256


`define DWC_IME_RDCH_UAES_XTS_CFG_SK_ADDR_WIDTH 4


`define DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN_BIT 0


`define DWC_IME_RDCH_UAES_XTS_CFG_CTS_EN_BIT 0


`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_ARCH_10_14


// `define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_ARCH_5_7


// `define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_ARCH_2_2


// `define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_ARCH_1_1


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_TWK_GEN_ARCH_PIPELINED


// `define DWC_IME_RDCH_UAES_XTS_CFG_SM4_TWK_GEN_ARCH_ITERATED



// `define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR_HALF_OR_1


// `define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR_HALF


// `define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR1


// `define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR01


`define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR2


// `define DWC_IME_RDCH_UAES_XTS_CFG_PIPELINE_FACTOR4


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR_SAME_AS_AES


// `define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR1


// `define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR2


// `define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR4


// `define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPELINE_FACTOR8


`define DWC_IME_RDCH_UAES_XTS_CFG_BSEQ_WIDTH 2


// `define DWC_IME_RDCH_UAES_XTS_CFG_SINGLE_BLK_DATA_UNIT


`define DWC_IME_RDCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS 1


`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_GMULT_STAGES 2'h1


// `define DWC_IME_RDCH_UAES_XTS_CFG_SW_KEY_DEC_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_HW_KEY_DEC_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_IF_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_SKP_EN_BIT 0


// `define DWC_IME_RDCH_UAES_XTS_CFG_PASSTHRU_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_NUM_CTX 17'h1


`define DWC_IME_RDCH_UAES_XTS_CFG_NUM_TWK_CTX 17'h20


`define DWC_IME_RDCH_UAES_XTS_CFG_CTX_WIDTH 1


`define DWC_IME_RDCH_UAES_XTS_CFG_NUM_CTX_IS_POW2


//

`define DWC_IME_RDCH_UAES_XTS_CFG_TWK_CTX_WIDTH 5


`define DWC_IME_RDCH_UAES_XTS_CFG_NUM_TWK_CTX_IS_POW2


// `define DWC_IME_RDCH_UAES_XTS_CFG_CTX_IS_POW2


`define DWC_IME_RDCH_UAES_XTS_CFG_CKEY_ADDR_WIDTH 1


`define DWC_IME_RDCH_UAES_XTS_CFG_TKEY_ADDR_WIDTH 1


`define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_ADDR_WIDTH 5


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_INVALIDATE_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_INVALIDATE_ENA 1


`define DWC_IME_RDCH_UAES_XTS_CFG_KEY_MEM_DATA_WIDTH 258


`define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_MEM_DATA_WIDTH 128


`define DWC_IME_RDCH_UAES_XTS_CFG_TPRAM_USED 1


`define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_MEM0_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_MEM1_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_INT_TVAL_MEM1_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_MEM2_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_MEM3_EN


// `define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_SEQ_MEM_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_MEM_RD_LATENCY 3'h1


`define DWC_IME_RDCH_UAES_XTS_CFG_PASSTHRU_LATENCY 21


// Name:         DWC_IME_RDCH_UAES_XTS_CFG_CMD_DATA_DELAY
// Default:      2 (DWC_IME_RDCH_UAES_XTS_CFG_INPUT_FLOP + 
//               DWC_IME_RDCH_UAES_XTS_CFG_MEM_RD_LATENCY + ((DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN==0) ? 
//               DWC_IME_RDCH_UAES_XTS_CFG_TWK_GMULT_STAGES : 1))
// Values:       1, ..., 2147483647
// 
// Maximum acceptable time delay from command to data request on read channel. 
//  Data load can be received on the same cycle with command request, or delayed up to 
//  this number of cycles later than the command request.
`define DWC_IME_RDCH_UAES_XTS_CFG_CMD_DATA_DELAY 2


`define DWC_IME_RDCH_UAES_XTS_CFG_FIPS_SELF_TEST_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_FIPS_SELF_TEST_INT_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_AES_PIPE_NUM_DEPTH 7


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_PIPE_NUM_DEPTH 4


`define DWC_IME_RDCH_UAES_XTS_CFG_PIPE_NUM_DEPTH 7


`define DWC_IME_RDCH_UAES_XTS_CFG_CTS_IN_ORDER_CALC 0


`define DWC_IME_RDCH_UAES_XTS_CFG_AES_DP_PIPE_NUM_DEPTH 7


`define DWC_IME_RDCH_UAES_XTS_CFG_SM4_DP_PIPE_NUM_DEPTH 4


`define DWC_IME_RDCH_UAES_XTS_CFG_DP_PIPE_NUM_DEPTH 7


`define DWC_IME_RDCH_UAES_XTS_CFG_CTS_PIPE_NUM_DEPTH 7


// Name:         DWC_IME_RDCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN
// Default:      10 (DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP + 
//               DWC_IME_RDCH_UAES_XTS_CFG_MEM_RD_LATENCY + 
//               DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP + DWC_IME_RDCH_UAES_XTS_CFG_PIPE_NUM_DEPTH + (1 + 
//               DWC_IME_RDCH_UAES_XTS_CFG_MEM_WR_LATENCY))
// Values:       1, ..., (DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_OUTPUT_FLOP + 
//               DWC_IME_RDCH_UAES_XTS_CFG_MEM_RD_LATENCY + 
//               DWC_IME_RDCH_UAES_XTS_CFG_TWK_GEN_INPUT_FLOP + DWC_IME_RDCH_UAES_XTS_CFG_PIPE_NUM_DEPTH + (1 + 
//               DWC_IME_RDCH_UAES_XTS_CFG_MEM_WR_LATENCY))
// 
// AES-XTS Tweak Generation Latency for read channel.
`define DWC_IME_RDCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN 10



// Name:         DWC_IME_RDCH_TWKGEN_LATENCY
// Default:      11 (DWC_IME_RDCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN + 
//               DWC_IME_TWKGEN_INPUT_FLOP)
// Values:       1, ..., (DWC_IME_RDCH_UAES_XTS_CFG_MIN_TWK_PRECOMP_WIN + 
//               DWC_IME_TWKGEN_INPUT_FLOP)
// 
// IME Tweak Generation Latency for read channel.
`define DWC_IME_RDCH_TWKGEN_LATENCY 11


`define DWC_IME_RDCH_UAES_XTS_CFG_PIPE_NUM_WIDTH 1


// `define DWC_IME_RDCH_UAES_XTS_CFG_RST_PCLK_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_RST_PCLK_EN_BIT 0


// `define DWC_IME_RDCH_UAES_XTS_CFG_RST_SKP_EN


`define DWC_IME_RDCH_UAES_XTS_CFG_RST_SKP_EN_BIT 0


// Name:         DWC_IME_RDCH_UAES_XTS_VER_NUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Version field.
`define DWC_IME_RDCH_UAES_XTS_VER_NUM_VAL 16'h0


// Name:         DWC_IME_RDCH_UAES_XTS_TYPE_NUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Type field.
`define DWC_IME_RDCH_UAES_XTS_TYPE_NUM_VAL 8'h0


// Name:         DWC_IME_RDCH_UAES_XTS_PKG_NUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Package field.
`define DWC_IME_RDCH_UAES_XTS_PKG_NUM_VAL 4'h0


// Name:         DWC_IME_RDCH_UAES_XTS_TYPE_ENUM_VAL
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// 
// This parameter defines the Core Type enumerated field.
`define DWC_IME_RDCH_UAES_XTS_TYPE_ENUM_VAL 4'h0


// `define DWC_IME_RDCH_UAES_XTS_CFG_APB4


// `define DWC_IME_RDCH_UAES_XTS_CFG_APB5


`define DWC_IME_AES_PIPELINE_LATENCY 7


`define DWC_IME_SM4_PIPELINE_LATENCY 4


`define DWC_IME_WRCH_PIPELINE_LATENCY 8


// Name:         DWC_IME_WRCH_PASSTHRU_LATENCY
// Default:      9 (DWC_IME_INPUT_FLOP + DWC_IME_WRCH_PIPELINE_LATENCY + 
//               DWC_IME_OUTPUT_FLOP + DWC_IME_BREAK_REGION_SEL_PATH)
// Values:       -2147483648, ..., 2147483647
// 
// Encryption Latency for write channel.
`define DWC_IME_WRCH_PASSTHRU_LATENCY 9


`define DWC_IME_WRCH_SHORT_PIPELINE_LATENCY 6


`define DWC_IME_RDCH_PIPELINE_LATENCY 8


// Name:         DWC_IME_RDCH_PASSTHRU_LATENCY
// Default:      9 (DWC_IME_INPUT_FLOP + DWC_IME_RDCH_PIPELINE_LATENCY + 
//               DWC_IME_OUTPUT_FLOP + DWC_IME_BREAK_REGION_SEL_PATH)
// Values:       -2147483648, ..., 2147483647
// 
// Encryption Latency for read channel.
`define DWC_IME_RDCH_PASSTHRU_LATENCY 9


`define DWC_IME_RDCH_SHORT_PIPELINE_LATENCY 6


// Name:         DWC_IME_FASTBYPASS_LATENCY
// Default:      2 (1+ DWC_IME_INPUT_FLOP + DWC_IME_OUTPUT_FLOP + 
//               DWC_IME_BREAK_REGION_SEL_PATH)
// Values:       -2147483648, ..., 2147483647
// 
// Fast-bypass latency.
`define DWC_IME_FASTBYPASS_LATENCY 2
//---------------------------------------------------------------------
//parameters related to SRAM calculation
//----------------------------------------------------------------------

`define DWC_IME_WRCH_UAES_XTS_TKEY_ECC_WIDTH_INFO 0


`define DWC_IME_RDCH_UAES_XTS_TKEY_ECC_WIDTH_INFO 0



`define DWC_IME_WRCH_UAES_XTS_CKEY_ECC_WIDTH_INFO 0


`define DWC_IME_RDCH_UAES_XTS_CKEY_ECC_WIDTH_INFO 0


`define DWC_IME_WRCH_UAES_XTS_TVAL_ECC_WIDTH_INFO 0


`define DWC_IME_RDCH_UAES_XTS_TVAL_ECC_WIDTH_INFO 0


`define DWC_IME_WRCH_UAES_XTS_TKEY_ECC_POISON_POS_WIDTH_INFO 0


`define DWC_IME_RDCH_UAES_XTS_TKEY_ECC_POISON_POS_WIDTH_INFO 0



`define DWC_IME_WRCH_UAES_XTS_CKEY_ECC_POISON_POS_WIDTH_INFO 0


`define DWC_IME_RDCH_UAES_XTS_CKEY_ECC_POISON_POS_WIDTH_INFO 0


`define DWC_IME_WRCH_UAES_XTS_TVAL_ECC_POISON_POS_WIDTH_INFO 0


`define DWC_IME_RDCH_UAES_XTS_TVAL_ECC_POISON_POS_WIDTH_INFO 0


// Name:         DWC_IME_WRCH_UAES_XTS_TKEY_SRAM_WIDTH_INFO
// Default:      0 ((DWC_IME_SYNTH_TKEY_MEM == 1) ? 0 : 
//               (DWC_IME_WRCH_UAES_XTS_CFG_KEY_MEM_DATA_WIDTH + DWC_IME_WRCH_UAES_XTS_TKEY_ECC_WIDTH_INFO))
// Values:       0, ..., 512
// Enabled:      ((DWC_IME_ECB_ENGINE==1) == 0 )
// 
// The width of the write channel tweak key memory for AES XTS core in (bits). 
// This value is always equal for write and read channel.
`define DWC_IME_WRCH_UAES_XTS_TKEY_SRAM_WIDTH_INFO 0


// Name:         DWC_IME_WRCH_UAES_XTS_TKEY_SRAM_DEPTH_INFO
// Default:      0 ((DWC_IME_SYNTH_TKEY_MEM == 1) ? 0 : DWC_IME_NUM_KEYS)
// Values:       0, ..., 1024
// Enabled:      ((DWC_IME_ECB_ENGINE==1) == 0 )
// 
// The depth of the write channel tweak key memory for AES XTS core in (rows). 
// This value is always equal for write and read channel.
`define DWC_IME_WRCH_UAES_XTS_TKEY_SRAM_DEPTH_INFO 0


// Name:         DWC_IME_WRCH_UAES_XTS_CKEY_SRAM_WIDTH_INFO
// Default:      0 ((DWC_IME_SYNTH_CKEY_MEM == 1) ? 0 : 
//               (DWC_IME_WRCH_UAES_XTS_CFG_KEY_MEM_DATA_WIDTH + DWC_IME_WRCH_UAES_XTS_CKEY_ECC_WIDTH_INFO))
// Values:       0, ..., 512
// 
// The width of the write channel cipher key memory for AES XTS core in (bits). 
// This value is always equal for write and read channel.
`define DWC_IME_WRCH_UAES_XTS_CKEY_SRAM_WIDTH_INFO 0


// Name:         DWC_IME_WRCH_UAES_XTS_CKEY_SRAM_DEPTH_INFO
// Default:      0 ((DWC_IME_SYNTH_CKEY_MEM == 1) ? 0 : DWC_IME_NUM_KEYS)
// Values:       0, ..., 1024
// 
// The depth of the write channel cipher key memory for AES XTS core in (rows). 
// This value is always equal for write and read channel.
`define DWC_IME_WRCH_UAES_XTS_CKEY_SRAM_DEPTH_INFO 0


// Name:         DWC_IME_RDCH_UAES_XTS_TKEY_SRAM_WIDTH_INFO
// Default:      0 ((DWC_IME_SYNTH_TKEY_MEM == 1) ? 0 : 
//               (DWC_IME_RDCH_UAES_XTS_CFG_KEY_MEM_DATA_WIDTH + DWC_IME_RDCH_UAES_XTS_TKEY_ECC_WIDTH_INFO))
// Values:       0, ..., 512
// Enabled:      ((DWC_IME_ECB_ENGINE==1) == 0 )
// 
// The width of the read channel tweak key memory for AES XTS core in (bits). 
// This value is always equal for write and read channel.
`define DWC_IME_RDCH_UAES_XTS_TKEY_SRAM_WIDTH_INFO 0


// Name:         DWC_IME_RDCH_UAES_XTS_TKEY_SRAM_DEPTH_INFO
// Default:      0 ((DWC_IME_SYNTH_TKEY_MEM == 1) ? 0 : DWC_IME_NUM_KEYS)
// Values:       0, ..., 1024
// Enabled:      ((DWC_IME_ECB_ENGINE==1) == 0 )
// 
// The depth of the read channel tweak key memory for AES XTS core in (rows). 
// This value is always equal for write and read channel.
`define DWC_IME_RDCH_UAES_XTS_TKEY_SRAM_DEPTH_INFO 0


// Name:         DWC_IME_RDCH_UAES_XTS_CKEY_SRAM_WIDTH_INFO
// Default:      0 ((DWC_IME_SYNTH_CKEY_MEM == 1) ? 0 : 
//               (DWC_IME_RDCH_UAES_XTS_CFG_KEY_MEM_DATA_WIDTH + DWC_IME_RDCH_UAES_XTS_CKEY_ECC_WIDTH_INFO))
// Values:       0, ..., 512
// 
// The width of the read channel cipher key memory for AES XTS core in (bits). 
// This value is always equal for write and read channel.
`define DWC_IME_RDCH_UAES_XTS_CKEY_SRAM_WIDTH_INFO 0


// Name:         DWC_IME_RDCH_UAES_XTS_CKEY_SRAM_DEPTH_INFO
// Default:      0 ((DWC_IME_SYNTH_CKEY_MEM == 1) ? 0 : DWC_IME_NUM_KEYS)
// Values:       0, ..., 1024
// 
// The depth of the read channel cipher key memory for AES XTS core in (rows). 
// This value is always equal for write and read channel.
`define DWC_IME_RDCH_UAES_XTS_CKEY_SRAM_DEPTH_INFO 0


// Name:         DWC_IME_WRCH_UAES_XTS_TVAL_SRAM_WIDTH_INFO
// Default:      0 ((DWC_IME_WRCH_UAES_XTS_CFG_SYNTH_TVAL_MEM == 1) ? 0 : 
//               (DWC_IME_WRCH_UAES_XTS_CFG_TVAL_MEM_DATA_WIDTH  + 
//               DWC_IME_WRCH_UAES_XTS_TVAL_ECC_WIDTH_INFO))
// Values:       0, ..., 512
// Enabled:      ((DWC_IME_ECB_EN)==0)
// 
// The width of the write channel tweak value memory for AES XTS core in (bits).
`define DWC_IME_WRCH_UAES_XTS_TVAL_SRAM_WIDTH_INFO 0


// Name:         DWC_IME_WRCH_UAES_XTS_TVAL_SRAM_DEPTH_INFO
// Default:      0 ((DWC_IME_WRCH_UAES_XTS_CFG_SYNTH_TVAL_MEM == 1) ? 0 : 
//               DWC_IME_WRCH_UAES_XTS_CFG_NUM_TWK_CTX_GUI)
// Values:       0, ..., 128
// Enabled:      ((DWC_IME_ECB_EN)==0)
// 
// The depth of the write channel tweak value memory for AES XTS core in (rows).
`define DWC_IME_WRCH_UAES_XTS_TVAL_SRAM_DEPTH_INFO 0


// Name:         DWC_IME_RDCH_UAES_XTS_TVAL_SRAM_WIDTH_INFO
// Default:      0 ((DWC_IME_RDCH_UAES_XTS_CFG_SYNTH_TVAL_MEM == 1) ? 0 : 
//               (DWC_IME_RDCH_UAES_XTS_CFG_TVAL_MEM_DATA_WIDTH + 
//               DWC_IME_RDCH_UAES_XTS_TVAL_ECC_WIDTH_INFO))
// Values:       0, ..., 512
// Enabled:      ((DWC_IME_ECB_EN)==0)
// 
// The width of the read channel tweak value memory for AES XTS core in (bits).
`define DWC_IME_RDCH_UAES_XTS_TVAL_SRAM_WIDTH_INFO 0


// Name:         DWC_IME_RDCH_UAES_XTS_TVAL_SRAM_DEPTH_INFO
// Default:      0 ((DWC_IME_RDCH_UAES_XTS_CFG_SYNTH_TVAL_MEM == 1) ? 0 : 
//               DWC_IME_RDCH_UAES_XTS_CFG_NUM_TWK_CTX_GUI)
// Values:       0, ..., 128
// Enabled:      ((DWC_IME_ECB_EN)==0)
// 
// The depth of the read channel tweak value memory for AES XTS core in (rows).
`define DWC_IME_RDCH_UAES_XTS_TVAL_SRAM_DEPTH_INFO 0


`define DWC_IME_WRCH_UAES_XTS_CFG_TKEY_SRAM_DATA_WIDTH 0


`define DWC_IME_RDCH_UAES_XTS_CFG_TKEY_SRAM_DATA_WIDTH 0


`define DWC_IME_WRCH_UAES_XTS_CFG_CKEY_SRAM_DATA_WIDTH 0


`define DWC_IME_RDCH_UAES_XTS_CFG_CKEY_SRAM_DATA_WIDTH 0


`define DWC_IME_WRCH_UAES_XTS_CFG_TVAL_SRAM_DATA_WIDTH 0


`define DWC_IME_RDCH_UAES_XTS_CFG_TVAL_SRAM_DATA_WIDTH 0


//==============================================================================
// End Guard
//==============================================================================
`endif // __GUARD__DWC_IME_CC_CONSTANTS__SVH__
