
/** \file
 * \brief Structures and enumeration definitions
 */
#ifndef _DWC_DDRPHY_PHYINIT_USERCUSTOM_H_
#define _DWC_DDRPHY_PHYINIT_USERCUSTOM_H_

#include <stdint.h>

//-------------------------------------------------------------
// Defines for max number of PStates
//-------------------------------------------------------------
/*! \def DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE
 * \brief Max number of allowed PStates for this product.
 */
#define DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE 4
#define DWC_DDRPHY_PHYINIT_HW_NUM_PSTATE 4

#define DWC_DDRPHY_PHYINIT_MAX_NUM_RANK 4
#if defined(_BUILD_LPDDR5) || defined(_BUILD_LPDDR4)
/*! \def NUM_HMAC_PER_CHAN
 * \brief Number of HMAC instances per channel in the PHY.
 */
#define NUM_HMAC_PER_CHAN 7
#endif

#include <dwc_ddrphy_phyinit_struct.h>

//-------------------------------------------------------------
// Defines for PState Mode Registers stored in ACSM SRAM
//-------------------------------------------------------------
/*! \def DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP4
 * \brief Number of rows for broadcasted Mode Registers restored on a PState change.
 */
#define DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP4 28

/*! \def DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP5
 * \brief Number of rows for broadcasted Mode Registers restored on a PState change.
 */
#define DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP5 48

/*! \def DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP4
 * \brief Number of rows for trained Mode Registers restored on a PState change.
 */
#define DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP4 10

/*! \def DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP5
 * \brief Number of rows for trained Mode Registers restored on a PState change.
 */
#define DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP5 42

/*! \def ACSM_NOP_ROW_OFFSET
 * \brief The first two rows of ACSM are NOP
 */
#define ACSM_NOP_ROW_OFFSET 0x2

//-------------------------------------------------------------
// Defines for Firmware Images
// - point to IMEM/DMEM incv files,
// - indicate IMEM/DMEM size (bytes)
//-------------------------------------------------------------
/*! \def FW_FILES_LOC
 * \brief set the location of training firmware uncompressed path.
 *
 * PhyInit will use this path to load the imem and dmem incv files of the
 * firmware image.
 */
/*! \def IMEM_INCV_FILENAME
 * \brief firmware instruction memory (imem) filename for 1D training
 */
/*! \def DMEM_INCV_FILENAME
 * \brief firmware instruction memory (imem) filename for 1D training.
 */
/*! \def IMEM_SIZE
 * \brief max size of instruction memory.
 */
/*! \def DMEM_SIZE
 * \brief max size of data memory.
 */
/*! \def DMEM_ST_ADDR
 * \brief start of DMEM address in memory.
 */
/*! \def IMEM_ST_ADDR
 * \brief start of IMEM address in memory.
 */
#ifndef FW_FILES_LOC
#define FW_FILES_LOC "./fw"
#endif

#ifndef IMEM_INCV_FILENAME
#define IMEM_INCV_FILENAME FW_FILES_LOC"/lpddr5x/lpddr5x_pmu_train_imem.incv"
#endif // IMEM_INCV_FILENAME

#ifndef DMEM_INCV_FILENAME
#define DMEM_INCV_FILENAME FW_FILES_LOC"/lpddr5x/lpddr5x_pmu_train_dmem.incv"
#endif // DMEM_INCV_FILENAME

#define IMEM_SIZE 1024*128 // 96KB (32 bits x 24K words)
#define DMEM_SIZE 1024*160 // 96KB (32 bits x 24K words)
#define DMEM_ST_ADDR 0x58000
#define IMEM_ST_ADDR 0x50000

/*! \def DWC_DDRPHY_NUM_PHY
 * \brief Multiple PHY interface.
 */
#ifndef DWC_DDRPHY_NUM_PHY
#define DWC_DDRPHY_NUM_PHY (1)
#endif
//-------------------------------------------------------------
// Defines for SR Firmware Images
// - point to IMEM incv files,
// - indicate IMEM size (bytes)
//-------------------------------------------------------------
/*! \def SR_FW_FILES_LOC
 * \brief location of optional retention save restore firmware image.
 */
/*! \def SR_IMEM_SIZE
 * \brief max IMEM size of retention save/restore firmware.
 */
/*! \def SR_IMEM_INCV_FILENAME
 * \brief file name of retention save/restore IMEM image.
 */
#ifndef SR_FW_FILES_LOC
#define SR_FW_FILES_LOC FW_FILES_LOC"/save_restore"
#endif

#define SR_IMEM_SIZE 128*1024
#define SR_IMEM_INCV_FILENAME       SR_FW_FILES_LOC"/dwc_ddrphy_io_retention_save_restore_imem.incv"

//-------------------------------------------------------------
// Defines for ACSM CSR Address
//-------------------------------------------------------------
/*! \def ACSM_START_CSR_ADDR
 * \brief Starting CSR address of ACSM SRAM
 */
#define ACSM_START_CSR_ADDR (0x41000u)
#define ACSM_CSR_ADDR_SIZE  (0xfffu)

//-------------------------------------------------------------
// Defines for ACSM markers for PHYINIT to adjust ACSM SRAM
//-------------------------------------------------------------
/*! \def DWC_DDRPHY_PHYINIT_NUM_ACSM_MARKERS
 * \brief Number of ACSM markers for ACSM instruction adjustment
 */
#define DWC_DDRPHY_PHYINIT_NUM_ACSM_MARKERS 68


/*! \def DWC_DDRPHY_PHYINIT_{UDR,MDR,LDR}_ACSM_MRKR_{4,2}to1_{RXCLK_TXDQ1,TXDQ2}_TG{0,1}_{MRW,WFF,RDD}
 * \brief Array offsets for phyinit_config_t.AcsmMrkrCnt[] array
 */
// Note: that the order of the defines must match the way the ACSM code is generated
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF     0
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF     1
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF     2
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF     3
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG0_RDC            4
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG1_RDC            5
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW           6
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF           7
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF           8
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS           9
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW           10
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF           11
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF           12
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS           13

#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF     14
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF     15
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF     16
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF     17
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG0_RDC            18
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG1_RDC            19
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW           20
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF           21
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF           22
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS           23
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW           24
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF           25
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF           26
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS           27

#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF     28
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF     29
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF     30
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF     31
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG0_RDC            32
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG1_RDC            33

#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF     34
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF     35
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF     36
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF     37
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG0_RDC            38
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG1_RDC            39
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW           40
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF           41
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF           42
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS           43
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW           44
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF           45
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF           46
#define DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS           47

#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF     48
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF     49
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF     50
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF     51
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG0_RDC            52
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG1_RDC            53
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW           54
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF           55
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF           56
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS           57
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW           58
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF           59
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF           60
#define DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS           61

#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF     62
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF     63
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF     64
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF     65
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG0_RDC            66
#define DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG1_RDC            67




/**
*	The following defines are being used to indicate when the bits of Seq0bGPR1 are set or reset
*	Also, there are defines for the lower and upper limit for datarates used for PClkDCA Calibration
*
*/
#define DWC_DDRPHY_PHYINIT_EDVFSC_EN_MIN_THRESHOLD         40u
#define DWC_DDRPHY_PHYINIT_PCLKDCA_EN_THRESHOLD			   3200u
#define DWC_DDRPHY_PHYINIT_ENHANCED_DVFSC_EN_MAX_THRESHOLD 3200u

#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET                 0x0000u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT0_SET              0X0001u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT1_SET              0X0002u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT2_SET              0X0004u	
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT3_SET              0X0008u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT4_SET              0X0010u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT5_SET              0X0020u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT6_SET              0X0040u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT7_SET              0X0080u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT8_SET              0X0100u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT9_SET              0X0200u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT10_SET             0X0400u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT11_SET             0X0800u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT12_SET             0X1000u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT13_SET             0X2000u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT14_SET             0X4000u
#define DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT15_SET             0X8000u

//Defines used for setting PLL csr values
#define DWC_DDRPHY_PHYINIT_PLL_MAX_ROWS  					50
#define DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT 	256
#define DWC_DDRPHY_PHYINIT_PLL_MAX_COLUMN_COUNT 			9
#define DWC_DDRPHY_PHYINIT_PLL_SETTINGS_CHARACTER_LENGTH	512

//-------------------------------------------------------------
// Defines for CSR addresses that may not be defined in some cases
//-------------------------------------------------------------
#ifndef csr_NeverGateACDlyScaleValClk_ADDR
#define csr_NeverGateACDlyScaleValClk_ADDR 0x3fu // 000_tttt_cccc_0000_0011_1111 {HMAC}
#endif

#ifndef csr_RxClkSeMode_ADDR
#define csr_RxClkSeMode_ADDR 0xee // ppp_tttt_cccc_0000_1110_1110 {HMDBYTE,HMDBYTE4} 
#endif

//-------------------------------------------------------------
// Message Block Structure Definitions.
#ifndef MSG_BLOCK_H
#define MSG_BLOCK_H "mnPmuSramMsgBlock_lpddr5x.h"
#endif // MSG_BLOCK_H 

#include MSG_BLOCK_H


//------------------
// Type definitions
//------------------

/// A structure used to SRAM memory address space.
typedef enum { return_offset, return_lastaddr } return_offset_lastaddr_t;

/// enumeration of instructions for PhyInit Register Interface
typedef enum {
	startTrack,					///< Start register tracking
	stopTrack,					///< Stop register tracking
	saveRegs,					///< Save (read) tracked register values
	restoreRegs,				///< Restore (write) saved register values
	dumpRegs,					///< Write register address,value pairs to file
	importRegs,					///< Import register address,value pairs to file
} regInstr;

/// enumeration of DfiMode CSR enable/disable
typedef enum {
	enableDfiMode,				///< Enable DFI0 and DFI1 in CSR DfiMode
	disableDfiMode				///< Program DFI0 and DFI1 based on userInput in CSR DfiMode
} dfiMode_t;

/// enumeration of D5DbyteMiscMode and PubDbytedisable CSR
typedef enum {
	setDbyteDisable,				///< Program csr based on userInput
	resetDbyteDisable				///< Program csr based on its default value
} dbytedisable_t;

/// enumeration of user input fields of PhyInit
typedef enum {
	// pRuntimeConfig Fields:
	_NumAchnActive_, // 0
	_firstTrainedPState_, // 1
	_DataRateMbps_0__, // 2
	_DataRateMbps_1__, // 3
	_DataRateMbps_2__, // 4
	_DataRateMbps_3__, // 5
	_psExecOrder_0__, // 6
	_psExecOrder_1__, // 7
	_psExecOrder_2__, // 8
	_psExecOrder_3__, // 9
	_NumDbyteActive_, // 10
	_enableBits_0__, // 11
	_enableBits_1__, // 12
	_enableBits_2__, // 13
	_NumDxOutPipeEn_0__, // 14
	_NumDxOutPipeEn_1__, // 15
	_NumDxOutPipeEn_2__, // 16
	_NumDxOutPipeEn_3__, // 17
	_NumDxInPipeEn_0__, // 18
	_NumDxInPipeEn_1__, // 19
	_NumDxInPipeEn_2__, // 20
	_NumDxInPipeEn_3__, // 21
	_NumMiscPipeEn_0__, // 22
	_NumMiscPipeEn_1__, // 23
	_NumMiscPipeEn_2__, // 24
	_NumMiscPipeEn_3__, // 25
	_NumDbyte_, // 26
	_skip_train_, // 27
	_initCtrl_, // 28
	_TG_active_0__, // 29
	_TG_active_1__, // 30
	_TG_active_2__, // 31
	_TG_active_3__, // 32
	_NumAcInPipeEn_0__, // 33
	_NumAcInPipeEn_1__, // 34
	_NumAcInPipeEn_2__, // 35
	_NumAcInPipeEn_3__, // 36
	_UcclkFull_0__, // 37
	_UcclkFull_1__, // 38
	_UcclkFull_2__, // 39
	_UcclkFull_3__, // 40
	_DfiFreq_0__, // 41
	_DfiFreq_1__, // 42
	_DfiFreq_2__, // 43
	_DfiFreq_3__, // 44
	_Train2D_, // 45
	_tck_ps_0__, // 46
	_tck_ps_1__, // 47
	_tck_ps_2__, // 48
	_tck_ps_3__, // 49
	_NumAlertNPipeEn_0__, // 50
	_NumAlertNPipeEn_1__, // 51
	_NumAlertNPipeEn_2__, // 52
	_NumAlertNPipeEn_3__, // 53
	_pubRev_, // 54
	_debug_, // 55
	_curD_, // 56
	_lastTrainedPState_, // 57
	_RetEn_, // 58
	_curPState_, // 59
	// pUserInputAdvanced Fields:
	_CalImpedanceCurrentAdjustment_, // 60
	_CalOnce_, // 61
	_DMEMLoadPerfEn_, // 62
	_TxSlewRiseCA_0__, // 63
	_TxSlewRiseCA_1__, // 64
	_TxSlewRiseCA_2__, // 65
	_TxSlewRiseCA_3__, // 66
	_RxGainCtrl_, // 67
	_DramStateChangeEn_, // 68
	_TxSlewFallCK_0__, // 69
	_TxSlewFallCK_1__, // 70
	_TxSlewFallCK_2__, // 71
	_TxSlewFallCK_3__, // 72
	_OdtImpedanceCk_0__, // 73
	_OdtImpedanceCk_1__, // 74
	_OdtImpedanceCk_2__, // 75
	_OdtImpedanceCk_3__, // 76
	_Lp5xDeassertDramReset_, // 77
	_OdtImpedanceWCK_0__, // 78
	_OdtImpedanceWCK_1__, // 79
	_OdtImpedanceWCK_2__, // 80
	_OdtImpedanceWCK_3__, // 81
	_EnWck2DqoTracking_0__, // 82
	_EnWck2DqoTracking_1__, // 83
	_EnWck2DqoTracking_2__, // 84
	_EnWck2DqoTracking_3__, // 85
	_AcInPipeEnOvr_, // 86
	_DtoEnable_, // 87
	_CkDisVal_0__, // 88
	_CkDisVal_1__, // 89
	_CkDisVal_2__, // 90
	_CkDisVal_3__, // 91
	_DxRdPipeEnOvr_, // 92
	_EnLpRxDqPowerDown_, // 93
	_TxSlewFallDq_0__, // 94
	_TxSlewFallDq_1__, // 95
	_TxSlewFallDq_2__, // 96
	_TxSlewFallDq_3__, // 97
	_TxImpedanceAc_0__, // 98
	_TxImpedanceAc_1__, // 99
	_TxImpedanceAc_2__, // 100
	_TxImpedanceAc_3__, // 101
	_CalInterval_, // 102
	_DisableRetraining_, // 103
	_TxImpedanceCk_0__, // 104
	_TxImpedanceCk_1__, // 105
	_TxImpedanceCk_2__, // 106
	_TxImpedanceCk_3__, // 107
	_DLEPKeyCode_, // 108
	_DxInPipeEn_0__, // 109
	_DxInPipeEn_1__, // 110
	_DxInPipeEn_2__, // 111
	_DxInPipeEn_3__, // 112
	_EnableSystemEcc_, // 113
	_PHYZCalPowerSaving_, // 114
	_PhyMstrTrainInterval_0__, // 115
	_PhyMstrTrainInterval_1__, // 116
	_PhyMstrTrainInterval_2__, // 117
	_PhyMstrTrainInterval_3__, // 118
	_DxOutPipeEn_0__, // 119
	_DxOutPipeEn_1__, // 120
	_DxOutPipeEn_2__, // 121
	_DxOutPipeEn_3__, // 122
	_DisableFspOp_, // 123
	_DfiLpPipeClkDisable_, // 124
	_DisablePclkDca_, // 125
	_RxDqsTrackingThreshold_0__, // 126
	_RxDqsTrackingThreshold_1__, // 127
	_RxDqsTrackingThreshold_2__, // 128
	_RxDqsTrackingThreshold_3__, // 129
	_TxImpedanceWCK_0__, // 130
	_TxImpedanceWCK_1__, // 131
	_TxImpedanceWCK_2__, // 132
	_TxImpedanceWCK_3__, // 133
	_OdtImpedanceDqs_0__, // 134
	_OdtImpedanceDqs_1__, // 135
	_OdtImpedanceDqs_2__, // 136
	_OdtImpedanceDqs_3__, // 137
	_AlertNPipeEn_0__, // 138
	_AlertNPipeEn_1__, // 139
	_AlertNPipeEn_2__, // 140
	_AlertNPipeEn_3__, // 141
	_SkipFlashCopy_0__, // 142
	_SkipFlashCopy_1__, // 143
	_SkipFlashCopy_2__, // 144
	_SkipFlashCopy_3__, // 145
	_DxRdPipeEn_0__, // 146
	_DxRdPipeEn_1__, // 147
	_DxRdPipeEn_2__, // 148
	_DxRdPipeEn_3__, // 149
	_Lp5xFwTinit3WaitTimex1000_, // 150
	_DisCheckAllUserInputsLegalVal_, // 151
	_SnoopWAEn_0__, // 152
	_SnoopWAEn_1__, // 153
	_SnoopWAEn_2__, // 154
	_SnoopWAEn_3__, // 155
	_ACDlyScaleGating_, // 156
	_TxSlewRiseDq_0__, // 157
	_TxSlewRiseDq_1__, // 158
	_TxSlewRiseDq_2__, // 159
	_TxSlewRiseDq_3__, // 160
	_IMEMLoadPerfEn_, // 161
	_AcInPipeEn_0__, // 162
	_AcInPipeEn_1__, // 163
	_AcInPipeEn_2__, // 164
	_AcInPipeEn_3__, // 165
	_DisCheckImpTxRx_0__, // 166
	_DisCheckImpTxRx_1__, // 167
	_DisCheckImpTxRx_2__, // 168
	_DisCheckImpTxRx_3__, // 169
	_AcQuarterDataRate_, // 170
	_DisCheckDvfsqDramOdt_0__, // 171
	_DisCheckDvfsqDramOdt_1__, // 172
	_DisCheckDvfsqDramOdt_2__, // 173
	_DisCheckDvfsqDramOdt_3__, // 174
	_ZcalClkDiv_0__, // 175
	_ZcalClkDiv_1__, // 176
	_ZcalClkDiv_2__, // 177
	_ZcalClkDiv_3__, // 178
	_OdtImpedanceCa_0__, // 179
	_OdtImpedanceCa_1__, // 180
	_OdtImpedanceCa_2__, // 181
	_OdtImpedanceCa_3__, // 182
	_RxBiasCurrentControlWck_0__, // 183
	_RxBiasCurrentControlWck_1__, // 184
	_RxBiasCurrentControlWck_2__, // 185
	_RxBiasCurrentControlWck_3__, // 186
	_PhyMstrMaxReqToAck_0__, // 187
	_PhyMstrMaxReqToAck_1__, // 188
	_PhyMstrMaxReqToAck_2__, // 189
	_PhyMstrMaxReqToAck_3__, // 190
	_TxSlewRiseCK_0__, // 191
	_TxSlewRiseCK_1__, // 192
	_TxSlewRiseCK_2__, // 193
	_TxSlewRiseCK_3__, // 194
	_DramByteSwap_, // 195
	_DisZCalOnDataRate_, // 196
	_RxClkTrackEn_0__, // 197
	_RxClkTrackEn_1__, // 198
	_RxClkTrackEn_2__, // 199
	_RxClkTrackEn_3__, // 200
	_OdtImpedanceDq_0__, // 201
	_OdtImpedanceDq_1__, // 202
	_OdtImpedanceDq_2__, // 203
	_OdtImpedanceDq_3__, // 204
	_CoreVddScalingMode_0__, // 205
	_CoreVddScalingMode_1__, // 206
	_CoreVddScalingMode_2__, // 207
	_CoreVddScalingMode_3__, // 208
	_RxDFECtrlDq_0__, // 209
	_RxDFECtrlDq_1__, // 210
	_RxDFECtrlDq_2__, // 211
	_RxDFECtrlDq_3__, // 212
	_DxInPipeEnOvr_, // 213
	_TxSlewFallCS_0__, // 214
	_TxSlewFallCS_1__, // 215
	_TxSlewFallCS_2__, // 216
	_TxSlewFallCS_3__, // 217
	_AlertNPipeEnOvr_, // 218
	_SkipPwrDnInRetrain_, // 219
	_TxSlewFallCA_0__, // 220
	_TxSlewFallCA_1__, // 221
	_TxSlewFallCA_2__, // 222
	_TxSlewFallCA_3__, // 223
	_DqsOscRunTimeSel_0__, // 224
	_DqsOscRunTimeSel_1__, // 225
	_DqsOscRunTimeSel_2__, // 226
	_DqsOscRunTimeSel_3__, // 227
	_RxBiasCurrentControlRxReplica_0__, // 228
	_RxBiasCurrentControlRxReplica_1__, // 229
	_RxBiasCurrentControlRxReplica_2__, // 230
	_RxBiasCurrentControlRxReplica_3__, // 231
	_Lp3DramState_0__, // 232
	_Lp3DramState_1__, // 233
	_Lp3DramState_2__, // 234
	_Lp3DramState_3__, // 235
	_TxSlewRiseCS_0__, // 236
	_TxSlewRiseCS_1__, // 237
	_TxSlewRiseCS_2__, // 238
	_TxSlewRiseCS_3__, // 239
	_UseSnpsController_, // 240
	_DisRxClkCLcdl_0__, // 241
	_DisRxClkCLcdl_1__, // 242
	_DisRxClkCLcdl_2__, // 243
	_DisRxClkCLcdl_3__, // 244
	_TxImpedanceDq_0__, // 245
	_TxImpedanceDq_1__, // 246
	_TxImpedanceDq_2__, // 247
	_TxImpedanceDq_3__, // 248
	_DisablePhyUpdate_, // 249
	_HalfTxCalCode_, // 250
	_DxOutPipeEnOvr_, // 251
	_RetrainMode_0__, // 252
	_RetrainMode_1__, // 253
	_RetrainMode_2__, // 254
	_RetrainMode_3__, // 255
	_DfiLoopbackEn_, // 256
	_DisablePmuEcc_, // 257
	_TxImpedanceDqs_0__, // 258
	_TxImpedanceDqs_1__, // 259
	_TxImpedanceDqs_2__, // 260
	_TxImpedanceDqs_3__, // 261
	_TrainSequenceCtrl_0__, // 262
	_TrainSequenceCtrl_1__, // 263
	_TrainSequenceCtrl_2__, // 264
	_TrainSequenceCtrl_3__, // 265
	_PmuClockDiv_0__, // 266
	_PmuClockDiv_1__, // 267
	_PmuClockDiv_2__, // 268
	_PmuClockDiv_3__, // 269
	_DqsSampNegRxEnSense_0__, // 270
	_DqsSampNegRxEnSense_1__, // 271
	_DqsSampNegRxEnSense_2__, // 272
	_DqsSampNegRxEnSense_3__, // 273
	_TxImpedanceCsCke_, // 274
	// pUserInputBasic Fields:
	_NumPStates_, // 275
	_NumRank_dfi0_, // 276
	_HardMacroVer_, // 277
	_NumCh_, // 278
	_DimmType_, // 279
	_Lp5xMode_, // 280
	_DramType_, // 281
	_DfiFreqRatio_0__, // 282
	_DfiFreqRatio_1__, // 283
	_DfiFreqRatio_2__, // 284
	_DfiFreqRatio_3__, // 285
	_FirstPState_, // 286
	_NumActiveDbyteDfi1_, // 287
	_NumRank_, // 288
	_DramDataWidth_, // 289
	_CfgPStates_, // 290
	_PclkPtrInitValOvr_, // 291
	_Frequency_0__, // 292
	_Frequency_1__, // 293
	_Frequency_2__, // 294
	_Frequency_3__, // 295
	_PllBypass_0__, // 296
	_PllBypass_1__, // 297
	_PllBypass_2__, // 298
	_PllBypass_3__, // 299
	_NumRank_dfi1_, // 300
	_NumDbytesPerCh_, // 301
	_PclkPtrInitVal_0__, // 302
	_PclkPtrInitVal_1__, // 303
	_PclkPtrInitVal_2__, // 304
	_PclkPtrInitVal_3__, // 305
	_MaxNumZQ_, // 306
	_NumActiveDbyteDfi0_, // 307
	// pUserInputSim Fields:
	_LcdlRxInsertionDelay_, // 308
	_tWCK2DQO_, // 309
	_tWCK2DQI_, // 310
	_tWCK2CK_, // 311
	_LcdlTxInsertionDelay_, // 312
	_PHY_tDQS2DQ_, // 313
	_RxEnDlyOffset_Reserved_, // 314
	_LcdlNumSteps_, // 315
	_LcdlStepSizex10_, // 316
} userInputFields;

/**Structure used to form pllTable*/
typedef struct pllRow{
    double pllIn_min;
    double pllIn_max;
    int PllCtrl5;
    int PllCtrl1;
    int PllCtrl4;
    int PllUPllProg3;
    int PllUPllProg2;
    int PllUPllProg1;
    int PllUPllProg0;
}pllTableRows;

/// data structure to store register address, value pairs
typedef struct Reg_Addr_Val {
	uint32_t Address;			///< register address
	uint32_t Value;				///< register value
} Reg_Addr_Val_t;

/// A structure to store the sequence function runtime input variables.
typedef struct runtime_config {
	int Train2D;														///< train2d input parameter (deprecated, training is always 2D)

	uint8_t initCtrl;
	///< Skip init steps for debug and sim speed up
	///< Bit   | Name        | Control Setting
	///< ----- | ----        | ---------------
	///<     0 | progCsrSkip | When bit is set progCsrSkipTrain() function is called to program PHY registers in lieu of training firmware.
	///<     1 | skip_fw     | When bit is set skip execution of training firmware entirely  including skipping imem and dmem loads.
	///<     2 | skip_imem   | When bit is set only skip imem load
	///<     3 | skip_dmem   | When bit is set only skip dmem load
	///<     4 | skip_pie    | When bit is set skip loading PIE image.
	///<     5 | devinit     | When bit is set forces SequenceCtrl in messageBlock to devinit

	int skip_train;
	///< skip_train input parameter
	///< Value | Control Setting
	///< ----- | ---------------
	///<     0 | Firmware is executed
	///<     1 | Training is skipped and registers are programmed to work with zero board delay
	///<     2 | Training is skipped but firmware is executed to initialize the DRAM state while registers are programmed to work with zero board delay

	int debug;															///< Print debug messages
	int RetEn;															///< Retention Enable, instructs PhyInit to save CSR addresses to S3 array list
	uint8_t curPState;													///< Internal variable representing current PState of PhyInit as it loops through
	uint32_t pubRev;													///< Digital hardware PUB revision number.

	// All PStates used by various functions.
	uint8_t firstTrainedPState;											///< Internal variable set to 1 for the first trained PState.
	uint8_t lastTrainedPState;											///< Internal variable set to 1 for the last trained PState.
	int curD;															///< Represents the Current dimension of Training 1D vs 2D.

	uint32_t enableBits[3];												///< ACSM configuration bits
	uint16_t NumDxOutPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];			///< Number of DxOutPipeEn pipeline stages
	uint16_t NumDxInPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];			///< Number of DxInPipeEn pipeline stages
	uint16_t NumAlertNPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];		///< Number of AlertNPipeEn pipeline stages
	uint16_t NumAcInPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];			///< Number of AcInPipeEn pipeline stages
	uint16_t NumMiscPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];			///< Number of MiscPipeEn pipeline stages

	uint16_t  psExecOrder[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];			///< PState execution order array
	char* pllSettings; 													///< optional PLL settings file 

	//
	// The variables below this comment are for internal use to be used by PHYINIT code
	//
	
	uint32_t DataRateMbps[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];                       ///< Data rate for each Pstate
	uint8_t NumDbyte;                                                               ///< All Dbytes
	uint8_t NumDbyteActive;                                                         ///< Active Dbytes
	uint8_t NumAchnActive;                                                          ///< Active channels
	uint16_t DfiFreq[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];                            ///< Dfi frequency for each Pstate
	uint32_t tck_ps[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];                             ///< Calculating the DRAM period tCK in picoseconds
	uint32_t UcclkFull[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE]; 
	int TG_active[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
} runtime_config_t;

/// PhyInit meta structure that holds other structures
typedef struct phyinit_config {
	int CurrentPhyInst;																	///< PHY Identifier when using multiple PHY's
	int PclkPtrInitVal[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];								///< Represent the value stored in Step C into the register with the same name

	// === Global Struct Defines === //
	runtime_config_t runtimeConfig;														///< Instance of runtime objects
	user_input_basic_t userInputBasic;													///< Instance of useInputBasic
	user_input_advanced_t userInputAdvanced;											///< Instance of userInputAdvanced
	user_input_sim_t userInputSim;														///< Instance of userInputSim

	// === Firmware Message Block Structs === //
	PMU_SMB_LPDDR5X_1D_t mb_LPDDR5X_1D[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];			///< 1D message block instance
	PMU_SMB_LPDDR5X_1D_t shdw_LPDDR5X_1D[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];		///< Shadow of 1D message block. Used by PhyInit to track user changes to the data structure.


	// === PPT2 data generated in Step C === //
	uint32_t AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_NUM_ACSM_MARKERS];							///< Updated count values for marked ACSM instructions.
	uint8_t  Ppt2PieSeqNum[DWC_DDRPHY_PHYINIT_NUM_ACSM_MARKERS];						///< PPT2 PIE start vector sequence number (0 or 1)
	uint16_t wrFTGwd[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];								///< Adjust Write Fast Toggle width depending on tWCKPST and x8 mode
	uint16_t wrFTGdly[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];								///< Write Fast Toggle delay value to generate 16-bit WR data for ACSMWckWriteFastTogglePulse CSR
} phyinit_config_t;

//-------------------------------
// Global variables - defined in dwc_ddrphy_phyinit_globals.c
//-------------------------------

/*! \def MAX_NUM_RET_REGS
 *  \brief default Max number of retention registers
 *
 * This define is only used by the PhyInit Register interface to define the max
 * amount of registered that can be saved. The user may increase this variable
 * as desired if a larger number of registers need to be restored.
 */
#define MAX_NUM_RET_REGS 15000

typedef enum {
  progCsrFile,
  stepCFile,
}fileType_t;

//-------------------------------------------------------------
// Fixed Function prototypes
//-------------------------------------------------------------
int dwc_ddrphy_phyinit_sequence(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_sequencePsLoop(phyinit_config_t *phyctx);
int dwc_ddrphy_phyinit_restore_sequence(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_C_initPhyConfig(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_overridePLLSettings(phyinit_config_t *phyctx, int mode, const char* print_header);
void dwc_ddrphy_phyinit_D_loadIMEM(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_progCsrSkipTrain(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_F_loadDMEM(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_G_execFW(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_H_readMsgBlock(phyinit_config_t *phyctx, int Train2D);
void dwc_ddrphy_phyinit_I_loadPIEImage(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_assert(int Svrty, const char *fmt, ...);
void dwc_ddrphy_phyinit_cmnt(const char *fmt, ...);
void dwc_ddrphy_phyinit_print(const char *fmt, ...);
void dwc_ddrphy_phyinit_print_dat(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_LoadPieProdCode(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_setDefault(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_calcMb(phyinit_config_t *phyctx);
int dwc_ddrphy_phyinit_storeIncvFile(char *incv_file_name, uint32_t mem[], return_offset_lastaddr_t return_type);
void dwc_ddrphy_phyinit_storeMsgBlk(void *msgBlkPtr, int sizeOfMsgBlk, uint32_t mem[]);
void dwc_ddrphy_phyinit_WriteOutMem(uint32_t mem[], int mem_offset, int mem_size, int sparse_write);
int dwc_ddrphy_phyinit_IsDbyteDisabled(phyinit_config_t *phyctx, int DbyteNumber);
int dwc_ddrphy_phyinit_getUserInput(phyinit_config_t *phyctx, char *field);
int dwc_ddrphy_phyinit_getMb(phyinit_config_t *phyctx, int ps, char *field);
int dwc_ddrphy_phyinit_setUserInput_enum(phyinit_config_t *phyctx, userInputFields field, int value);
int dwc_ddrphy_phyinit_setUserInput(phyinit_config_t *phyctx, char *field, int value);
int dwc_ddrphy_phyinit_trackReg(uint32_t adr);
void dwc_ddrphy_phyinit_MicroContMuxSel_write32(uint32_t dat);
void initRuntimeConfigEnableBits(phyinit_config_t* phyctx);
int dwc_ddrphy_phyinit_regInterface(regInstr myRegInstr, uint32_t adr, uint16_t dat);
void dwc_ddrphy_phyinit_getS3List(int S3List[MAX_NUM_RET_REGS]);
void dwc_ddrphy_phyinit_chkInputs(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_chkAllLegalValues(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_getPsExecOrder(phyinit_config_t *phyctx);

extern void dwc_ddrphy_phyinit_userCustom_overrideUserInput(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_A_bringupPower(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_customPreTrain(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_customPreTrainPsLoop(phyinit_config_t *phyctx, int pstate);
extern void dwc_ddrphy_phyinit_userCustom_customPostTrain(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop(phyinit_config_t *phyctx, int pstate);
extern int dwc_ddrphy_phyinit_userCustom_E_setDfiClk(phyinit_config_t *phyctx, int pstate);
extern void dwc_ddrphy_phyinit_userCustom_G_waitFwDone(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_H_readMsgBlock(phyinit_config_t *phyctx, int Train2D);
extern void dwc_ddrphy_phyinit_userCustom_J_enterMissionMode(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_io_write16(uint32_t adr, uint16_t dat);
extern void dwc_ddrphy_phyinit_userCustom_io_write32(uint32_t adr, uint32_t dat);
void dwc_ddrphy_phyinit_io_write16(uint32_t adr, uint16_t dat);
void dwc_ddrphy_phyinit_io_write32(uint32_t adr, uint32_t dat);
extern uint16_t dwc_ddrphy_phyinit_userCustom_io_read16(uint32_t adr);
extern uint32_t dwc_ddrphy_phyinit_userCustom_io_read32(uint32_t adr);
extern void dwc_ddrphy_phyinit_userCustom_saveRetRegs(phyinit_config_t *phyctx);
extern void dwc_ddrphy_phyinit_userCustom_wait(uint32_t nDfiClks);
extern void dwc_ddrphy_phyinit_userCustom_waitTime(uint32_t waitTimeNs);

void dwc_ddrphy_phyinit_ProgPPT(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_PieFlags(phyinit_config_t *phyctx, int prog_csr);
int dwc_ddrphy_phyinit_setReg(uint32_t adr, uint16_t dat);

int dwc_ddrphy_phyinit_setStruct(phyinit_config_t *phyctx, const void *userStruct, int structType);
phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, char* pllSettings, int pubRev);
void dwc_ddrphy_phyinit_configFree(phyinit_config_t *ptr);
void dwc_ddrphy_phyinit_programPLL(phyinit_config_t *phyctx, int mode, const char* print_header);
void dwc_ddrphy_phyinit_ACSM_delay(phyinit_config_t *phyctx, uint8_t pstate, const char* print_header);
void dwc_ddrphy_phyinit_programLCDLSeed(phyinit_config_t *phyctx, int mode, const char* print_header);
uint16_t dwc_ddrphy_phyinit_getNumPipeStages(uint16_t PipeEn);
void dwc_ddrphy_phyinit_programPclkDca(phyinit_config_t *phyctx, int pstate);
void dwc_ddrphy_phyinit_setTxRxPowerDown(uint8_t powerDown, phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_PowerUp(phyinit_config_t *phyctx);
void dwc_ddrphy_phyinit_programDfiMode(phyinit_config_t *phyctx, dfiMode_t mode);

void dwc_ddrphy_phyinit_programMemResetL(phyinit_config_t *phyctx, fileType_t fileType, uint16_t MemResetL);

#include "dwc_ddrphy_csr_ALL_cdefines.h"

#endif // _DWC_DDRPHY_PHYINIT_USERCUSTOM_H_
