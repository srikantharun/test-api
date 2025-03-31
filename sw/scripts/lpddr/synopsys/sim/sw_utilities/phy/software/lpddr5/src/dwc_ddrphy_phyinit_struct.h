

#ifndef _DWC_DDRPHY_PHYINIT_STRUCT_H_
#define _DWC_DDRPHY_PHYINIT_STRUCT_H_


/** \file dwc_ddrphy_phyinit_struct.h
 *  \brief This file defines the internal data structures used in PhyInit to store user configuration.
 *
 *  Please see \ref docref to obtain necessary information for program variables
 *  correctly for your PHY variant and process technology.
 */

/**  \addtogroup structDef
 *  @{
 */

/** Enumerator for DRAM Type */
typedef enum DramTypes {
     DDR4,                              /*!< DDR4 */
     DDR3,                              /*!< DDR3 */
     LPDDR4,                            /*!< LPDDR4 */
     LPDDR3,                            /*!< LPDDR3 */
     LPDDR5,                            /*!< LPDDR5 */
     DDR5                               /*!< DDR5 */
} DramType_t;

/** Enumerator for DIMM Type */
typedef enum DimmTypes {
  UDIMM,            /*!< UDIMM */
  SODIMM,           /*!< SODIMM */
  RDIMM,            /*!< RDIMM*/
  NODIMM,           /*!< No DIMM (Soldered-on) */
  NVDIMMP           /*!< NVDIMMP */
} DimmType_t;

#include "dwc_ddrphy_phyinit_protocols.h"

/** \brief Structure for basic (mandatory) user inputs
 *
 * The following basic data structure must be set and completed correctly so
 * that the PhyInit software package can accurately program PHY registers.
 */
typedef struct user_input_basic {
  /**
   * @brief DRAM Module Type
   * - Choose DRAM Module Type
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x2 | LPDDR4
   *     0x4 | LPDDR5
   *     0x5 | DDR5
   * - Default: 0x5
   */
  DramType_t DramType;

  /**
   * @brief DIMM type specification
   * - Choose the Dimm type
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | UDIMM
   *     0x1 | SODIMM
   *     0x2 | RDIMM
   *     0x3 | No DIMM (Soldered-on)
   *     0x4 | NVDIMMP
   * - Default: 0x4
   */
  DimmType_t DimmType;

  /**
   * @brief Number of chnnels supported by PHY
   * - Must match RTL define DWC_DDRPHY_NUM_CHANNELS_1 and DWC_DDRPHY_NUM_CHANNELS_2
   * - Values: 1, 2
   * - Default: 2
   */
  int NumCh;

  /**
   * @brief Number of ranks supported by PHY
   * - Must match RTL define DWC_DDRPHY_NUM_RANKS_1 and DWC_DDRPHY_NUM_RANKS_2 for LPDDR5
   * - Values: 1, 2
   * - Default: 1 for LPDDR5/LPDDR4
   */
  int NumRank;

  /**
   * @brief Number of Dbytes Per channel supported by PHY
   * - Must match RTL define DWC_DDRPHY_NUM_DBYTES_PER_CHANNEL_2
   * - The option of DWC_DDRPHY_NUM_DBYTES_PER_CHANNEL_4 is not supported
   * - Values: 2
   * - Default: 2
   */
  int NumDbytesPerCh;

  /**
   * @brief Number of active dbytes to be controlled by dfi0
   * - See PUB databook section on supported PHY configurations for valid settings.
   * - Values: 2, 4
   * - Default: 2
   */
  int NumActiveDbyteDfi0;

  /**
   * @brief Number of active dbytes to be controlled by dfi1
   * - See PUB databook section on supported PHY configurations for valid settings.
   * - Values: 0, 2, 4
   * - Default: 2
   */
  int NumActiveDbyteDfi1;

  /**
   * @brief Number of active ranks in DFI0 channel
   * - See PUB databook section on supported PHY configurations for valid settings.
   * - Values: 1, 2
   * - Default: 1 for LPDDR5/LPDDR4
   */
  int NumRank_dfi0;

  /**
   * @brief Number of active ranks in DFI1 channel
   * - See PUB databook section on supported PHY configurations for valid settings.
   * - Values: 0, 1, 2
   * - Default: 1 for LPDDR5/LPDDR4
   */
  int NumRank_dfi1;

  /**
   * @brief DRAM chip data bus width
   * - See PUB databook section "Supported System Configurations" for DRAM width options supported by your PHY product.
   * @note: For mixed x8 and x16 width devices, set variable to x8.
   * - Values: 8, 16
   * - Default: 16
   */
  int DramDataWidth;


  /**
   * @brief Number of DRAM devices (die) sharing a ZQ resistor(LPDDR5 only).
   * - Specifies the maximum number of DRAM die within a package that can share a common external ZQ resistor.
   * - This value is used to derive the ZQ calibration time (tZQCAL).
   * - Values:
   *  - Min: 1
   *  - Max: 16
   * - Default: 4
   */
  int MaxNumZQ;

  /**
   * @brief Number of p-states used
   * - Number of p-states used, must be decimal integer between 1 and 4
   * - Values:
   *  - Min: 1
   *  - Max: 4
   * - Default: 1
   */
  int NumPStates;

  /**
   * @brief Define 4-bit binary map to enable specific PStates
   * - Each bit position defines if the corresponding PState is valid.
   * - Note, the number of 1's in CfgPStates must match userInput NumPState entry.
   * - Example 1: When NUmPStates=2 and PState 1 and 2 are to be enabled, CfgPStates=0x6 ('b0110)
   * - Example 2: When NumPStates=3 and Pstate 0, 1, and 3 are to be enabled, CfgPStates=0xB ('b1011)
   * - Example 3: When NumPstates=4, all PStates to be enabled, CfgPStates=0xF ('b1111)
   *  - Values:
   *  - Min: 0x1
   *  - Max: 0xf
   * - Default: 0x1
   */
  int CfgPStates;

  /**
   * @brief First PState for Cold Boot.
   * - In order to ensure correct state of DRAM, the initialization sequence needs to match the last
   *   trained PState with the first PState entered in Step J.  ie the first
   *   set of dfi_frequency, dfi_freq_ratio and dfi_freq_fsp on cold boot must select this PState.
   * - Any valid PState can be specified.
   * - Values:
   *     Value | Description
   *     ----- | -----------
   *       0   | PState 0
   *       1   | PState 1
   *       2   | PState 2
   *       3   | PState 3
   * - Default: 0x0
   */
  int FirstPState;


  /**
   * @brief DRAM CK Frequency for each PState
   * - Frequency of CK_t in MHz round up to next highest integer. Enter 334 for 333.333, etc.
   * - Each array entry must represent the value for the index Pstate.
   * - Values:
   *   - Min: 5
   *   - Max: 1200
   * - Default: 800
   */
  int Frequency[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Enable PLL Bypass
   * - Indicates if PLL should be in Bypass mode.
   * - See PUB Databook section "PLL Bypass Mode" under "Clocking and Timing" for requirements.
   * - At data rates below 667 Mbps, PLL must be in Bypass Mode.
   * - Must be set as hex.
   * - Each array entry must represent the value for the indexed Pstate.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Disabled
   *     0x1 | Enabled
   * - Default: 0x1
   */
  int PllBypass[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief Selected dfi frequency ratio
   * - Used to program the DfiFreqRatio register. This register controls how dfi_freq_ratio
   *   input pin should be driven inaccordance with DFI Spec.
   * - For LPDDR4: this is the ratio between the DFI clock and the memory clock CK.
   * - For LPDDR5: this is the ratio between the DFI Clock and WCK.(The DFI Clock to CK clock is always a 1:1 ratio for LPDDR5.)
   * - See PUB databook section "DfiClk" on details on how to set the value.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x1 | 1:2
   *     0x2 | 1:4
   * - Default: 0x1
   */
  int DfiFreqRatio[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Hard Macro Family version in use
   * - Please see technology specific PHY Databook for "Hard Macro Family" version. The variable is used to fine tune analog register value settings.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | hardmacro family A
   *       1 | hardmacro family B
   * - Default: 0
   */
  int HardMacroVer;


  /**
   * @brief Indicates LPDDR5X mode support (LPDDR5 only)
   * - Indicates LPDDR5X mode support
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | LPDDR5  mode, when DramType is LPDDR5
   *     0x1 | LPDDR5X mode, when DramType is LPDDR5
   * - Default: 0x0
   */
  int Lp5xMode;

  /**
   * @brief PclkPtrInitVal
   * - Set this to the number of pclks for write/read pointer initialization separation
   * - Values :
   * - Min : 3
   * - Max : 10
   * - Default : 3
   */
  int PclkPtrInitVal[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief PclkPtrInitVal override variable.
   * - Set this to 1 if the PclkPtrInitVal should be overriden via userInput.  else,
   * - dwc_ddrphy_phyinit_C_initPhyConfig.c will program based on PLL mode and Data rate
   * - Values:
   * - Min : 0
   * - Max : 1
   * - Default : 0
   */
  int PclkPtrInitValOvr;



} user_input_basic_t;

/** \brief Structure for advanced (optional) user inputs
 *
 *  if user does not enter a value for these parameters, a default recommended or
 *  default value will be used
 */
typedef struct user_input_advanced {

  /**
   * @brief Controls the Receiver bias current control for the DQS RxReplica circuits
   * - Used for programming RxGainCurrAdjDIFF1 registers.
   * - Please Refer to Technology specific PHY DATABOOK for supported values.
   * - Values:
   *   - Min: 0
   *   - Max: 0xf
   * - Default: 0x5
   */
  int RxBiasCurrentControlRxReplica[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Controls the Receiver bias current control for WCK (LPDDR5 only)
   * - Used for programming RxGainCurrAdjRxReplica registers.
   * - Please Refer to Technology specific PHY DATABOOK for supported values.
   * - Values:
   *   - Min: 0
   *   - Max: 0xf
   * - Default: 0x5
   */
  int RxBiasCurrentControlWck[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Indicates Power-saving clock divider to ZCAL
   * - Indicates the ratio of HMZCAL DfiClk to PUB ZCAL DfiClk
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Recommended for DfiClk < 800 MHz
   *     0x1 | Recommended for debug
   *     0x2 | Recommended for debug
   *     0x3 | Recommended for DfiClk >=800 MHz
   * - Default: 0
   */
  int ZcalClkDiv[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Tx Drive Impedance for DQ bit slices in ohm
   * - Does not apply to WCK_t/c, DQS_t/c
   * - Used for programming DQ TxImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "Output drive pull-up/down Impedance: DQ, DQS outputs" in "Common DC Output Paremeters"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   * - Default: 60
   */
  int TxImpedanceDq[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Tx Drive Impedance for DQS_t/c in ohm
   * - Used for programming DQS TxImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "Output drive pull-up/down Impedance: address, command, CLK outputs" in "Common DC Output Paremeters"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   * - Default: 60
   */
  int TxImpedanceDqs[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  /**
   * @brief Tx Drive Impedance for CS,CKE bit slices in ohm
   * - Used for programming AC SE TxImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "Common DC Output Parameters"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     400 | 400 ohms
   *     100 | 100 ohms
   *      66 | 66 ohms
   *      50 | 50 ohms
   * - Default: 50
   */
  int TxImpedanceCsCke;

  /**
   * @brief Reserved. 
   * - Only default value is supported 
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Reserved 
   *       1 | Not supported 
   * - Default: 0x0
   */  
  int DisRxClkCLcdl[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Reserved. 
   * - Only default value is supported 
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Reserved 
   *       1 | Not supported 
   * - Default: 0x0
   */
  int DramStateChangeEn;

  /**
   * @brief Reserved.  
   * - Only default value is supported 
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Reserved 
   *       1 | Not supported 
   * - Default: 0x0
   */
  int DfiLoopbackEn;

  /**
   * @brief Reserved.  
   * - Only default value is supported 
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Reserved 
   *       1 | Not supported 
   * - Default: 0x0
   */
  int HalfTxCalCode;

  /**
   * @brief Tx Drive Impedance for AC bit slices in ohm
   * - Does not apply to CKE(LP4), CS(LP5), CK_t/c
   * - Used for programming AC SE TxImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "Common DC Output Parameters"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   * - Default: 60
   */
  int TxImpedanceAc[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Tx Drive Impedance for CK_t/c in ohm
   * - Used for programming AC DIFF TxImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "Common DC Output Parameters"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   * - Default: 60
   */
  int TxImpedanceCk[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Tx Drive Impedance for WCK_t/c in ohm (LPDDR5 only)
   * - Used for programming WCK TxImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "Output drive pull-up/down Impedance: address, command, CLK outputs" in "Common DC Output Paremeters"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   *      30 | 30 ohms
   * - Default: 60
   */
  int TxImpedanceWCK[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Use SNPS Controller 
   * - When using SNPS Controller, PHYINIT programs csrCtrlUpdReqDelay0,1/CtrlUpdAckDelay0,1 value per PState based on data rate
   *   to add timing margin (0~15 DfiClks) before and after DRAM CK stop when MRR Snoop retraining is enabled.
   * - When using 3rd party Controller, PHYINIT doesn't change csrCtrlUpdReqDelay0,1/CtrlUpdAckDelay0,1 value.
   * - When set to 1 and EnWck2DqoTracking is enabled, this will programcsr DisableZQupdateOnSnoop=1,
   *   otherwise,program DisableZQupdateOnSnoop=0.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Use 3rd party Controller
   *       1 | Use SNPS Controlller
   * - Default: 0x0
   */
  int UseSnpsController;

  /**
   * @brief ODT Impedance for DQ bit slices in ohm
   * - Does not apply to DQS_t/c
   * - Used for programming DQ OdtImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "On-die termination (ODT) programmable resistances (Rtt)" in "DC Input Conditions"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.ODT Impedance for DQ bit slices in ohm
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Hi-Z
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   *      30 | 30 ohms
   * - Default: 40
   */
  int OdtImpedanceDq[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief ODT Impedance for DQS_t/c in ohm
   * - Used for programming DQS OdtImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "On-die termination (ODT) programmable resistances (Rtt)" in "DC Input Conditions"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PUB databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Hi-Z
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   *      30 | 30 ohms
   * - Default: 40
   */
  int OdtImpedanceDqs[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief ODT Impedance for WCK_t/c in ohm (LPDDR5 only)
   *
   * - Used for programming WCK OdtImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "On-die termination (ODT) programmable resistances (Rtt)" in "DC Input Conditions"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PUB databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Hi-Z
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   *      30 | 30 ohms
   * - Default: 40
   */
  int OdtImpedanceWCK[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief ODT Impedance for CA bit slices in ohm
   * - Used for programming AC SE OdtImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "On-die termination (ODT) programmable resistances (Rtt)" in "DC Input Conditions"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Hi-Z
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   *      30 | 30 ohms
   * - Default: 40
   */
  int OdtImpedanceCa[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief ODT Impedance for CK bit slices in ohm
   * - Used for programming AC DIFF OdtImpedance registers.
   * - See "Electrical Parameters" in PHY Databook for supported impedance
   *   range given your Hard Macro Family.  Set based on Typical values from
   *   "On-die termination (ODT) programmable resistances (Rtt)" in "DC Input Conditions"
   *   table for each protocol. See table foot notes for more details.
   * - Based on SI Analysis and DRAM modules, select from supported values in the PHY Databook.
   *   Only values in the PHY databook are supported.
   * - Must be decimal integer.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Hi-Z
   *     120 | 120 ohms
   *      60 | 60 ohms
   *      40 | 40 ohms
   *      30 | 30 ohms
   * - Default: 40
   */
  int OdtImpedanceCk[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief Pull-up slew rate control for DQ, DMI and DQS
   * - Value specified here will be written to DQ, DMI and DQS TxSlew register.
   *   See register description for more information.
   * - Only the default are currently recommended.
   * - Values:
   *   - Min: 0x0
   *   - Max: 0xf
   * - Default: 0x3 for LPDDR5/LPDDR4
   */
  int TxSlewRiseDq[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Pull-down slew rate control for DQ, DMI and DQS
   * - Value specified here will be written to DQ, DMI and DQS TxSlew register.
   *   See register description for more information.
   * - Only the default are currently recommended.
   * - Values:
   *   - Min: 0x0
   *   - Max: 0xf
   * - Default: 0x0 for LPDDR5/LPDDR4
   */
  int TxSlewFallDq[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief Pull-up slew rate control for CA lanes
   * - Value specified here will be written to AC SE TxSlew register.
   *   See register description for more information.
   * - Only the default are currently recommended.
   * - Values:
   *   - Min: 0x0
   *   - Max: 0xf
   * - Default: 0x3 for LPDDR5/LPDDR4
   */
  int TxSlewRiseCA[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Pull-down slew rate control for CA lanes
   * - Value specified here will be written to AC SE TxSlew register.
   *   See register description for more information.
   * - Only the default are currently recommended.
   * - Values:
   *   - Min: 0x0
   *   - Max: 0xf
   * - Default: 0x0 for LPDDR5/LPDDR4
   */
  int TxSlewFallCA[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
    * @brief Pull-up slew rate control for CS lanes
    * - Value specified here will be written to AC CS TxSlew register.
    *   See register description for more information.
    * - Only the default are currently recommended.
    * - Values:
    *   - Min: 0x0
    *   - Max: 0xf
    * - Default: 0x8 for LPDDR5/LPDDR4
    */
  int TxSlewRiseCS[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
    * @brief Pull-down slew rate control for CS lanes
    * - Value specified here will be written to AC CS TxSlew register.
    *   See register description for more information.
    * - Only the default are currently recommended.
    * - Values:
    *   - Min: 0x0
    *   - Max: 0xf
    * - Default: 0xf for LPDDR4/LPDDR5
    */
  int TxSlewFallCS[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
    * @brief Pull-up slew rate control for CK
    * - Value specified here will be written to AC DIFF TxSlew register.
    *   See register description for more information.
    * - Only the default are currently recommended.
    * - Values:
    *   - Min: 0x0
    *   - Max: 0xf
    * - Default: 0x3 for LPDDR5/LPDDR4
    */
  int TxSlewRiseCK[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
    * @brief Pull-down slew rate control for CK
    * - Value specified here will be written to AC DIFF TxSlew register.
    *   See register description for more information.
    * - Only the default are currently recommended.
    * - Values:
    *   - Min: 0x0
    *   - Max: 0xf
    * - Default: 0x0 for LPDDR5/LPDDR4
    */
  int TxSlewFallCK[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief Determine behavior of CK pins when dfi_clk_disable is used.
   * - See register CkDisVal register description.
   * - value directly written to register.
   * - Values: 0
   * - Only the default value is supported.
   * - Default: 0
   */
  int CkDisVal[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief DRAM Oscillator count source mapping.
   * - The PHY supports swapping of DRAM oscillator count values between paired DBytes for the purpose of tDQSDQ DRAM Drift Compensation(DDC).
   * - Each DByte has a register bit to control the source of the oscillator count value used to perform tDQSDQ Drift compensation.
   *   The training firmware will not determine the DByte swap, it will rely on PptCtlStatic register to select oscillator count source.
   *   This input is used to program such CSR and is required depending on the configuration.
   * - The default hardware configuration is for odd Dbyte instance n to use oscillator count values from its paired Dbyte instance n-1.
   *   So Dbyte1 will use the oscillator count values from Dbyte0, Dbyte3 will use Dbyte2 and so on.  This is required for DRAM Data width =16.
   * - Each bit of this field corresponds to a DBYTE:
   *   - bit-0 = setting for DBYTE0
   *   - bit-1 = setting for DBYTE1
   *   - bit-2 = setting for DBYTE2
   *   - . . .
   *   - bit-n = setting for DBYTEn
   * - By setting the associated bit for each DByte to 1, PHY will use non-default source for count value.
   *   - for even Dbytes, non-default source is to use the odd pair count value.
   *   - for odd Dbytes, no-default source to use data received directly from the DRAM.
   * - Byte swapping must be the same across different ranks.
   * - must be set as hex
   * - if Byte mode devices are indicated via the X8Mode messageBlock parameter, this variable is ignored as PHY only supports
   *   a limited configuration set based on Byte mode configuration..
   * Example:
   *   DramByteSwap = 0x03 - Dbyte0: use count values from Dbyte1, Dbyte1 uses count values received directly received from DRAM.
   *   Rest of Dbytes have default source for DRAM oscilator count.
   * - Values:
   *    Value | Description
    *    ----- | ------
    *      0x0 | no DBYTEs are swapped
    *      0x3 | DBYTEs in channel A are swapped 
    *      0xc | DBYTEs in channel B are swapped
    *      0xf | DBYTEs in both DFI channels are swapped
   * - Default: 0
   */
  int DramByteSwap;


  /**
   * @brief Specifies how frequently dfi_phymstr_req is issued by PHY
   * - See PUB databook section "DFI Master Interface" and DFI 3.1
   *   Spec + 4.0v2 Addendum for details of DFI PHY Master interface.
   * - Based on SI analysis determine how frequently DRAM drift compensation and
   *   re-training is required.
   * - Determine if Memory controller supports DFI PHY Master Interface.
   * - Program based on desired setting for PPTTrainSetup.PhyMstrTrainInterval register.
   *   See register description in PUB Databook for translation table
   *   of values to MEMCLKs.  Example values provided in below table.
   * - The DFI PHY Master Interface needs to be disabled when controller uses dwc_ddrphy_snoop_en interface for drift tracking.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | to Disable PHY Master Interface
   *    0x1 | PPT Train Interval = 262144 DfiClks
   *    0x2 | PPT Train Interval =  524288 DfiClks
   *    0x3 | PPT Train Interval =  1048576 DfiClks
   *    0x4 | PPT Train Interval =  2097152 DfiClks
   *    0x5 | PPT Train Interval =  4194304 DfiClks
   *    0x6 | PPT Train Interval =  8388608 DfiClks
   *    0x7 | PPT Train Interval =  16777216 DfiClks
   *    0x8 | PPT Train Interval =  33554432 DfiClks
   *    0x9 | PPT Train Interval =  67108864 DfiClks
   *    0xA | PPT Train Interval =  134217728 DfiClks
   *    0xB | Interval = undefined
   * - Default: 0x0a
   */
  int PhyMstrTrainInterval[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Max time from dfi_phymstr_req asserted to dfi_phymstr_ack asserted
   * - Based on your Memory controller's(MC) specification determine how long the PHY
   *  should wait for the assertion of dfi_phymstr_ack once dfi_phymstr_req has
   *  been issued by the PHY. If the MC does not ack the PHY's request, PHY may issue
   *  dfi_error.
   * - See PUB databook section "DFI Master Interface" and DFI 3.1
   *  Spec + 4.0v2 Addendum for details of DFI PHY Master interface.
   * - This value will be used to program PPTTrainSetup.PhyMstrMaxReqToAck register.
   *  See detailed register description in PUB Databook.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Disable PHY Master Interface
   *     0x1 | PPT Max. Req to Ack. = 256 DfiClks
   *     0x2 | PPT Max. Req to Ack. = 512 DfiClks
   *     0x3 | PPT Max. Req to Ack. = 1024 DfiClks
   *     0x4 | PPT Max. Req to Ack. = 2048 DfiClks
   *     0x5 | PPT Max. Req to Ack. = 4096 DfiClks
   *     0x6 | PPT Max. Req to Ack. = 16384 DfiClks
   *     0x7 |  PPT Max. Req to Ack. = undefined
   * - Default: 0x5
   */
  int PhyMstrMaxReqToAck[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Specifies the interval between successive calibrations, in mS
   * - See PUB Databook section "Impedance Calibrator" to learn about PHY Impedance
   *   calibration FSM. Based on feedback from SI analysis, determine desired
   *   calibration interval for your System.
   * - Program variable based on desired setting for CalRate.CalInterval register.
   *   See detailed register description in PUB Databook.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *    0x0  | 0 (continuous)
   *    0x3  | 1 ms
   *    0x4  | 2 ms
   *    0x5  | 3 ms
   *    0x6  | 4 ms
   *    0x7  | 8 ms
   *    0x8  | 10 ms
   *    0x9  | 20 ms
   * - Default: 0x9
   */
  int CalInterval;

  /**
   * @brief This setting changes the behavior of CalRun register
   * - See PUB Databook section "Impedance Calibrator" to learn about PHY Impedance
   *   calibration FSM. Based on feedback from SI analysis, determine desired
   *   calibration interval for your System.
   * - Program variable based on desired setting for CalRate.CalInterval register.
   *   See detailed register description in PUB Databook.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *   0x1   | The 0->1 transition of CSR CalRun causes a single iteration of the calibration sequence to occur
   *   0x0   | Calibration will proceed at the rate determined by CalInterval. This field should only be changed while the calibrator is idle. ie before csr CalRun is set
   * - Default: 0x0
   */
  int CalOnce;

  /**
   * @brief Adjustment to bias current in the Impedance Calibration Control Circuit
   * - It is not recommended to change the default value of this parameter.
   * - Values: 0
   * - Default: 0
   */
  int CalImpedanceCurrentAdjustment;

  /**
   * @brief Firmware Training Sequence Control
   * - This input is used to program SequenceCtrl in messageBlock.
   *   It controls the training stages executed by firmware.
   *   Consult the training firmware App Note section "1D Training Steps" for details on training stages.
   * - For production silicon Synopsys recommends to use default value programmed by PhyInit.
   * - If running simulation for the first time, program value according to "Initial interactions with the firmware" section in Training firmware App Note.
   * - Values:
   *  - Min: 0
   *  - Max: 0xffff
   * - Default: 0x131f
   */
  int TrainSequenceCtrl[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Disable PHY DRAM Drift compensation re-training
   * - Disable PHY re-training during DFI frequency change requests.
   * - The purpose of retraining is to compensate for drift in the DRAM.
   * - Determined based on SI analysis and DRAM datasheet if retraining can be disabled.
   * @note If SkipTrain==1 (via "phyinit -skip_train [1|2]" or runtime_config.initCtrl[0]=1), DisableRetraining must be value 1.  PHY DRAM Drift compenstation
   *       retraining can only be enabled if Training FW is enabled.
   * - Values:
   *    Value | Description
   *    ----- | -----------
   *      0x1 | Disable retraining
   *      0x0 | Enable retraining
   * - Default: 0x0
   */
    int DisableRetraining;

  /**
   * @brief Disable DFI PHY Update feature
   * - Disable DFI PHY Update feature. When set PHY will not assert dfi0/1_phyupd_req.
   *   See DFI specification for DFI PHY update interface.  See PUB databook section
   *   "PHY Update" for details of the DFI PHY update interface implementation.
   * - The DFI PHY Update features needs to be disabled when controller uses dwc_ddrphy_snoop_en interface for drift tracking.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x1 | Disable DFI PHY Update
   *     0x0 | Enable DFI PHY Update
   * - Default: 0x0
   */
  int DisablePhyUpdate;

  /**
   * @brief Controls the frequency of the PMU clock
   * - Controls the frequency of the PMU clock
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | DfiClk frequency
   * - Default: 0x0
   */
  int PmuClockDiv[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Disables PHY Microcontroller ECC
   * - Disable PHY Microcontroller ECC
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | ECC enabled
   *     0x1 | ECC disabled
   * - Default: 0
   */
  int DisablePmuEcc;

  /**
   * @brief Prevent the PHY from sending MRW commands for destination pstate.
   * - If set to 0, the PHY will send MRW for destination pstate and will set MR13.FSP-OP(LPDDR4) or MR16.FSP-OP(LPDDR5) based on dfi_freq_fsp input;
   * - If set to 1 in LPDDR4, PHY will not send DRAM MRW for destination pstate and will not set MR13 FSP-OP. MC must send DRAM MRW as well as MR13 FSP-OP;
   * - If set to 1 in LPDDR5, PHY will not send DRAM MRW for destination. However, PHY will set MR16 FSP-OP based on dfi_freq_fsp input.  
   *   Refer to frequency change section of PUB datatbook
   * - This behavior can be disabled if desired.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | FSP-OP enabled
   *     0x1 | FSP-OP disabled
   * - Default: 0 for LPDDR5/LPDDR4
   * - Default: 1 for DDR5
   */
  int DisableFspOp;

  /**
   * @brief Enable PHY RxClk Drift Tracking
   * - Refer to PUB databook for details of this PHY feature.
   * - Enable RxClkTrackEn=1 when retraining is enabled only.
   * - At data rates below 1600Mbps the RxClk tracking must be disabled.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | disabled
   *     0x1 | enabled
   * - Default: 1
   */
  int RxClkTrackEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief Read DQS Drift tracking threshold
   * - The value specified here is programmed directly in the RxDqsTrackingThreshold register.
   * - When tracking is enabled (EnRxDqsTracking = 1), this input is used to set the tracking threshold.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | threshold value of 3
   *       1 | threshold value of 5
   *       2 | threshold value of 9
   *       3 | threshold value of 15
   *       4 | threshold value of 31
   * - Default: 1
   */
  int RxDqsTrackingThreshold[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Informs the PHY of the DQS oscillator runtime configured in the DRAMs
   * - Or the runtime used by the controller. That time must agree with the configuration of this CSR.
   * - The value specified here is programmed directly in the DqsOscRunTimeSel register.Informs the PHY of the DQS oscillator runtime
   *   configured in the DRAMs. This user input should be used when snoop mode is enabled
   *   (userInputAdvanced->EnWck2DqoTracking[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATES]),
   *   else the default value should be used. DqsOscRunTimeSel = 0x3 (DRAM OSC Runtime = 2048tCK) is used during retraining by PIE.
   *   Please refer to PUB data book for details on MRR Snoop mechanism.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x3 | Runtime of 2048 memCK
   * - Default: 3
   */
  int DqsOscRunTimeSel[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Invert the phase-dectector value as seen by the tracking logic.
   * - The value specified here is programmed directly in the DqsSampNegRxEnSense register.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | RxEnDlyTg is trained to be 1UI before the posedge of DQS_T
   *     0x1 | RxEnDlyTg is trained to be 2UI before the posedge of DQS_T
   * - Default: 1
   */
  int DqsSampNegRxEnSense[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Enable Snoop Interface to modify the RxEn timing (LPDDR5 only)
   * - The value specified here is programmed directly into the EnWck2DqoSnoopTracking register.
   * - If enabled, this will program CSR EnPhyUpdateZQCalUpdate=1 (see PUB databook Snoop section for details).
   * - If enabled and UseSnpsController is set, this will programcsr DisableZQupdateOnSnoop=1(see PUB databook Snoop section for details)
   * - If system uses MRR Snoop retraining in any PState, all PState's must be set.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | disabled
   *     0x1 | enabled
   * - Default: 0x0
   */
  int EnWck2DqoTracking[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Reserved. 
   * - Only default value is supported 
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *       0 | Reserved 
   *       1 | Not supported 
   * - Default: 0x0
   */
  int SnoopWAEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
	
  /**
   * @brief Enable support for Deep Sleep Mode during LP3 (LPDDR5 only)
   * - Specifies the state of the DRAM when entering LP3.
   * - When Deep Sleep Mode is selected, the PHY will wait longer to satisfy tXDSM_XP during LP3 exit sequence.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Self-Refresh + Power Down Mode
   *     0x1 | Deep Sleep Mode
   * - Default: 0x0
   */
  int Lp3DramState[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Select Retraining Mode.
   * - Retraining Mode for enabling PPT2.
   * @note PHY does not support PPT2 to PStates data rates < 1600Mbps.
   * @note PPT2 can only be supported with PUB version 2.00 or higher.
   *
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | No Retraining
   *     0x1 | PPT1
   *     0x4 | Interleaved Retraining (PPT2)
   * - Default: 1
   */
  int RetrainMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Override DxInPipeEn.
   * - When user input DxInPipeEnOvr is set, the value from this user input is used.
   * - Each bit set enables a stage of delay for the signals.
   * - Must be programmed as hex.
   * - If no override value provided, DfiClk frequency dependent value programmed.
   *   Value | Description
   *   ----- | -----------
   *     0x0 | No stages of delay for signals
   *     0x1 | Enable 1 stage of delay for signals
   *     0x2 | Enable 1 stage of delay for signals
   *     0x3 | Enable 2 stages of delay for signals
   *     0x4 | Enable 1 stage of delay for signals
   *     0x5 | Enable 2 stages of delay for signals
   *     0x6 | Enable 2 stages of delay for signals
   *     0x7 | Enable 3 stages of delay for signals
   *     0x8 | Enable 1 stage of delay for signals
   *     0x9 | Enable 2 stages of delay for signals
   *     0xA | Enable 2 stages of delay for signals
   *     0xB | Enable 3 stages of delay for signals
   *     0xC | Enable 2 stages of delay for signals
   *     0xD | Enable 3 stages of delay for signals
   *     0xE | Enable 3 stages of delay for signals
   *     0xF | Enable 4 stages of delay for signals
   * - Default: 0
   */
  int DxInPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief DxInPipeEn override variable
   * - Set this to 1 if the DxInPipeEn should be overriden via userInput.  else,
   * - dwc_ddrphy_phyinit_C_initPhyConfig.c will program a default
   * - Values:
   * - Min : 0
   * - Max : 1
   * - Default : 0
   */
  int DxInPipeEnOvr;

  /**
   * @brief Override DxOutPipeEn.
   * - When user input DxOutPipeEnOvr is set, the value from this user input is used.
   * - Each bit set enables a stage of delay for the signals.
   * - Must be programmed as hex.
   * - If no override value provided, DfiClk frequency dependent value programmed.
   *   Value | Description
   *   ----- | -----------
   *     0x0 | No stages of delay for signals
   *     0x1 | Enable 1 stage of delay for signals
   *     0x2 | Enable 1 stage of delay for signals
   *     0x3 | Enable 2 stages of delay for signals
   *     0x4 | Enable 1 stage of delay for signals
   *     0x5 | Enable 2 stages of delay for signals
   *     0x6 | Enable 2 stages of delay for signals
   *     0x7 | Enable 3 stages of delay for signals
   *     0x8 | Enable 1 stage of delay for signals
   *     0x9 | Enable 2 stages of delay for signals
   *     0xA | Enable 2 stages of delay for signals
   *     0xB | Enable 3 stages of delay for signals
   *     0xC | Enable 2 stages of delay for signals
   *     0xD | Enable 3 stages of delay for signals
   *     0xE | Enable 3 stages of delay for signals
   *     0xF | Enable 4 stages of delay for signals
   * - Default: 0
   */
  int DxOutPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief DxOutPipeEn override variable.
   * - Set this to 1 if the DxOutPipeEn should be overriden via userInput.  else,
   * - dwc_ddrphy_phyinit_C_initPhyConfig.c will program a default
   * - Values:
   * - Min : 0
   * - Max : 1
   * - Default : 0
   */
  int DxOutPipeEnOvr;

  /**
   * @brief Override AlertNPipeEn.
   * - When user input AlertNPipeEnOvr is set, the value from this user input is used.
   * - Each bit set enables a stage of delay for the signals.
   * - Must be programmed as hex.
   * - If no override value provided, DfiClk frequency dependent value programmed.
   *   Value | Description
   *   ----- | -----------
   *     0x0 | No stages of delay for signals
   *     0x1 | Enable 1 stage of delay for signals
   *     0x2 | Enable 1 stage of delay for signals
   *     0x3 | Enable 2 stages of delay for signals
   *     0x4 | Enable 1 stage of delay for signals
   *     0x5 | Enable 2 stages of delay for signals
   *     0x6 | Enable 2 stages of delay for signals
   *     0x7 | Enable 3 stages of delay for signals
   *     0x8 | Enable 1 stage of delay for signals
   *     0x9 | Enable 2 stages of delay for signals
   *     0xA | Enable 2 stages of delay for signals
   *     0xB | Enable 3 stages of delay for signals
   *     0xC | Enable 2 stages of delay for signals
   *     0xD | Enable 3 stages of delay for signals
   *     0xE | Enable 3 stages of delay for signals
   *     0xF | Enable 4 stages of delay for signals
   * - Default: 0
   */
  int AlertNPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief AlertNPipeEn override variable.
   * - Set this to 1 if the AlertNPipeEnEn should be overriden via userInput.  else,
   * - dwc_ddrphy_phyinit_C_initPhyConfig.c will program a default
   * - Values:
   * - Min : 0
   * - Max : 1
   * - Default : 0
   */
  int AlertNPipeEnOvr;

  /**
   * @brief Override AcInPipeEn.
   * - When user input AcInPipeEnOvr is set, the value from this user input is used.
   * - Each bit set enables a stage of delay for the signals.
   * - Must be programmed as hex.
   * - If no override value provided, DfiClk frequency dependent value programmed.
   *   Value | Description
   *   ----- | -----------
   *     0x0 | No stages of delay for signals
   *     0x1 | Enable 1 stage of delay for signals
   *     0x2 | Enable 1 stage of delay for signals
   *     0x3 | Enable 2 stages of delay for signals
   *     0x4 | Enable 1 stage of delay for signals
   *     0x5 | Enable 2 stages of delay for signals
   *     0x6 | Enable 2 stages of delay for signals
   *     0x7 | Enable 3 stages of delay for signals
   *     0x8 | Enable 1 stage of delay for signals
   *     0x9 | Enable 2 stages of delay for signals
   *     0xA | Enable 2 stages of delay for signals
   *     0xB | Enable 3 stages of delay for signals
   *     0xC | Enable 2 stages of delay for signals
   *     0xD | Enable 3 stages of delay for signals
   *     0xE | Enable 3 stages of delay for signals
   *     0xF | Enable 4 stages of delay for signals
   * - Default: 0
   */
  int AcInPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief AcInPipeEn override variable.
   * - Set this to 1 if the AcInPipeEn should be overriden via userInput.  else,
   * - dwc_ddrphy_phyinit_C_initPhyConfig.c will program a default
   * - Values:
   * - Min : 0
   * - Max : 1
   * - Default : 0
   */
  int AcInPipeEnOvr;

  /**
   * @brief Override AcInPipeEn.
   * - When user input AcInPipeEnOvr is set, the value from this user input is used.
   * - Each bit set enables a stage of delay for the signals.
   * - Must be programmed as hex.
   * - If no override value provided, DfiClk frequency dependent value programmed.
   *   Value | Description
   *   ----- | -----------
   *     0x0 | tphy_rdlat DFI Timing parameter will not be increased
   *     0x1 | tphy_rdlat DFI Timing parameter will be increased by 1 DfiPubClk
   * - Default: 0
   */
  int DxRdPipeEn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief DxRdPipeEn override variable.
   * - Set this to 1 if the DxRdPipeEn should be overriden via userInput.  else,
   * - dwc_ddrphy_phyinit_C_initPhyConfig.c will program a default
   * - Values:
   * - Min : 0
   * - Max : 1
   * - Default : 0
   */
  int DxRdPipeEnOvr;

  /**
   * @brief DisablePclkDca.
   * - When this option is set Pclk duty cycle adjustment will not be performed.
   * - Values: 0x0, 0x1
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Enable Pclk Dca.
   *     0x1 | Disable Pclk Dca.
   * - Default: 0
   *
   */
  int DisablePclkDca;


  /**
   * @brief Selects the Rx DFE Dq tap
   * - Value specified here will be applied directly to HMDBYTE csr RxDFECtrlDq
   * - Values:
   *    Value | Description
   *    ----- | -----------
   *      0x0 | no DFE fxn
   *      0x1 | 001 - DFE 1 tap
   *      0x2 | 010 - DFE 2 tap
   *      0x5 | 101 - 2 tap DFE with Tap 1 forced to zero (for training)
   * - Default: 0
   */
  int RxDFECtrlDq[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Skip Copy of initial train data during skip-train frequency change.
   * - When set to 1:
   *   - Relock Only frequency change encoding must always be to current PStates and cannot be used to change freuqency.
   *   - PHY does not support frequency change to PStates with data rates < 1600Mbps.
   *   - Supported sequence:
   *   - 	P0 (retrain+relock) 	--> P0(skip_retrain) 	--> P1(retrain+relock) 	--> P1(skip_retrain)	--> P0 (retrain+relock)
   *   - 	[retrain T1 P0		    [use T1 Results] 	    [T2 P1]		    [use T2 results]	    [T3 P0]
   *   - 	P0 (retrain+relock)	--> P0(skip_retrain)	--> P0(retrain+relock)	--> P0(skip_retrain)
   *   - 	[retrain T1 P0] 	    [use T1 Results] 	   [T2 P0] 		    [use T2 Results]
   * - Values:
   *     Value | Description
   *     ----- | -----------
   *       0x0 | RelockOnly frequency change flash copies initial train data.
   *       0x1 | Relock frequency change will not change any PHY timing registers. relock only frequency changes will not copy target Pstate initial training data into PHY registers.
   */
  int SkipFlashCopy[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];


  /**
   * @brief Enables DBYTE RX DQ power down when in LP state with clocks stopped (LPDDR5 only)
   * - The value specified here is programmed directly into the LpRxDqPowerDown register.
   * - The LpDqPowerDnDly CSR will be programmed to generate a 5ns delay if this input is enabled.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | disabled
   *     0x1 | enabled
   * - Default: 0x0
   */
  int EnLpRxDqPowerDown;

  /**
   * @brief IMEM Loading Performance Enhancement
   * - "Quick load" mode for ICCM loading.  It is controlled by csrCCMWriteBypassEnable, csrHclkEn should be disabled before loading ICCM and re-enable it after.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | disabled
   *     0x1 | enabled
   * - Default: 0x1
   */
  int IMEMLoadPerfEn;

  /**
   * @brief DMEM Loading Performance Enhancement
   * - Performance Enhancement for writing out dccm data, it's controlled by csrStartDccmClear. This csr should be set to 1 then call function wait with 8200 DfiClks and set the csr back to 0 .
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | disabled
   *     0x1 | enabled
   * - Default: 0x1
   */
  int DMEMLoadPerfEn;

  /**
   * @brief Setting 4th bit of csrLpDqPhaseDisable
   * - This bit disables clock to PIPE. Disabling will increase wakeup time as a result.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | clock is enabled
   *     0x1 | clock is disabled
   * - Default: 0x0
   */
  int DfiLpPipeClkDisable;


  /**
   * @brief Setting PHYZCalPowerSaving 
   * - This bit will stop DfiClk when ZCal is not in use.
   * - This is not supported in all PUB versions; please check PUB databook section impedance calibration for more details.
   * - This control will program the ZCalStopClk CSR to save power when enabled.
   * - Note, when user_input_advanced.DisZCalOnDataRate=0, this userInput must be 0.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Power saving is disabled 
   *     0x1 | Power saving is enabled
   * - Default: 0x1
   */
  int PHYZCalPowerSaving;

  


  /**
   * @brief Disable function dwc_ddrphy_phyinit_chkAllLegalValues.
   * - This UI disable PHYINIT checker for all User Inputs if they are set with legal values.
   * - Disable if intentionally override UI with illegal value.
   * - Values:
   *   Value | Description
   *   ----- | -----------
   *     0x0 | Checker enabled
   *     0x1 | Checker disabled
   * - Default: 0x0
   */
  int DisCheckAllUserInputsLegalVal;

  /**
   * @brief Disable the checker that PHY Tx Impedance value must be the same as corresponding DRAM ODT (LPDDR5 only)
   * - Values:
   *   Value | Description
   *    ---- | ------
   *     0x0 | checker enabled
   *     0x1 | checker disabled
   * - Default: 1
   */
  int DisCheckImpTxRx[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Disable the checker that DRAM ODT msut be off if DVFSQ is enabled (LPDDR5 only)
   * - Values:
   *   Value | Description
   *    ---- | ------
   *     0x0 | checker enabled
   *     0x1 | checker disabled
   * - Default: 1
   */
  int DisCheckDvfsqDramOdt[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  /**
   * @brief Configure the VDD scaling mode if DVFS is enabled 
   * - Values:
   *   Value | Description
   *    ---- | ------
   *     0x0 |  No VDD scaling supported. All pstates use same VDD level (0.75v)
   *     0x1 |  VDD scaling supported during Pstate Change when memory access is paused i.e. after dfi_init_complete changes from 1 to 0 and all clock inputs stopped  
   *     0x2 |  VDD ramp up/down supported during background while memory access is ongoing 
   * - Default: 1
   */
  int CoreVddScalingMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];



  /**
   * @brief AC Quater Data Rate enable
   * - Used to enable AC Quarter Data Rate for LP5/5X. This is not supported in all PUB versions.
   * - Please check PUB databook Clocking Architecture and Configurations for more information,
   * - and to determine if it's supported.
   * - Values: 0, 1
   * - Default: 0
   */
  int AcQuarterDataRate;

 /**
   * @brief Gain control bits
   * - It is recommended to use default values for this CSR.
   * - Values:
   *   Value | Description
   *    ---- | -----------
   *     0x0 |  0dB
   *     0x7 |  -4dB
   *     0x3 |  -6dB
   *     0x5 |  -9dB
    - Default: 0x0
   */
  int RxGainCtrl;


  /**
  
   *   @brief Reserved for future use.
   * - Only default value is supported
   * - Values: 0
   * - Default: 0
  
   */
  int Lp5xDeassertDramReset;

  /**
  
   *   @brief Reserved for future use.
   * - Only default value is supported
   * - Min: 0
   * - Max: 0
   * - Default: 0
  
   */
  int Lp5xFwTinit3WaitTimex1000;

  /**
   * @brief Enables DTO.
   * - When dtoEn is enabled(0x1):
   *   -the DfiClkAcLnDis, PClkAcLnDis and AcLnDisable (AC) DTO pin is enabled.
   *   -TxImpedanceAC should be power down.
   * - Values: 0, 1
   * - Default: 0
   */
  int DtoEnable;

  /**
   * @brief Disable PIE ZCal when data rate <=3200Mbps
   * - Used to enable or disable if the PIE will enable/disable PIE ZCal FSM when data rate <=3200Mbps
   * - Values:
   *   Value | Description
   *    ---- | -----------
   *     0x0 | PIE will enable ZCal FSM for all data rates
   *     0x1 | PIE will disable ZCal FSM when data rate <=3200Mbps and force ZCal override codes
   * - Default: 1
   */
  int DisZCalOnDataRate;
  

  /**
   *  @brief program CSRs ACDlyScaleGatingDisable and NeverGateACDlyScaleValClk.
   *  * - Values:
   *   Value | Description
   *    ---- | -----------
   *     0x0 |  ACDlyScaleGatingDisable = 0x1 and NeverGateACDlyScaleValClk = 0x1
   *     0x1 |  ACDlyScaleGatingDisable = 0x0 and NeverGateACDlyScaleValClk = 0x0
   *  - Default: 0x0
   */
  int ACDlyScaleGating;


  /**
   *  @brief Reserved for future use.
   * - Only default value is supported.
   * - Values: 0
   * - Default: 0
   */
  int EnableSystemEcc;

    /**
   *  @brief Reserved for future use.
   * - Only default value is supported.
   * - Values: 0
   * - Default: 0
   */
  int DLEPKeyCode;

  /**
   *  @brief Skip PDE/PDX during Retrain Only / PMI.
   *  * - Values:
   *   Value | Description
   *    ---- | -----------
   *     0x0 |  PIE issues PDE/PDX during Retrain Only / PMI.
   *     0x1 |  PIE does NOT issue PDE/PDX during Retrain Only / PMI. This setting is allowed with JESD209-5C complaint devices only.
   *  - Default: 0x0
   */
  int SkipPwrDnInRetrain;

} user_input_advanced_t;

/** \brief Structure for user input simulation options (Optional)
 *
 * This structure can be programed with DRAM timing parameters for strict use
 * of the SkipTrain or SkipTrain + DevInit initialization method.  If executing
 * training firmware, this structure is not used.
 *
 */
typedef struct user_input_sim {



  /**
   * @brief Enter the value of tWCK2CK in ps (LPDDR5 only)
   * - Enter the value of tWCK2CK in ps
   * - Values:
   *   - Min: 0
   *   - Max: (TODO)
   * - Default: 0
   */
  int tWCK2CK;

  /**
   * @brief Enter the value of tWCK2DQI for LPDDR5 dram in ps (LPDDR5 only)
   * - Enter the value of tWCK2DQI for LPDDR5 dram in ps
   * - Values:
   *   - Min: 250
   *   - Max: 900
   * - Default: 500
   */
  int tWCK2DQI;

  /**
   * @brief Enter the value of tWCK2DQO in ps (LPDDR5 only)
   * - Enter the value of tWCK2DQO in ps
   * - Values:
   *   - Min: 0
   *   - Max: 1900
   * - Default: 1000
   */
  int tWCK2DQO;


  /**
   * @brief This parameter represents the internal PHY tDQS2DQ (in ps)
   * - The delay value (ps) specified here is used in simulations when the training firmware is skipped, and
   * - must match the delay from BP_DQS_T,_C in DIFF to _lcdl_rxclk in SE including the lcdl zerodelay.
   * - This delay must match what is programmed in the RTL logic model or annotated in gate level simulation.
   * - Values:
   *   - Min: 0
   *   - Max: 442
   * - Default: 250
   */
  int PHY_tDQS2DQ;

  /**
   * @brief This parameter represents the max number of LCDL steps
   * - This parameter represents the max number of LCDL steps
   * - The max number of LCDL steps specified here is used in simulations when the training firmware is skipped.
   * - Values:
   *   - Min: 0
   *   - Max: 511
   * - Default: 511
   */
  int LcdlNumSteps;

  /**
   * @brief This parameter represents the value of the steps in the LCDL
   * - This parameter represents the step size value of each delay element in the LCDL (multiplied by 10).
   * - The LCDL step size specified here is used in simulations when the training firmware is skipped.
   * - Note that this is the step size muliplied by 10 (e.g. 3.2ps step size x10 = 32)
   * - Values:
   *   - Min: 14
   *   - Max: 39
   * - Default: 30
   */
  int LcdlStepSizex10;

  /**
   * @brief This parameter represents the value of the LCDL's Tx Insertion delay
   * - This parameter represents the value of the LCDL's Tx Insertion delay.
   * - The LCDL Tx Insertion delay specified here is used in simulations when the training firmware is skipped.
   * - Values:
   *   - Min: 51
   *   - Max: 141
   * - Default: 85
   */
  int LcdlTxInsertionDelay;

  /**
   * @brief This parameter represents the value of the LCDL's Rx Insertion delay
   * - This parameter represents the value of the LCDL's Rx Insertion delay.
   * - The LCDL Rx Insertion delay specified here is used in simulations when the training firmware is skipped.
   * - Values:
   *   - Min: 39
   *   - Max: 104
   * - Default: 85
   */
  int LcdlRxInsertionDelay;

  /**
   * @brief Used for GLS+SDF to adjusting RxEnDly CSR. Allowed values for adjusting are between 100 and 200.
   * - Values:
   *   - Min: 100
   *   - Max: 200
   * - Default: 0
   */
  int RxEnDlyOffset_Reserved;

} user_input_sim_t;

#endif // _DWC_DDRPHY_PHYINIT_STRUCT_H_
/** @} */
