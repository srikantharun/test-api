/**
 * \file
 * \brief Implements Step C of initialization sequence
 *
 * This file contains the implementation of dwc_ddrphy_phyinit_C_initPhyConfig
 * function.
 *
 * \addtogroup SrcFunc
 * @{
 */
#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "string.h"
#include "dwc_ddrphy_phyinit_userCustom.h"
#include <errno.h>

/** \brief Implements Step C of initialization sequence
 *
 * This function programs majority of PHY Non-Pstate configuration registers based
 * on data input into PhyInit data structures.
 *
 * This function programs PHY configuration registers based on information
 * provided in the PhyInit data structures (userInputBasic, userInputAdvanced).
 * The user can overwrite the programming of this function by modifying
 * dwc_ddrphy_phyinit_userCustom_customPreTrain().  Please see
 * dwc_ddrphy_phyinit_struct.h for PhyInit data structure definition.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 *
 * List of registers programmed by this function:
 */

void dwc_ddrphy_phyinit_C_initPhyConfig(phyinit_config_t *phyctx)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  dwc_ddrphy_phyinit_cmnt("\n\n");
  dwc_ddrphy_phyinit_cmnt("##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt(" Step (C) Initialize PHY Configuration\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt(" Load the required PHY configuration registers for the appropriate mode and memory configuration\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n\n");

  uint16_t regData;

  dwc_ddrphy_phyinit_cmnt("[phyinit_C_initPhyConfig] Start of %s()\n", __func__);
  uint8_t NumAchn = pUserInputBasic->NumCh;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
  uint8_t NumDbyte = pRuntimeConfig->NumDbyte;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive; 
  
  uint8_t NumHmacPerChan = NUM_HMAC_PER_CHAN;
  uint8_t DtoEnable = pUserInputAdvanced->DtoEnable;

  /**
   * - Program MemResetL:
   *   - Description: Set ProtectMemReset=1 and drive BP_MEMRESET_L=0 by keeping MemResetLValue=0
   *   - Fields:
   *     - ProtectMemReset
   *   - Dependencies:
   *     - None
   */
  uint16_t MemResetL = csr_ProtectMemReset_MASK;
  dwc_ddrphy_phyinit_programMemResetL(phyctx, stepCFile, MemResetL);

  // Program the power up registers (ModeSel->PwrOkDlyCtrl->VshDacControl)
  dwc_ddrphy_phyinit_PowerUp(phyctx);


  /**
   * - Program LP5Mode:
   *   - Description: Select LP5 protocol
   *   - Dependencies:
   *     - user_input_basic.DramType
   */
  uint16_t isLP5Mode = 1;

    dwc_ddrphy_phyinit_cmnt("[%s] Programming LP5Mode to 0x%x\n", __func__,isLP5Mode);
    dwc_ddrphy_phyinit_io_write32((tMASTER | csr_LP5Mode_ADDR), isLP5Mode);

  /**
   * - Program DxOdtEn:
   *   - Description: DBYTE OdtEn controls
   *   - Fields:
   *     - OdtEnDq
   *     - OdtEnDqs
   *     - OdtEnWck
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  for (uint32_t byte=0; byte< NumDbyteActive; byte++) {
    uint32_t c_addr = byte * c1;
    dwc_ddrphy_phyinit_cmnt("[%s] Programming DBYTE%d DxOdtEn to 0x7ff\n",__func__, byte);
    dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_DxOdtEn_ADDR), 0x7ffu);
  }

  /**
   * - Protram TtcfControl:
   *   - Description: Pulse the TtcfForceSendAll bit to mark all registers in the TTCF interface as changed
   *   - Fields:
   *     - TtcfForceSendAll
   *   - Dependencies:
   *     - user_input_basic.DramType
   */
    for (int byte=0; byte<NumDbyte; byte++) {
      uint32_t c_addr = byte * c1;
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save TtcfForceSendAll to S3 list as this
      //       works by setting to "1" and then setting to  "0",and this CSR will be programmed as below in the dwc_ddrphy_phyinit_restore_sequence.c.
      dwc_ddrphy_phyinit_cmnt("[%s] Programming DBYTE%d. TtcfControl[TtcfForceSendAll] to 0x1\n", __func__, byte);
      dwc_ddrphy_phyinit_userCustom_io_write32((tDBYTE | c_addr | csr_TtcfControl_ADDR), (0x1u<<csr_TtcfForceSendAll_LSB));
      dwc_ddrphy_phyinit_cmnt("[%s] Programming DBYTE%d. TtcfControl[TtcfForceSendAll] to 0x0\n", __func__, byte);
      dwc_ddrphy_phyinit_userCustom_io_write32((tDBYTE | c_addr | csr_TtcfControl_ADDR), (0x0u<<csr_TtcfForceSendAll_LSB));
    }




 /**
  * - Program ZCalRate:
  *   - Description: Set ZCalInterval to user_input_advanced.CalInterval and trigger single iteration of calibration sequence if user_input_advanced.CalOnce is set
  *   - Fields:
  *     - ZCalInterval
  *     - ZCalOnce
  *   - Dependencies:
  *     - user_input_advanced.CalInterval
  *     - user_input_advanced.CalOnce
  */
  int ZCalRate;
  uint32_t ZCalInterval;
  uint32_t ZCalOnce;

  ZCalInterval = pUserInputAdvanced->CalInterval;
  ZCalOnce = pUserInputAdvanced->CalOnce;

  ZCalRate = (ZCalOnce << csr_ZCalOnce_LSB) | (ZCalInterval << csr_ZCalInterval_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalRate::ZCalInterval to 0x%x\n", __func__, ZCalInterval);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalRate::ZCalOnce to 0x%x\n", __func__, ZCalOnce);

  dwc_ddrphy_phyinit_io_write32((tZCAL | csr_ZCalRate_ADDR), ZCalRate);

  /**
   * - Program ZCalCompVref
   *   - Description: Set DAC digitial input to specify reference voltage for impedance calibration offset correction and DAC range selection
   *   - Fields:
   *     - ZCalCompVrefDAC
   *     - ZCalDACRangeSel
   *   - Dependencies for LPDDR4
   *     - user_input_basic.DramType
   *     - user_input_basic.Lp4xMode
   *     - mb1D[ps].MR3_A0[0:0]
   */
  uint16_t ZCalCompVrefDAC;
  uint16_t ZCalDACRangeSel;




    ZCalDACRangeSel = 0x0;
    ZCalCompVrefDAC = 0x26;


  uint16_t ZCalCompVref = (ZCalCompVrefDAC << csr_ZCalCompVrefDAC_LSB) | (ZCalDACRangeSel << csr_ZCalDACRangeSel_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalCompVref::ZCalCompVrefDAC to 0x%x\n", __func__, ZCalCompVrefDAC);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalCompVref::ZCalDACRangeSel to 0x%x\n", __func__, ZCalDACRangeSel);
  dwc_ddrphy_phyinit_io_write32((tHMZCAL | csr_ZCalCompVref_ADDR), ZCalCompVref);

  /**
   * - Program ZCalBaseCtrl
   *   - Description: Program impedance calibration TX mode control
   *   - Fields:
   *     - ZCalTxModeCtl
   *   - Dependencies of LPDDR4
   *     - user_input_basic.DramType
   *     - user_input_basic.Lp4xMode
   *     - mb1D[ps].MR3_A0[0:0]
   */
  uint16_t valZCalBasePU = 0x0;
  uint16_t valZCalBasePD = 0x0;
  uint16_t valTxModeCtl;
  uint16_t valWeakPullDown = 0x0;


    valTxModeCtl = (0x0u << 1);


  valTxModeCtl |= valWeakPullDown;

  uint16_t valZCalBaseCtrl = (valZCalBasePU << csr_ZCalBasePU_LSB) | (valZCalBasePD << csr_ZCalBasePD_LSB) | (valTxModeCtl << csr_ZCalTxModeCtl_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalBaseCtrl::ZCalBasePU to 0x%x\n", __func__, valZCalBasePU);
  dwc_ddrphy_phyinit_cmnt("%s] Programming ZCalBaseCtrl::ZCalBasePD to 0x%x\n", __func__, valZCalBasePD);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalBaseCtrl::ZCalTxModeCtl to 0x%x\n", __func__, valTxModeCtl);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalBaseCtrl to 0x%x\n", __func__, valZCalBaseCtrl);
  dwc_ddrphy_phyinit_io_write32((tZCAL | csr_ZCalBaseCtrl_ADDR), valZCalBaseCtrl);

  /**
   * - Program ZCalAnaSettlingTime
   *   - Description: Program the time ZCalana's comparator output takes to settle.
   *   - Fields:
   *     - ZCalAnaSettlingTime
   *   - Dependencies:
   *     - None
   */
  uint16_t valZCalAnaSettlingTime = 0x1d;
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalAnaSettlingTime to 0x%x\n", __func__, valZCalAnaSettlingTime);
  dwc_ddrphy_phyinit_io_write32((tZCAL | csr_ZCalAnaSettlingTime_ADDR), valZCalAnaSettlingTime);

  /**
   * - Program DFIPHYUPD0,1
   *   - Description: Program per AC channel DFIPhyUpd request timer counter (in DfiClk)
   *   - Fields:
   *     - DFIPHYUPDRESP0,1
   *     - DFIPHYUPDCNT0,1
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_advanced.DisablePhyUpdate
   */
  if (pUserInputAdvanced->DisablePhyUpdate != 0) {
    dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC DFIPHYUPD0 to 0x%x\n", __func__ , 0);
    dwc_ddrphy_phyinit_io_write32((tPPGC | c0 | csr_DFIPHYUPD0_ADDR), 0);
    if (NumAchn > 1) {
      dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC DFIPHYUPD1 to 0x%x\n", __func__ , 0);
      dwc_ddrphy_phyinit_io_write32((tPPGC | c0 | csr_DFIPHYUPD1_ADDR), 0);
    }
  }  


  /**
   * - Program DfiClkAcLnDis PClkAcLnDis, AcLnDisable (AC)
   *   - Description: Program per AC channel to disable DfiClk, Pclk, and lanes
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumRank
   *     - user_input_basic.NumRank_dfi0
   *     - user_input_basic.NumRank_dfi1
   */
  
  uint16_t data_ch0;
  uint16_t data_ch1;
  uint16_t dto_mask = (pUserInputAdvanced->DtoEnable == 0x1u) ? 0x0000u : 0x1000u;


  data_ch0 = (pUserInputBasic->NumRank == 2) ? (pUserInputBasic->NumRank_dfi0 == 1 ? 0x0A80 : 0x0880) : 0x0A80;
  data_ch1 = (NumAchnActive == 2) ? (pUserInputBasic->NumRank_dfi1 == 1 ? 0x0A80 : 0x0880) : 0x1fff;
   // Enable or disable the DTO pin based on userInput
  data_ch0 |= dto_mask;
  data_ch1 |= dto_mask;
  dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.DfiClkAcLnDis to 0x%x\n", __func__, 0, data_ch0);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.PClkAcLnDis to 0x%x\n", __func__, 0, data_ch0);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.AcLnDisable to 0x%x\n", __func__, 0, data_ch0);
  dwc_ddrphy_phyinit_io_write32((tAC | c0 | csr_PClkAcLnDis_ADDR), data_ch0);
  dwc_ddrphy_phyinit_io_write32((tAC | c0 | csr_DfiClkAcLnDis_ADDR), data_ch0);
  dwc_ddrphy_phyinit_io_write32((tAC | c0 | csr_AcLnDisable_ADDR), data_ch0);
  if (NumAchn > 1) {
    dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.DfiClkAcLnDis to 0x%x\n", __func__, 1, data_ch1);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.PClkAcLnDis to 0x%x\n", __func__, 1, data_ch1);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.AcLnDisable to 0x%x\n", __func__, 1, data_ch1);
    dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_PClkAcLnDis_ADDR), data_ch1);
    dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_DfiClkAcLnDis_ADDR), data_ch1);
    dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_AcLnDisable_ADDR), data_ch1);
    }



  /**
   * - Program ArcPmuEccCtl (PMU ECC)
   *   - Description: Set ARC error protection hardware control
   *   - Dependencies:
   *     - user_input_advanced.DisablePmuEcc
   */
  uint16_t disableEcc = pUserInputAdvanced->DisablePmuEcc;

  if (disableEcc == 1) {
    // ArcPmuEccCtl[4:0] = 0x1F
    // ArcPmuEccCtl[4] Engages override.  When this bit is set, [3:0] have the functions listed below
    // ArcPmuEccCtl[3] DCCM exception disable.
    // ArcPmuEccCtl[2] ICCM exception disable.
    // ArcPmuEccCtl[1] DCCM ECC disable.
    // ArcPmuEccCtl[0] ICCM ECC Disable
    dwc_ddrphy_phyinit_cmnt("[%s] Programming ArcPmuEccCtl to 0x%x\n", __func__, 0x001F);
    dwc_ddrphy_phyinit_io_write32((tDRTUB | csr_ArcPmuEccCtl_ADDR), 0x001F);

    dwc_ddrphy_phyinit_cmnt("[%s] Programming PhyInterruptEnable::PhyEccEn to 0x0\n",__func__);
    dwc_ddrphy_phyinit_io_write32((tPPGC | csr_PhyInterruptEnable_ADDR), (0UL << csr_PhyEccEn_LSB));
  }

  /**
   * - Program PptCtlStatic
   *   - Description: Program controls for PPT drift compensation
   *   - Fields:
   *     - PptEnDqs2DqTg0
   *     - PptEnDqs2DqTg1
   *     - PptRxEnTg0
   *     - PptRxEnTg1
   *     - PptEnRxEnBackOff
   *     - DOCByteSelTg0
   *     - DOCByteSelTg1
   *     - PptEnWck2Dq0Tg0
   *     - PptEnWck2Dq0Tg1
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.DramDataWidth
   *     - user_input_advanced.DramByteSwap
   *     - mb1D[ps].X8Mode
   *     - user_input_advanced.DisableRetraining
   *     - user_input_basic.NumRank_dfi0
   *     - user_input_basic.NumRank_dfi1
   */

  for (uint32_t byte = 0; byte < NumDbyteActive; byte++) { // Each Dbyte could have a different configuration.
    uint16_t PptEnRxEnBackOff;

      PptEnRxEnBackOff = 0x2;

    uint16_t DOCByteTg0, DOCByteTg1;

    uint32_t c_addr = byte * c1;
    if (pUserInputBasic->DramDataWidth == 8) {
      if (mb1D[pUserInputBasic->FirstPState].X8Mode == 0xf) {
        // all ranks are bytemode
        DOCByteTg0 = 0x0;
        DOCByteTg1 = 0x0;
      } else if (mb1D[pUserInputBasic->FirstPState].X8Mode == 0xa) {
       	DOCByteTg1 = 0x0;
        if (byte % 2 == 0) {
     	  DOCByteTg0 = 0x1u & ((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
   	} else {
      	  DOCByteTg0 = 0x1u & ~((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
        }
      } else if (mb1D[pUserInputBasic->FirstPState].X8Mode == 0x5) {
       	DOCByteTg0 = 0x0;
        if (byte % 2 == 0) {
     	  DOCByteTg1 = 0x1u & ((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
   	} else {
      	  DOCByteTg1 = 0x1u & ~((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
        }
      } else {
        dwc_ddrphy_phyinit_assert(0, "[%s] Unexpected value for mb1D[p0].X8Mode == %d", __func__, mb1D[pUserInputBasic->FirstPState].X8Mode);
      }
    } else if (byte % 2 == 0) {
      DOCByteTg0 = 0x1u & ((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
      DOCByteTg1 = 0x1u & ((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
    } else {
      DOCByteTg0 = 0x1u & ~((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
      DOCByteTg1 = 0x1u & ~((uint32_t)(pUserInputAdvanced->DramByteSwap) >> byte);
    }

    uint32_t PptRxEnTg0;
    uint32_t PptRxEnTg1;
    uint32_t PptEnTg1;

    PptRxEnTg0 = (pUserInputAdvanced->DisableRetraining == 1) ? 0x0 : 0x1;
    PptRxEnTg1 = (pUserInputAdvanced->DisableRetraining == 1) ? 0x0 : (((pUserInputBasic->NumRank_dfi0 == 2) || (pUserInputBasic->NumRank_dfi1 == 2)) ? 0x1 : 0x0);
    PptEnTg1 = (((pUserInputBasic->NumRank_dfi0 == 2) || (pUserInputBasic->NumRank_dfi1 == 2)) ? 0x1 : 0x0);
    regData = (0x1u << csr_PptEnDqs2DqTg0_LSB |
           PptEnTg1 << csr_PptEnDqs2DqTg1_LSB |
           PptRxEnTg0 << csr_PptEnRxEnDlyTg0_LSB |
           PptRxEnTg1 << csr_PptEnRxEnDlyTg1_LSB |
           PptEnRxEnBackOff << csr_PptEnRxEnBackOff_LSB | DOCByteTg0 << csr_DOCByteSelTg0_LSB | DOCByteTg1 << csr_DOCByteSelTg1_LSB);

    uint8_t PptEnWck2DqoTg0 = 0x1;
    uint8_t PptEnWck2DqoTg1 = PptEnTg1;
      regData |= PptEnWck2DqoTg0 << csr_PptEnWck2DqoTg0_LSB | PptEnWck2DqoTg1 << csr_PptEnWck2DqoTg1_LSB;
    dwc_ddrphy_phyinit_cmnt("[%s] Programming PptCtlStatic to 0x%x\n", __func__, regData);
    dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_PptCtlStatic_ADDR), regData);
  }


  /**
   * - Program DfiXlat based on Pll Bypass Input
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.PllBypass
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Programming DfiFreqXlat*\n", __func__);

  uint32_t xlat[64]    = {0x0};   // For DfiFreqXlat CSR
  uint32_t xlat_dp[64] = {0x0};   // For DfiFreqXlatDestPState CSR
  uint32_t idx;

  int xlatNumPs = DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;

  for (int ps=0; ps < xlatNumPs; ps++) {
    uint16_t freqThreshold;
    uint16_t NoRDQS = 0x0;


  /**
   * - Program DfiFreqXlat[n] and DfiFreqXlatDestPState[n]:
   *   - Description: Set up the DFI frequency translation table to translate dfi_frequence[4:0] values to PIE start vectors and destination PStates
   *   - Fields:
   *     - DfiFreqXlatVal[n+0]
   *     - DfiFreqXlatVal[n+1]
   *     - DfiFreqXlatVal[n+2]
   *     - DfiFreqXlatVal[n+3]
   *     - DfiFreqXlatDestPStateVal[n+0]
   *     - DfiFreqXlatDestPStateVal[n+1]
   *     - DfiFreqXlatDestPStateVal[n+2]
   *     - DfiFreqXlatDestPStateVal[n+3]
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.CfgPStates
   *     - user_input_basic.DfiFreqRatio
   *     - mb1D[ps].MR20_A0[1:0]
   */

      freqThreshold = pUserInputBasic->DfiFreqRatio[ps] == 1 ? 400 : 200;
      NoRDQS = ((mb1D[ps].MR20_A0 & 0x3u) == 0x0);


    if (((uint32_t)(pUserInputBasic->CfgPStates) & (0x1u << (uint32_t)(ps))) == 0) {

      continue;
    }

    idx = ps;

    // Program DfiFreqXlat xlat[] array for each pstate
    xlat[idx] = ((pUserInputBasic->Frequency[ps]<freqThreshold) ||
                      (pUserInputBasic->Frequency[ps]>=freqThreshold && (NoRDQS != 0))) ? 0x5 : 0x1;
    xlat[4  + idx] = 0x2;
    xlat[8  + idx] = 0x7;
    xlat[16 + idx] = 0x5;

    // Program DfiFreqXlatDestPstate xlat_dp[] array for each pstate
    xlat_dp[    idx] = idx;
    xlat_dp[4 + idx] = idx;
    xlat_dp[8 + idx] = idx;
    xlat_dp[16 + idx] = idx;
  }

  // Program fixed DfiFreqXlat entries
  xlat[12] = 0x4;     // Retrain Only
  xlat[13] = 0x3;     // LP2 Enter/Exit
  xlat[31] = 0xF;     // LP3 Enter

  // Program fixed DfiFreqXlatDestPstate entries
  xlat_dp[12] = 0x5;  // Retrain Only
  xlat_dp[13] = 0x5;  // LP2 Enter/Exit
  xlat_dp[31] = 0x5;  // LP3 Enter

  uint16_t loopVector;
  uint16_t PhyMstrPMValOverride = 0x4;
  uint16_t Seq0BFixedAddrBits = 0xfu << csr_Seq0BChipletBits_LSB;

  for (loopVector = 0; loopVector < 16; loopVector++) {
    int xlatIdx = loopVector * 4;

    // DfiFreqXlat
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat[%d]=%d\n", __func__, xlatIdx,     xlat[xlatIdx]);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat[%d]=%d\n", __func__, xlatIdx + 1, xlat[xlatIdx + 1]);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat[%d]=%d\n", __func__, xlatIdx + 2, xlat[xlatIdx + 2]);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat[%d]=%d\n", __func__, xlatIdx + 3, xlat[xlatIdx + 3]);

    regData = (xlat[xlatIdx + 3] << 12) | (xlat[xlatIdx + 2] << 8) | (xlat[xlatIdx + 1] << 4) | (xlat[xlatIdx]);
    if (regData != 0x0) {
      dwc_ddrphy_phyinit_io_write32((c0 | tDRTUB | (csr_DfiFreqXlat0_ADDR + loopVector)), regData);
    }

    // DfiFreqXlatDestPstate
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat_dp[%d]=%d\n", __func__, xlatIdx,     xlat_dp[xlatIdx]);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat_dp[%d]=%d\n", __func__, xlatIdx + 1, xlat_dp[xlatIdx + 1]);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat_dp[%d]=%d\n", __func__, xlatIdx + 2, xlat_dp[xlatIdx + 2]);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming xlat_dp[%d]=%d\n", __func__, xlatIdx + 3, xlat_dp[xlatIdx + 3]);

    regData = (xlat_dp[xlatIdx + 3] << 9) | (xlat_dp[xlatIdx + 2] << 6) | (xlat_dp[xlatIdx + 1] << 3) | (xlat_dp[xlatIdx]);
    if (regData != 0x0) {
      dwc_ddrphy_phyinit_io_write32((c0 | tINITENG | (csr_DfiFreqXlatDestPState0_ADDR + loopVector)), regData);
    }
  }

  /**
   * - Program PhyMstrPMValOverride:
   *   - Description: Program PMI ddrPmVal to be used by the PIE for PMI (same ddrPmVal as Retrain Only)
   *   - Dependencies:
   *     - None
   */
  dwc_ddrphy_phyinit_io_write32((c0 | tINITENG | csr_PhyMstrPMValOverride_ADDR), PhyMstrPMValOverride);

  /**
   * - Program Seq0BFixedAddrBits:
   *   - Description: Program PIE CSR address chiplet bits to be broadcast (0xF)
   *   - Fields:
   *     - Seq0BChipletBits
   *   - Dependencies:
   *     - None
   */
  dwc_ddrphy_phyinit_io_write32(c0 | tINITENG | (csr_Seq0BFixedAddrBits_ADDR), Seq0BFixedAddrBits);
  /**
   * - Program DbyteMiscMode
   *   - Description: Disable DBYTE module, see function dwc_ddrphy_phyinit_IsDbyteDisabled() to determine which DBYTEs are turned off completely based on PHY configuration
   *   - Fields:
   *     - DByteDisable
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */

  uint16_t pubDbyteDis = 0x0u;
  for (uint32_t byte = 0; byte < NumDbyte; byte++) { // for each dbyte
    uint32_t c_addr = byte * c1;
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte)) {
      pubDbyteDis |= (0x1u << byte);
      dwc_ddrphy_phyinit_cmnt("[%s] Programming DBYTE%d.DbyteMiscMode to disable Dbyte\n", __func__, byte);
      dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_DbyteMiscMode_ADDR), 0x1u << csr_DByteDisable_LSB);
    }
  }

  /**
   * - Program PubDbyteDisable:
   *   - Description: Power down unused DBYTE's
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */

     // Note: S3 waiver
     //       Purposely using userCustom_io_write32(), do not want to save PubDbyteDisable to S3 list as if this
     //       CSR restored prior to DBYTE CSR, DBYTE will not be restored. 
     //       This CSR will be restored at the end of restore sequence 
     //       dwc_ddrphy_phyinit_restore_sequence.c
     dwc_ddrphy_phyinit_cmnt("[%s] Programming MASTER.PubDbyteDisable to 0x%x\n", __func__, pubDbyteDis);
     dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_PubDbyteDisable_ADDR), pubDbyteDis);


  /**
   * - Program RxModeX8Sel:
   *   - Description: Program X8 mode enable (DX4 RxModeX8Sel=0, DX5 RxModeX8Sel=1)
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  for (uint32_t byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr0 = ((byte*2) & 0xfu) * c1;
    uint32_t c_addr1 = (((byte*2)+1) & 0xfu) * c1;

    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE %d DX4 RxModeX8Sel to 0x%x\n", __func__, byte, 0);
    dwc_ddrphy_phyinit_io_write32((tHMDBYTE | c_addr0 | csr_RxModeX8Sel_ADDR), 0);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE %d DX5 RxModeX8Sel to 0x%x\n", __func__, byte, 1);
    dwc_ddrphy_phyinit_io_write32((tHMDBYTE | c_addr1 | csr_RxModeX8Sel_ADDR), 1);
  }


  /**
   * - Program PclkDCAClkGaterEnAC PclkDCAClkGaterEnDB:
   *   - Description: Program Clock to DCA FSM controls to 0
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  for (int acx=0; acx<NumAchnActive; acx++) {
    for (int hmac=0; hmac<NumHmacPerChan; hmac++) {
      uint32_t c_addr = (hmac+acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt ("[%s] Programming ACX%d HMAC%d Instance%d PclkDCAClkGaterEnAC/DB to 0x%x\n", __func__, acx, hmac, instance, 0);
      dwc_ddrphy_phyinit_io_write32((tHMAC | c_addr | csr_PclkDCAClkGaterEnAC_ADDR), 0);
      _PROG_DTO(DtoEnable, acx, hmac, "PclkDCAClkGaterEnAC/DB", (tHMAC | c14 | csr_PclkDCAClkGaterEnAC_ADDR), 0)
    }
  }
    for (int byte = 0; byte < NumDbyteActive; byte++) {
     uint32_t c_addr = byte * c1;
     dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_PclkDCAClkGaterEnDB_ADDR), 0);
	}


  /**
   * - Program PclkDCANextFineOnCoarseAC PclkDCANextFineOnCoarseDB:
   *   - Description:
   *   - Fields:
   *     - PclkDCACoarseIncFineURAC
   *     - PclkDCACoarseDecFineURAC
   *     - PclkDCACoarseIncFineLLAC
   *     - PclkDCACoarseDecFineLLAC
   *     - PclkDCACoarseIncFineURDB
   *     - PclkDCACoarseDecFineURDB
   *     - PclkDCACoarseIncFineLLDB
   *     - PclkDCACoarseDecFineLLDB
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  /*
   * - Program PclkDCANextFineOnCoarseAC/DB
   */

  if (pUserInputAdvanced->DisablePclkDca == 0) {
    uint16_t PclkDCANextFineOnCoarse = 0xee66;

    dwc_ddrphy_phyinit_cmnt("[%s] Programming PclkDCANextFineOnCoarseAC/DB Full Search to 0x%x\n", __func__, PclkDCANextFineOnCoarse);
    for (uint32_t achn = 0; achn < NumAchnActive; achn++) {
      uint32_t c_addr = achn * c1;
     dwc_ddrphy_phyinit_io_write32((tAC | c_addr | csr_PclkDCANextFineOnCoarseAC_ADDR), PclkDCANextFineOnCoarse);
    }

    for (uint32_t byte = 0; byte < NumDbyteActive; byte++) {
      uint32_t c_addr = byte * c1;
      dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_PclkDCANextFineOnCoarseDB_ADDR), PclkDCANextFineOnCoarse);
    }
  }

  //Configuring AsyncAcTxEn/AsyncAcTxEnD5 such as to be enabled only for CS signals (i.e. to be cleared for CA and CK signals).
  /**
   * - Program AsyncAcTxEn:
   *   - Description: Program TxEnable bits for Async Flyover
   *   - Dependencies:
   *     - user_input_basic.NumCh
   */
  // clearing the channel 1 asyncactxen value
  int AsyncAcTxEn = 0x0000;
  if ((NumAchn > 1) && (NumAchnActive == 1)) {
    AsyncAcTxEn = 0x0000;
    dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.AsyncAcTxEn to 0x%x\n", __func__, 1, AsyncAcTxEn);
    dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_AsyncAcTxEn_ADDR), AsyncAcTxEn);
  }


  /**
   * - Program AsyncAcTxMode:
   *   - Description: Enables Async Flyover for all lanes of the AC
   *   - Dependencies:
   *     - user_input_basic.NumCh
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.AsyncAcTxMode to 0x%x\n", __func__, 0, 0x3fff);
  dwc_ddrphy_phyinit_io_write32((tAC | c0 | csr_AsyncAcTxMode_ADDR), 0x3fff);

  if (NumAchn > 1) {
    dwc_ddrphy_phyinit_cmnt("[%s] Programming AC%d.AsyncAcTxMode to 0x%x\n", __func__, 1, 0x3fff);
    dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_AsyncAcTxMode_ADDR), 0x3fff);
  }


  /**
   * - Program AsyncDbyteTxMode AsyncDbyteRxMode:
   *   - Description: Enables Async Flyover for all lanes of DBYTE for TX and RX
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t AsyncDbyteTxMode = 0x1fff;
  uint16_t AsyncDbyteRxMode = 0x7ff;

  // Set DBYTE's Async path
  for (int byte = 0; byte < NumDbyte; byte++) {
    uint32_t c_addr = byte * c1;

    dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_AsyncDbyteTxMode_ADDR), AsyncDbyteTxMode);
    dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_AsyncDbyteRxMode_ADDR), AsyncDbyteRxMode);
  }


  /**
   * - Program LpDqPhaseDisable:
   *   - Description: Disables master clock when in LP state with clocks stopped
   *   - Dependencies:
   *     - user_input_advanced.DfiLpPipeClkDisable
   */
  uint16_t LpDqPhaseDisable_data = (pUserInputAdvanced->DfiLpPipeClkDisable == 1) ? 0x1f : 0xf;
  dwc_ddrphy_phyinit_cmnt("[%s] Programming LpDqPhaseDisable to 0x%x\n", __func__, LpDqPhaseDisable_data);
  dwc_ddrphy_phyinit_io_write32((tMASTER | csr_LpDqPhaseDisable_ADDR), LpDqPhaseDisable_data);



  /**
   * - Program PipeNetDis:
   *   - Description: Power saving feature where all *PipeEn area lways 0, set this to 1 to turn off clock network to mux flops in the PIPE block
   *   - Dependencies:
   *     - user_input_basic.CfgPStates
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_advanced.AcInPipeEnOvr
   *     - user_input_advanced.DxInPipeEnOvr
   *     - user_input_advanced.DxOutPipeEnOvr
   *     - user_input_advanced.AlertNPipeEnOvr
  */
  uint16_t PipeNetDis = 1;
  for (uint32_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    uint16_t DfiFreq=pRuntimeConfig->DfiFreq[pstate];

    if (((uint32_t)(pUserInputBasic->CfgPStates) & (0x1u << pstate)) == 0) {
      continue;
    }
    if ((DfiFreq > 800) || (pUserInputAdvanced->AcInPipeEnOvr == 1) || (pUserInputAdvanced->DxInPipeEnOvr == 1) || (pUserInputAdvanced->DxOutPipeEnOvr == 1) || (pUserInputAdvanced->AlertNPipeEnOvr == 1)) {
      PipeNetDis = 0;
    }
  }
  dwc_ddrphy_phyinit_cmnt("[%s] Programming PipeNetDis to 0x%x\n", __func__, PipeNetDis);
  dwc_ddrphy_phyinit_io_write32((tMASTER | csr_PipeNetDis_ADDR), PipeNetDis);


  /**
   * - Program RxPowerDownLightEn LpDqPowerDnEn:
   *   - Description: Program RxPowerDownLight feature in HMDBYTE and enable DBYTE power down when in LP with clocks stopped
   *   - Dependencies:
   *     - user_input_advanced.EnLpRxDqPowerDown
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t RxPowerDownLightEn_data = 0x1;

  if (pUserInputAdvanced->EnLpRxDqPowerDown == 1) {
    for (uint32_t byte = 0; byte < NumDbyteActive; byte++) {
      unsigned c_addr0 = ((byte*2) & 0xfu)  * c1;
      unsigned c_addr1 = (((byte*2)+1) & 0xfu) * c1;

      dwc_ddrphy_phyinit_cmnt ("[%s] Programming HMDBYTE%d RxPowerDownLightEn to 0x%x\n", __func__, (byte*2), RxPowerDownLightEn_data);
      dwc_ddrphy_phyinit_io_write32((tHMDBYTE | c_addr0 | csr_RxPowerDownLightEn_ADDR), RxPowerDownLightEn_data);

      dwc_ddrphy_phyinit_cmnt ("[%s] Programming HMDBYTE%d RxPowerDownLightEn to 0x%x\n", __func__, ((byte*2)+1), RxPowerDownLightEn_data);
      dwc_ddrphy_phyinit_io_write32((tHMDBYTE | c_addr1 | csr_RxPowerDownLightEn_ADDR), RxPowerDownLightEn_data);
    }
  }



  uint16_t RxOffsetEn = 1;
  uint16_t RxGainCtrl =  (((uint32_t)(pUserInputAdvanced->RxGainCtrl) << csr_RxGainCtrl_LSB) & csr_RxGainCtrl_MASK) | ((RxOffsetEn << csr_RxOffsetEn_LSB) & csr_RxOffsetEn_MASK);
  for (uint32_t byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr0 = ((byte*2) & 0xfu)  * c1;
    unsigned c_addr1 = (((byte*2)+1) & 0xfu) * c1;

    dwc_ddrphy_phyinit_cmnt ("[%s] Programming HMDBYTE%d RxGainCtrl to 0x%x\n", __func__, (byte*2), RxGainCtrl);
    dwc_ddrphy_phyinit_io_write32((tHMDBYTE | c_addr0 | csr_RxMiscCtl_ADDR), RxGainCtrl);

    dwc_ddrphy_phyinit_cmnt ("[%s] Programming HMDBYTE%d RxGainCtrl to 0x%x\n", __func__, ((byte*2)+1), RxGainCtrl);
    dwc_ddrphy_phyinit_io_write32((tHMDBYTE | c_addr1 | csr_RxMiscCtl_ADDR), RxGainCtrl);
  }



     /* - Program ACDlyScaleGatingDisable and NeverGateACDlyScaleValClk
     *   - Dependencies:
     *     - user_input_advanced.ACDlyScaleGating
     */
     int ACDlyScaleGatingDisable = (pUserInputAdvanced->ACDlyScaleGating == 0x0) ? 0x1 : 0x0;
     for (int acx=0; acx<NumAchnActive; acx++) {
       uint32_t c_addr = acx * c1;
       dwc_ddrphy_phyinit_cmnt("[%s] Programming ACDlyScaleGatingDisable AC%d to 0x%x\n", __func__, acx, ACDlyScaleGatingDisable);
       dwc_ddrphy_phyinit_io_write32((tAC | c_addr | csr_ACDlyScaleGatingDisable_ADDR), ACDlyScaleGatingDisable);
       for (int hmac=0; hmac<NumHmacPerChan; hmac++) {
         c_addr = (hmac + acx*NumHmacPerChan)*c1;
         int instance = hmac + acx*NumHmacPerChan;

         _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)

         dwc_ddrphy_phyinit_cmnt("[%s] Programming ACX%d HMAC%d Instance%d to NeverGateACDlyScaleValClk 0x%x\n",  __func__, acx, hmac, instance, ACDlyScaleGatingDisable);
         dwc_ddrphy_phyinit_io_write32((tHMAC | c_addr | csr_NeverGateACDlyScaleValClk_ADDR), ACDlyScaleGatingDisable);
         _PROG_DTO(DtoEnable, acx, hmac, "NeverGateACDlyScaleValClk",(tHMAC | c14 | csr_NeverGateACDlyScaleValClk_ADDR), ACDlyScaleGatingDisable)
       }
     }
  
  // Disable DFI channels based on userInput
  dwc_ddrphy_phyinit_programDfiMode(phyctx, disableDfiMode);
  dwc_ddrphy_phyinit_cmnt("[phyinit_C_initPhyConfig] End of %s()\n", __func__);
}
// End of dwc_ddrphy_phyinit_C_initPhyConfig()

/** \brief This function programs MemResetL csr
 *
 * This utility function is used to program MemResetL csr value based on the value of 16 bit
 * MEMResetL value
 *
 * \param phyctx Data structure to hold user-defined parameters
 * \param filetype enumerated data structure which lists in which file the function was used
 * \param MemResetL 16 bit value indicating whether BP_MEMRESET_L is logic LOW / logic HIGH
 *
 * \return void
 */
void dwc_ddrphy_phyinit_programMemResetL(phyinit_config_t *phyctx, fileType_t fileType, uint16_t MemResetL)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint8_t NumAchn = pUserInputBasic->NumCh;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;

  if(fileType == progCsrFile) {    
    if (pRuntimeConfig->firstTrainedPState == 1) {
      dwc_ddrphy_phyinit_cmnt(" [%s] Programming MemResetL AC %dto 0x%x\n", __func__,0, MemResetL);
      dwc_ddrphy_phyinit_io_write32((tAC | c0 | csr_MemResetL_ADDR), MemResetL);
      if (NumAchn > 1) {
        dwc_ddrphy_phyinit_cmnt(" [%s] Programming MemResetL AC %dto 0x%x\n", __func__,1, MemResetL);
        dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_MemResetL_ADDR), MemResetL);
      }
    }
  } else if (fileType == stepCFile) {    
    for (uint32_t achn = 0; achn < NumAchnActive; achn++) {
      uint32_t c_addr = achn * c1;
      dwc_ddrphy_phyinit_cmnt("[%s] Programming MemResetL AC%d to 0x%x\n", __func__, achn, MemResetL);
      dwc_ddrphy_phyinit_io_write32((tAC | c_addr | csr_MemResetL_ADDR), MemResetL);
    }
  } else {
    dwc_ddrphy_phyinit_cmnt("[%s] Incorrect file type selected for programming MEMResetL\n", __func__);
  }
}

/** \brief Implements Step C in Pstate Loop of initialization sequence
 *
 * This function programs majority of PHY Pstate configuration registers based
 * on data input into PhyInit data structures.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 *
 * List of registers programmed by this function:
 */
// coverity[misra_c_2012_rule_5_1_violation]
void dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(phyinit_config_t *phyctx)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

  uint8_t pstate = pRuntimeConfig->curPState;
  uint32_t tck_ps = pRuntimeConfig->tck_ps[pstate];
  dwc_ddrphy_phyinit_cmnt("Start of %s(), PState=%d, tck_ps=%dps\n",  __func__, pstate,tck_ps);

  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  uint16_t ratio = 1u << (uint32_t)(pUserInputBasic->DfiFreqRatio[pstate]);

  uint32_t p_addr = (uint32_t) pstate << 20;

  uint16_t freq = pUserInputBasic->Frequency[pstate];
  uint8_t NumHmacPerChan = NUM_HMAC_PER_CHAN;
  uint8_t DtoEnable = pUserInputAdvanced->DtoEnable;

  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
  uint8_t NumDbyte = pRuntimeConfig->NumDbyte;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive; 
  uint8_t NumAchn = pUserInputBasic->NumCh;
  //  Data Rate in JEDEC
  uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
  uint16_t regData;
  uint16_t freqThreshold;

  // enable DFI channels 
  dwc_ddrphy_phyinit_programDfiMode(phyctx, enableDfiMode);

  // Calculate frequency threshold for PPT disable

    freqThreshold = pUserInputBasic->DfiFreqRatio[pstate] == 1 ? 400 : 200;
    
    //Strobeless Mode (NoRDQS) is used for LPDDR5x/5 only
    uint16_t NoRDQS = ((mb1D[pstate].MR20_A0 & 0x3u) == 0x0);


  /**
   * - Program PState:
   *   - Description: Program PState CSR
   *   - Dependencies:
   *     - runtime_config.curPState
   */
    
     uint16_t curPState = pRuntimeConfig->curPState;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, programming PState = %d\n", __func__, pRuntimeConfig->curPState, curPState);
     // Note: S3 waiver
     //       Purposely using userCustom_io_write32(), do not want to save PState to S3 list as this
     //       CSR will be controlled depend on the dfi_frequency when retention exit.PHY must Enter and Exit the same PState for LP3.
    dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | c0 | csr_PState_ADDR), curPState);


  /**
   * - Program Seq0BGPR1:
   *   - Description: Program Seq0BGPR1 CSR with information PIE uses when executing
   *     - Seq0BGPR1[0:0] = PllBypass enable/disable for PIE
   *     - Seq0BGPR1[1:1] = DisableRetraining enable/disable for PIE
   *     - Seq0BGPR1[2:2] = SkipFlashCopy enable/disable for PIE
   *     - Seq0BGPR1[3:3] = DSM or Self-Refresh + Power Down Mode for LP3 for PIE (LPDDR5x/5 only)
   *     - Seq0BGPR1[4:4] = DisablePclkDca enable/disable for PIE
   *     - Seq0BGPR1[5:5] = PclkDca Calibration type based on DataRate for PIE
   *     - Seq0BGPR1[6:6] = RFU
   *     - Seq0BGPR1[7:7] = 2nd channel active enable for PIE
   *     - Seq0BGPR1[8:8] = snoop WA enable/disable
   *     - Seq0BGPR1[9:9] = Disable ZCal FSM for data rate <= 3200Mbps (LPDDR5X/5/4X only), note if csrZQCalCodeOvrEnP{U,D}=1'b to override
   *     -                  calibration codes, this bit must be cleared in dwc_ddrphy_phyinit_userCustom_customPostTrain() funciton
   *     - Seq0BGPR1[10:10] = 1 when data rate <= 4267Mbps, 0 when data rate > 4267Mbps
   *     - Seq0BGPR1[11:11] = Strobeless mode enabled for PIE (LPDDR5X/5 only)
   *     - Seq0BGPR1[12:12] = CoreVddScalingMode is 2 or not (LPDDR5/4 Only)
   *     - Seq0BGPR1[14:13] = Data rate range for PIE (LPDDR5x/5 only); 'b00: data rate <= 1600 Mbps; 'b01: 1600 Mbps < data rate <= 3200 Mbps; 'b10: data rate > 3200 Mbps
   *     - Seq0BGPR1[15:15] = userInput->DisZCalOnDataRate (LP5X STDPROD only)
   *   - Dependencies:
   *     - user_input_basic.PllBypass
   *     - user_input_basic.Frequency
   *     - user_input_basic.DramType
   *     - user_input_advanced.SkipFlashCopy
   *     - user_input_advanced.DisableRetraining
   *     - user_input_advanced.DisablePclkDca
   *     - mb1D[ps].MR11_A0[6:4]
   *     - mb1D[ps].MR17_A0[5:5]
   *     - user_input_basic.NumCh
   *     - user_input_advanced.CoreVddScalingMode
   */
  uint16_t Seq0BGPR1 = DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;

  //Bit 0 - PllBypass
  Seq0BGPR1 |= (pUserInputBasic->PllBypass[pstate] == 1) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT0_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;                 
  
  //Bit 1 - DisableRetraining
  Seq0BGPR1 |= ((pUserInputAdvanced->DisableRetraining == 1) || (pUserInputBasic->Frequency[pstate] < freqThreshold)) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT1_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;                                                        

  //Bit 4 - DisablePclkDCA
  Seq0BGPR1 |= ((pUserInputAdvanced->DisablePclkDca == 1) || (DataRateMbps <= DWC_DDRPHY_PHYINIT_PCLKDCA_EN_THRESHOLD)) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT4_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;                                                           
  
  //Bit 5 - PclkDca Calibration type based on data rate
  Seq0BGPR1 |= (DataRateMbps > DWC_DDRPHY_PHYINIT_PCLKDCA_EN_THRESHOLD) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT5_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;          
  
  //Bit 7 - Number of Active Channels
  Seq0BGPR1 |= (NumAchnActive == 2) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT7_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;                                       

  //Bit 1 - DisableRetraining Override (for LPDDR5x/5 Strobeless Mode)
  Seq0BGPR1 |= pUserInputBasic->DramType == LPDDR4 ? 0x0 : ((NoRDQS == 0x1) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT1_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET);
  
  //Bit 2 - SkipFlashCopy
  Seq0BGPR1 |= ( (pUserInputAdvanced->SkipFlashCopy[pstate] == 1) && (pUserInputBasic->Frequency[pstate] >= freqThreshold) && (pUserInputAdvanced->DisableRetraining == 0) 
                && ((pUserInputBasic->DramType == LPDDR4 ? 0x1 : (NoRDQS == 0)) != 0) ) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT2_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;

  
  //Bit8 - snoop WA 
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[8:8] with SnoopWA to  0x%d\n", __func__, pUserInputAdvanced->SnoopWAEn[pstate]);
  Seq0BGPR1 |= (pUserInputAdvanced->SnoopWAEn[pstate] ==1 ) ?  DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT8_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;
 

  //Bit 9 - Disable ZCal FSM based on data rate
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[9:9] with ZCal FSM disable to %d for data rate = %0d\n", __func__, (DataRateMbps <= DWC_DDRPHY_PHYINIT_PCLKDCA_EN_THRESHOLD ? 0x1 : 0x0), DataRateMbps);
  Seq0BGPR1 |= ((DataRateMbps <= 3200u) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT9_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET);

  //Bit 10 - Data Rate Check
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[10:10] to %d for PPT2 data rate = %d\n", __func__, (DataRateMbps <= 4267u ? 0x1 : 0x0), DataRateMbps);
  Seq0BGPR1 |= ((DataRateMbps <= 4267u) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT10_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET);

  //Bit 12 - CoreVddScalingMode 
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[12:12] to CoreVddScalingMode= %d\n", __func__, ((pUserInputAdvanced->CoreVddScalingMode[pstate] == 2) ? 0x2 : 0x0) );
  Seq0BGPR1 |= (pUserInputAdvanced->CoreVddScalingMode[pstate] == 2) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT12_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;       

  //Bit 3 - DSM or Self-Refresh and Power Down Mode for LP3 for PIE
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[3:3] with DSM to  0x%d\n", __func__, pUserInputAdvanced->Lp3DramState[pstate]);
  Seq0BGPR1 |=  (pUserInputAdvanced->Lp3DramState[pstate] == 1) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT3_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;
                                                          
  //Bit 11 - Strobeless mode
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming GPR1[11:11] to 0x%x\n", __func__,pstate, ((((mb1D[pstate].MR20_A0 & 0x3u) == 0x0) && (freq * ratio * 2 <= 1600))? 0x1 : 0x0) );
  Seq0BGPR1 |= (((mb1D[pstate].MR20_A0 & 0x3u) == 0x0) && (freq * ratio * 2 <= 1600)) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT11_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET;                                                             

  //Bit 13 and 14 - Data Rate Check
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[14:13] to DataRateRange = %d when DataRateMbps = %d\n", __func__, ((DataRateMbps > 3200u) ? 0x2 : ((DataRateMbps > 1600u) ? 0x1 : 0x0)), DataRateMbps);
  Seq0BGPR1 |= ((DataRateMbps > 3200u) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT14_SET : ((DataRateMbps > 1600u) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT13_SET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET)); 
  dwc_ddrphy_phyinit_cmnt("[%s] Programming GPR1[15:15] to userInputAdvanced->DisZCalOnDataRate = %d\n", __func__,  pUserInputAdvanced->DisZCalOnDataRate);
  Seq0BGPR1 |= ((pUserInputAdvanced->DisZCalOnDataRate==0x0u) ? DWC_DDRPHY_PHYINIT_SEQ0BGPR1_RESET : DWC_DDRPHY_PHYINIT_SEQ0BGPR1_BIT15_SET);


  dwc_ddrphy_phyinit_cmnt("[%s] Programming Seq0BGPR1 to 0x%x\n", __func__, Seq0BGPR1);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BGPR1_ADDR), Seq0BGPR1);

  /**
   * - Program Seq0BGPR2:
   *   - Description: Clear PIE's csrPState read GPR
   *   - Dependencies:
   *     - None
   */
  regData = 0x0;
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR2_ADDR), regData);

  /**
   * - Program Seq0BGPR6:
   *   - Description: Set GPR6=0x1 as a one-time flag to be used by PIE during cold boot
   *   - Dependencies:
   *     - None
   */
  regData = 0x1;
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR6_ADDR), regData);

  /**
   * - Program OdtSeg120:
   *   - Description: Enable specific driver segements for impedance calibration
   *   - Fields:
   *     - OdtSeg120PU0
   *     - OdtSeg120PD0
   *     - OdtSeg120PU1
   *     - OdtSeg120PD1
   *   - Dependencies:
   *     - None
   */
  uint16_t OdtSeg120;

  OdtSeg120 = (0x4UL << csr_OdtSeg120PD1_LSB) | (0x1UL << csr_OdtSeg120PU1_LSB) | (0x0UL << csr_OdtSeg120PD0_LSB) | (0x1UL << csr_OdtSeg120PU0_LSB);


  dwc_ddrphy_phyinit_cmnt("[%s] Programming OdtSeg120 to 0x%x\n", __func__, OdtSeg120);
  dwc_ddrphy_phyinit_io_write32((p_addr | tHMZCAL | csr_OdtSeg120_ADDR), OdtSeg120);

  /**
   * - Program ZCalCompCtrl
   *   - Description: Impedance calibration zcalana control
   *   - Fields:
   *     - ZCalCompGainCurrAdj
   *   - Dependencies
   *     - user_input_advanced.CalImpedanceCurrentAdjustment
   */
  uint16_t valZCalCompGainCurrAdj = pUserInputAdvanced->CalImpedanceCurrentAdjustment;
  uint16_t valZCalCompCtrl = valZCalCompGainCurrAdj << csr_ZCalCompGainCurrAdj_LSB;

  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalCompCtrl::ZCalCompGainCurrAdj to 0x%x\n", __func__, valZCalCompGainCurrAdj);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalCompCtrl to 0x%x\n", __func__, valZCalCompCtrl);
  dwc_ddrphy_phyinit_io_write32((p_addr | tHMZCAL | csr_ZCalCompCtrl_ADDR), valZCalCompCtrl);



  int DfiFreqRatio = pUserInputBasic->DfiFreqRatio[pstate];

  // Program PLL
  dwc_ddrphy_phyinit_programPLL(phyctx, 0, "[phyinit_C_initPhyConfigPsLoop]");


  uint16_t psCount[14];

  // Calculate the counts to obtain the correct delay for each frequency
  // Need to divide by 4 since the delay value are specified in units of
  // 4 clocks.
  uint32_t dllLock;
  uint32_t DfiFrq = pRuntimeConfig->DfiFreq[pstate];

  psCount[0] = ceil(0.5 * 0.25 * DfiFrq);

  uint16_t tZQCal;

  uint16_t nZQ;
    nZQ = pUserInputBasic->MaxNumZQ;
    tZQCal = 0;
    if (nZQ > 0 && nZQ <= 4) {
      tZQCal = ceil(1.5 * 0.25 * DfiFrq);
    } else if (nZQ <= 8) {
      tZQCal = ceil(3.0 * 0.25 * DfiFrq);
    } else if (nZQ <= 16) {
      tZQCal = ceil(6.0 * 0.25 * DfiFrq);
    } else {
      dwc_ddrphy_phyinit_assert(0, "[%s] invalid user input MaxNumZQ: %d\n", __func__, nZQ);
    }
  psCount[1] = tZQCal; // tZQCAL or tZQCAL4/8/16

  psCount[2] = ceil(10.0 * 0.25 * DfiFrq);

  if (DfiFrq > 266) {
    dllLock = 176;
  } else if (DfiFrq <= 266 && DfiFrq > 200) {
    dllLock = 132;
  } else {
    dllLock = 128;
 }

  if (pUserInputBasic->DfiFreqRatio[pstate] == 0x2) {
    dllLock *= 2;
  }

  psCount[3] = ceil(0.25 * dllLock);
  psCount[4] = ceil(0.1 * 0.25 * DfiFrq);

  uint32_t RxReplicaShortRangeB = (pUserInputAdvanced->CoreVddScalingMode[pstate] == 2) ? 150 : 50; 
  uint32_t RxReplicaShortRangeA = (pUserInputAdvanced->CoreVddScalingMode[pstate] == 2) ? 150 : 50; 


int16_t RxRepCalWait = (12 * RxReplicaShortRangeA/2 * 2 + 180)/4;  //stride=2 for LP5X PHY


    RxReplicaShortRangeB = 50; //set to 50
    RxReplicaShortRangeA = 50; //set to 50

    RxRepCalWait -= (pUserInputBasic->NumRank == 1) ? 292 : 441;
    RxRepCalWait -= (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 14 * pUserInputBasic->NumRank : 0;
  psCount[5] = (RxRepCalWait < 0) ? 0 : RxRepCalWait;

  int16_t OscWait;

    // Need to wait at least 2048tck for oscillator and tOSCODQI max of 40ns and 8tck.(42tck for datarate 8533)
    OscWait = pUserInputBasic->DfiFreqRatio[pstate] == 0x2 ? 71 : 131;
    if (pUserInputBasic->NumRank == 1) {
      OscWait += (pUserInputBasic->DfiFreqRatio[pstate] == 0x2) ? 152 : 168;
    }
  OscWait -= 4; // 16 DFI clocks for RxClk LCDL update delay
  OscWait -= psCount[5]; // Subtrack the RxRepCalWait.
  psCount[6] = (OscWait < 0) ? 0 : OscWait;

  psCount[7] = 0x0;
  psCount[10] = 0x0;

  uint16_t tXDSM_XP;
  uint16_t tPDXCSODTON;

    tXDSM_XP = (uint16_t)ceil(190.0 * 0.25 * DfiFrq);
    psCount[7] = (pUserInputAdvanced->Lp3DramState[pstate] == 1) ? tXDSM_XP : 0;

    tPDXCSODTON = (uint16_t)ceil(0.02 * 0.25 * DfiFrq);
    psCount[10] = ((psCount[7] == 0) && (((mb1D[pstate].MR17_A0 & 0x10u) >> 4) == 0)) ? tPDXCSODTON : 0;

   // 20ns delay for PIE to use
  psCount[11] = (uint16_t)ceil(0.02 * 0.25 * DfiFrq);

  // 50ns delay for PIE to use in LP54 for tFC_Long delay
  psCount[12] = ceil(0.050 * 0.25 * DfiFrq);

  // tXSR = tRFCab + 7.5ns delay
  uint16_t tRFCab;

  tRFCab = ((mb1D[pstate].MR19_A0 & 0x3u) == 0x2u) ? 410u : 380u;
  psCount[13] = (uint16_t)ceil(0.001 * (tRFCab + 7.5) * 0.25 * DfiFrq);

  /**
   * - Program Seq0BDLY0:
   *   - Description: Program DLY0 with 0.5us number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.Frequency
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY0 to 0x%x (0.5us PIE delay)\n", __func__, pstate, freq, psCount[0]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY0_ADDR), psCount[0]);

  /**
   * - Program Seq0BDLY1:
   *   - Description: Program DLY1 with tZQCal (LPDDR5) or 1.0us number of DfiClk's for PIE (LPDDR4, DDR5)
   *   - Dependencies:
   *     - user_input_advanced.MaxNumZQ
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY1 to 0x%x (tZQCal PIE delay)\n", __func__, pstate, freq, psCount[1]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY1_ADDR), psCount[1]);

  /**
   * - Program Seq0BDLY2:
   *   - Description: Program DLY2 with 10.0us number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.Frequency
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY2 to 0x%x (10.us PIE delay)\n", __func__, pstate, freq, psCount[2]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY2_ADDR), psCount[2]);

  /**
   * - Program Seq0BDLY3:
   *   - Description: Program DLY3 with dllLock delay in number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.Frequency
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY3 to 0x%x (dllLock PIE delay)\n", __func__, pstate, freq, psCount[3]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY3_ADDR), psCount[3]);

  /**
   * - Program Seq0BDLY4:
   *   - Description: Program DLY4 with 0.1us number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.Frequency
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY4 to 0x%x (0.1us PIE delay)\n", __func__, pstate, freq, psCount[4]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY4_ADDR), psCount[4]);

  /**
   * - Program Seq0BDLY5:
   *   - Description: Program DLY5 with RxReplicaCalWait delay number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumRank
   *     - user_input_basic.DfiFreqRatio
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY5 to 0x%x (RxReplicaCalWait delay)\n", __func__, pstate, freq, psCount[5]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY5_ADDR), psCount[5]);

  /**
   * - Program Seq0BDLY6:
   *   - Description: Program DLY6 with oscillator wait delay number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumRank
   *     - user_input_basic.DfiFreqRatio
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY6 to 0x%x (Oscillator PIE delay)\n", __func__, pstate, freq, psCount[6]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY6_ADDR), psCount[6]);

  /**
   * - Program Seq0BDLY7:
   *   - Description: Program DLY7 with tXDSM_XP delay number of DfiClk's for PIE in LPDDR5 mode and 0x0 for other protocols
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_advanced.Lp3DramState
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY7 to 0x%x (tXDSM_XP PIE delay)\n", __func__, pstate, freq, psCount[7]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY7_ADDR), psCount[7]);

  /**
   * - Program Seq0BDLY10:
   *   - Description: Program DLY10 with tPDXCSODTON 20ns delay if Lp3DramState is disabled, else 0x0
   *   - Dependencies:
   *     - user_input_advanced.Lp3DramState
   *     - user_input_basic.DramType
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY10 to 0x%x (tPDXCSODTON 20ns PIE delay)\n", __func__, pstate, freq, psCount[10]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY10_ADDR), psCount[10]);

  /**
   * - Program Seq0BDLY11:
   *   - Description: Program DLY10 with 20ns delay
   *   - Dependencies:
   *     - user_input_basic.DramType
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY11 to 0x%x (20ns PIE delay)\n", __func__, pstate, freq, psCount[11]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY11_ADDR), psCount[11]);

  /**
   * - Program Seq0BDLY12:
   *   - Description: Program DLY12 with 50ns number of DfiClk's for PIE
   *   - Dependencies:
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.Frequency
   *     - user_input_basic.DramType
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY12 to 0x%x (50ns PIE delay)\n", __func__, pstate, freq, psCount[12]);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY12_ADDR), psCount[12]);

  /**
   * - Program Seq0BDLY13:
   *   - Description: Program DLY13 with tXSR = tRFCab + 7.5ns number of DfiClk's for PIE
   *   - Dependencies:
   *     - MR19 [1:0] eDVFSC
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming Seq0BDLY13 to 0x%x (tXSR PIE delay, tRFCab delay is %dns)\n", __func__, pstate, freq, psCount[13], tRFCab);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY13_ADDR), psCount[13]);


  /**
   * - Program PclkPtrInitVal:
   *   - Description: The values programmed here assume ideal properties of DfiClk and Pclk including:
   *                  - DfiClk skew
   *                  - DfiClk jitter
   *                  - DfiClk PVT variations
   *                  - Pclk skew
   *                  - Pclk jitter
   *                  - The PclkPtrInitVal register controls the hase offset between read and write pointers of master command FIFO.
   *                  A small value my be prone to causing underflow and a large value will increase the PHY latency.
   *                  The units of this register are in UI. Please see PUB databook for detailed programming information.
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - phyinit_config.PclkPtrInitVal
   *     - user_input_basic.PclkPtrInitValOvr
   */
  // We update the struct field here as the dwc_ddrphy_phyinit_progCsrSkipTrain() function
  // needs the value and would otherwise require a PHY read register implementation.
  phyctx->PclkPtrInitVal[pstate] = 3;
  if (pUserInputBasic->PclkPtrInitValOvr == 1) {
    phyctx->PclkPtrInitVal[pstate] = pUserInputBasic->PclkPtrInitVal[pstate];
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming PclkPtrInitVal to 0x%x\n", __func__, pstate, freq, phyctx->PclkPtrInitVal[pstate]);
  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_PclkPtrInitVal_ADDR), phyctx->PclkPtrInitVal[pstate]);
  dwc_ddrphy_phyinit_io_write32((p_addr | tHMMAS | csr_HMPclkPtrInitVal_ADDR), phyctx->PclkPtrInitVal[pstate]);

  /**
   * - Program DfiFreqRatio,
   *   - Description: DFI Frequency Ratio
   *   - Dependencies:
   *     - user_input_basic.DfiFreqRatio
   */
    uint16_t CKR = (mb1D[pstate].MR18_A0 & 0x80u) >> 7;

    if ((CKR == 1 && DfiFreqRatio != 1) || (CKR == 0 && DfiFreqRatio != 2)) {
      dwc_ddrphy_phyinit_assert(0, "[%s] Inconsistent clock ratio set with MR18 CKR (%d) and pUserInputBasic->DfiFreqRatio (0x%x) for pstate %d\n", __func__, CKR, DfiFreqRatio, pstate);
    }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DfiFreqRatio to 0x%x\n", __func__, pstate, freq, DfiFreqRatio);
  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_DfiFreqRatio_ADDR), DfiFreqRatio);

  /**
   * - Program DbyteRxDqsModeCntrl
   *   - RxPostambleMode
   *   - RxPreambleMode
   * - Program DqsPreambleControl:
   *   - Fields:
   *     - LP4PostambleExt (Tx)
   *   - Dependencies:
   *      - user_input_basic.DramType
   * - Program RxDigStrbEn and DxDigStrobeMode for RDQS disabled mode (strobe-less read mode) (only applies to LPDDR5 protocol)
   */
  int DqsPreambleControl;
  uint32_t LP4PostambleExt = 0;
  uint32_t WDQSEXTENSION = 0;
  uint32_t WCKEXTENSION = 0;
  uint32_t RxPostambleMode = 0;
  uint32_t RxPreambleMode = 0;
  uint32_t LPDDR5RdqsEn = 0;
  uint32_t LPDDR5RdqsPre = 0;
  uint32_t LPDDR5RdqsPst = 0;
  uint32_t DqPreOeExt = 0;
  uint32_t DqPstOeExt = 0;
  int DbyteRxDqsModeCntrl;

  uint16_t pst;
  uint16_t RxDigStrbEn;
  uint16_t DxDigStrobeMode;

  /**
   * - Program RxDigStrbEn DxDigStrobeMode:
   *   - Description: Program RxDigStrbEn to enable digital strobe read mode and DxDigStrobeMode to select source for read-data strobes
   *   - Fields:
   *     - EnStrblssRdMode
   *     - RxReplicaPowerDownNoRDQS
   *     - OdtDisDqs
   *   - Dependencies:
   *     - mb1D[ps].MR10_A0[7:6]
   *     - mb1D[ps].MR20_A0[1:0]
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   */
    pst = (mb1D[pstate].MR10_A0 & 0xC0u) >> 6;
    WDQSEXTENSION = 0;
    LPDDR5RdqsEn = 0x1;
    LPDDR5RdqsPre = 0x1; // JEDEC MR10.OP[5:4]=1 Static 2*tWCK, Toggle 2*tWCK
    LPDDR5RdqsPst = pst; // JEDEC MR10.OP[7:6]=1 2.5*tWCK or =2 4.5*tWCK
    RxDigStrbEn = 0;
    DxDigStrobeMode = 0;
    // Case where RDQS is disabled and data rate is equal or less than 1600 Mbps;
    if (((mb1D[pstate].MR20_A0 & 0x3u) == 0x0) && (freq * ratio * 2 <= 1600)) {
      LPDDR5RdqsEn = 0x0;
      RxPreambleMode = 0x1;
      RxPostambleMode = 0x1;
      RxDigStrbEn = (0x1u << csr_EnStrblssRdMode_LSB) | (0x1u << csr_RxReplicaPowerDownNoRDQS_LSB) | (0x1u << csr_OdtDisDqs_LSB);
      DxDigStrobeMode = 0x2;
    }
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming RxDigStrbEn to 0x%x\n", __func__, pstate, freq, RxDigStrbEn);
    for (int byte = 0; byte < NumDbyteActive; byte++) {
      uint32_t c_addr = byte * c1;
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxDigStrbEn_ADDR), RxDigStrbEn);
    }
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DxDigStrobeMode HMDBYTE to 0x%x\n", __func__, pstate, freq, DxDigStrobeMode);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DxDigStrobeMode HMDBYTE to 0x%x\n", __func__, pstate, freq, DxDigStrobeMode);

    for (uint32_t byte = 0; byte < NumDbyteActive; byte++) {
      uint32_t c_addr0 = ((byte*2) & 0xfu) * c1;
      uint32_t c_addr1 = (((byte*2)+1) & 0xfu) * c1;
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_DxDigStrobeMode_ADDR), DxDigStrobeMode);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_DxDigStrobeMode_ADDR), DxDigStrobeMode);
    }

    // DFE
    if (((mb1D[pstate].MR24_A0 & 0x07u) != 0) || ((mb1D[pstate].MR24_A0 & 0x70u) != 0) || ((mb1D[pstate].MR41_A0 & 0x01u) != 0)) {
      DqPreOeExt = 1;
    }


    if ((pUserInputBasic->Frequency[pstate] > 688) && (pUserInputBasic->Frequency[pstate] < 800) && (pUserInputBasic->DfiFreqRatio[pstate] == 0x1)) {
      WCKEXTENSION = 1;
    }

  /**
   * - Program DqsPreambleControl DbyteRxDqsModeCntrl:
   *   - Description: Program read/write DQS preamble and control for generating RxClk from read DQS edges
   *   - Fields:
   *      - LP4PostambleExt
   *      - WDQSEXTENSION
   *      - DqPreOeExt
   *      - DqPstOeExt
   *      - RxPostambleMode
   *      - RxPreambleMode
   *      - LPDDR5RdqsEn
   *      - LPDDR5RdqsPre
   *      - LPDDR5RdqsPst
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumDbytesPerCh
   *     - mb1D[ps].MR3_A0[1:1]
   */
  DqsPreambleControl = (WDQSEXTENSION << csr_WDQSEXTENSION_LSB)
            | (LP4PostambleExt << csr_LP4PostambleExt_LSB)
            | (WCKEXTENSION << csr_WCKEXTENSION_LSB)
            | (DqPreOeExt << csr_DqPreOeExt_LSB)
            | (DqPstOeExt << csr_DqPstOeExt_LSB);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = byte * c1;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DqsPreambleControl::LP4PostambleExt to 0x%x\n", __func__, pstate, freq, byte, LP4PostambleExt);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DqsPreambleControl::WCKEXTENSION to 0x%x\n", __func__, pstate, freq, byte, WCKEXTENSION);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DqsPreambleControl::DqPreOeExt to 0x%x\n", __func__, pstate, freq, byte, DqPreOeExt);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DqsPreambleControl to 0x%x\n", __func__, pstate, freq, byte, DqsPreambleControl);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_DqsPreambleControl_ADDR), DqsPreambleControl);
  }

  DbyteRxDqsModeCntrl = (RxPreambleMode << csr_RxPreambleMode_LSB) | (RxPostambleMode << csr_RxPostambleMode_LSB)
                      | (LPDDR5RdqsEn << csr_LPDDR5RdqsEn_LSB) | (LPDDR5RdqsPre << csr_LPDDR5RdqsPre_LSB) | (LPDDR5RdqsPst << csr_LPDDR5RdqsPst_LSB);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = byte * c1;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DbyteRxDqsModeCntrl::RxPreambleMode to 0x%x\n", __func__, pstate, freq, byte, RxPreambleMode);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DbyteRxDqsModeCntrl::RxPostambleMode to 0x%x\n", __func__, pstate, freq, byte, RxPostambleMode);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DbyteRxDqsModeCntrl::LPDDR5RdqsEn to 0x%x\n", __func__, pstate, freq, byte, LPDDR5RdqsEn);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DbyteRxDqsModeCntrl::LPDDR5RdqsPre to 0x%x\n", __func__, pstate, freq, byte, LPDDR5RdqsPre);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DbyteRxDqsModeCntrl::LPDDR5RdqsPst to 0x%x\n", __func__, pstate, freq, byte, LPDDR5RdqsPst);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DbyteRxDqsModeCntrl to 0x%x\n", __func__, pstate, freq, byte, DbyteRxDqsModeCntrl);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_DbyteRxDqsModeCntrl_ADDR), DbyteRxDqsModeCntrl);
  }

  /**
   * - Program DxDfiClkDis and DxPClkDis
   *   - Description: Program DBYTE DfiClk and Pclk disable
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - mb1D[ps].MR20_A0[1:0]
   */
  for (int byte = 0; byte < NumDbyte; byte++) {
    uint32_t c_addr = byte * c1;

    uint16_t DxDfiClkDis = 0x0;
    uint16_t DxPClkDis = 0x0;


      if (((mb1D[pstate].MR20_A0 & 0x3u) == 0x0) && (freq * ratio * 2 <= 1600)) {
        DxDfiClkDis = 0x1UL << csr_DfiClkDqsDis_LSB;
        DxPClkDis = 0x1UL << csr_PClkDqsDis_LSB;
      }

    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte)) {
      DxDfiClkDis = (0x1UL << csr_DfiClkWckDis_LSB) | (0x1UL << csr_DfiClkDqsDis_LSB) | (0x1ffUL << csr_DfiClkDqDis_LSB);
      DxPClkDis = (0x1UL << csr_PClkWckDis_LSB) | (0x1UL << csr_PClkDqsDis_LSB) | (0x1ffUL << csr_PClkDqDis_LSB);
    }

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DxPClkDis to 0x%x\n", __func__, pstate, freq, byte, DxPClkDis);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DxDfiClkDis to 0x%x\n", __func__, pstate, freq, byte, DxDfiClkDis);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_DxPClkDis_ADDR), DxPClkDis);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_DxDfiClkDis_ADDR), DxDfiClkDis);
  }


  /**
   * - Program ZCalClkInfo:
   *   - Description: Program impedance calibration clock ratio
   *   - Fields:
   *     - ZCalDfiClkTicksPer1uS
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio (only applies for LPDDR4 protocol)
   */
  int ZCalDfiClkTicksPer1uS[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  // Number of DfiClk cycles per 1usi
    ZCalDfiClkTicksPer1uS[pstate] = freq;

  if (ZCalDfiClkTicksPer1uS[pstate] < 24) {
    ZCalDfiClkTicksPer1uS[pstate] = 24;  // Minimum value of ZCalDfiClkTicksPer1uS = 24
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ZCalClkInfo::ZCalDfiClkTicksPer1uS to 0x%x\n", __func__, pstate, freq, ZCalDfiClkTicksPer1uS[pstate]);
  dwc_ddrphy_phyinit_io_write32((p_addr | tZCAL | csr_ZCalClkInfo_ADDR), ZCalDfiClkTicksPer1uS[pstate]);

  /**
   * - Program ZCalSlewRateCtrl:
   *   - Description: Program impedance calibration slew rate control
   *   - Fields:
   *     - ZCalTxSlewPU
   *     - ZCalTxSlewPD
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - mb1D[ps].MR3_A0[0:0]
   */
    uint16_t ZCalTxSlewPU = 0x0;
    uint16_t ZCalTxSlewPD = 0x0;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ZCalSlewRateCtrl::ZCalTxSlewPU to 0x%x ZCalSlewRateCtrl::ZCalTxSlewPD to 0x%x\n\n", __func__, pstate, freq, ZCalTxSlewPU,ZCalTxSlewPD);
  dwc_ddrphy_phyinit_io_write32((p_addr | tHMZCAL | csr_ZCalSlewRateCtrl_ADDR), ((ZCalTxSlewPU << csr_ZCalTxSlewPU_LSB) | (ZCalTxSlewPD << csr_ZCalTxSlewPD_LSB)));


  /**
   * - Program RxGainCurrAdjRxReplica:
   *   - Description: Program RX bias current control for DIFF IOs in DQS slice RxReplica ckt
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.RxBiasCurrentControlRxReplica
   */
  uint16_t valRxGainCurrAdjR = pUserInputAdvanced->RxBiasCurrentControlRxReplica[pstate];

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE RxGainCurrAdjRxReplica to 0x%x\n", __func__, pstate, freq, valRxGainCurrAdjR);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = byte * c1;

    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxGainCurrAdjRxReplica_ADDR), valRxGainCurrAdjR);
  }

  /**
   * - Program CmdFifoWrModeMaster:
   *   - Description: Program master top FIFO write mode value
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.PllBypass
   *     - user_input_basic.Pll2xMode (LPDDR4 only)
   */
  uint16_t CmdFifoWrModeMaster;
    CmdFifoWrModeMaster = ((pUserInputBasic->PllBypass[pstate] == 1) && (DfiFreqRatio == 1)) ? 0x0 : 0x1;


  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_CmdFifoWrModeMaster_ADDR), CmdFifoWrModeMaster);

  /**
   * - Program CPclkDivRatio:
   *   - Description: Program Pclk clock divider ratios
   *   - Fields:
   *     - CPclkDivCa0
   *     - CPclkDivCa1
   *     - CPclkDivDq0
   *     - CPclkDivDq1
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.PllBypass
   *     - user_input_basic.Pll2xMode (LPDDR4 only)
   *     - user_input_basic.NumCh
   */
  uint16_t CPclkDivCa0 = 0, CPclkDivCa1 = 0;
  uint16_t CPclkDivDq0 = 0, CPclkDivDq1 = 0;
  uint16_t CPclkDivRatio;

  CPclkDivCa0 = 1;
  CPclkDivCa1 = 1;
  CPclkDivDq0 = 1;
  CPclkDivDq1 = 1;

  if (DfiFreqRatio == 1) {
    CPclkDivCa0 = 2;
    CPclkDivCa1 = 2;
    CPclkDivDq0 = 2;
    CPclkDivDq1 = 2;
  }
  if ((pUserInputAdvanced->AcQuarterDataRate == 0x1) && (DataRateMbps>=5500)) {
    CPclkDivCa0 = 2;
    CPclkDivCa1 = 2;
    CPclkDivDq0 = 1;
    CPclkDivDq1 = 1;
  }
  if (pUserInputBasic->PllBypass[pstate] == 1) {
    CPclkDivCa0 = 1;
    CPclkDivCa1 = 1;
    CPclkDivDq0 = 1;
    CPclkDivDq1 = 1;
  }

  if (NumAchnActive == 1) {
    CPclkDivRatio = ((CPclkDivCa0 << csr_CPclkDivCa0_LSB) & csr_CPclkDivCa0_MASK) | ((CPclkDivDq0 << csr_CPclkDivDq0_LSB) & csr_CPclkDivDq0_MASK);
  }else {
    CPclkDivRatio = ((CPclkDivCa0 << csr_CPclkDivCa0_LSB) & csr_CPclkDivCa0_MASK)
              | ((CPclkDivCa1 << csr_CPclkDivCa1_LSB) & csr_CPclkDivCa1_MASK)
              | ((CPclkDivDq0 << csr_CPclkDivDq0_LSB) & csr_CPclkDivDq0_MASK)
              | ((CPclkDivDq1 << csr_CPclkDivDq1_LSB) & csr_CPclkDivDq1_MASK);
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming CPclkDivRatio to 0x%x\n", __func__, pstate, freq, CPclkDivRatio);
  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_CPclkDivRatio_ADDR), CPclkDivRatio);

  /**
   * - Program CkDisVal:
   *   - Description: Program mode select register for MEMCLK
   *   - Dependencies:
   *     - user_input_advanced.CkDisVal
   */
  if (pUserInputAdvanced->CkDisVal[pstate] != 0x0) {
    dwc_ddrphy_phyinit_assert(0, "[%s] Unexpected value for CkDisVal == %d", __func__, pUserInputAdvanced->CkDisVal[pstate]);
  }

  /**
   * - Program DMIPinPresent
   *   - Description: Program each DBYTE enable for Read-DBI feature
   *   - Fields:
   *     - RdDbiEnabled
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - mb1D[ps].MR3_A0[6:6]
   *     - mb1D[ps].MR22_A0[7:6]
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t DMIPinPresent;

    DMIPinPresent = ((mb1D[pstate].MR3_A0 & 0x40u) >> 6 & 1u)  // DBI-RD
            | ((mb1D[pstate].MR22_A0 & 0xC0u) >> 6 & 1u);  // RECC

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = byte * c1;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming DBYTE%d.DMIPinPresent::RdDbiEnabled to 0x%x\n", __func__, pstate, freq, byte, DMIPinPresent);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_DMIPinPresent_ADDR), DMIPinPresent);
  }

  /**
   * - Program TrackingModeCntrl, EnRxDqsTracking:
   *   - Description: Program mode controls for fine RxEn timing adjustment during mission mode
   *   - Fields:
   *     - EnWck2DqoSnoopTracking
   *     - Twck2dqoTrackingLimit
   *     - Tdqs2dqTrackingLimit
   *     - DqsOscRunTimeSel
   *     - RxDqsTrackingThreshold
   *     - DqsSampNegRxEnSense
   *     - EnDqsSampNegRxEn
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - uesr_input_basic.NumDbytesPerCh
   *     - user_input_advanced.EnWck2DqoTracking 
   */
  /**    - user_input_advanced.RxDqsTrackingThreshold
   *     - user_input_advanced.DqsOscRunTimeSel
   */

  uint16_t EnWck2DqoSnoopTracking;
  uint16_t Twck2dqoTrackingLimit;

    EnWck2DqoSnoopTracking = pUserInputAdvanced->EnWck2DqoTracking[pstate] == 1 ? 1 : 0;
    Twck2dqoTrackingLimit = 0;  // no limit (default)

  /**
   * - Program EnPhyUpdZQCalUpdate:
   *   - Description: Enable ZQ Cal on Phy update
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_advanced.EnWck2DqoTracking
   */
  uint16_t EnPhyUpdZQCalUpdate = csr_EnPhyUpdZQCalUpdate_MASK;

    // If single channel, mask out the upper channel enable
    EnPhyUpdZQCalUpdate = (EnWck2DqoSnoopTracking == 1) ? ( (NumAchn == 1) ? (EnPhyUpdZQCalUpdate & 0x1u) : EnPhyUpdZQCalUpdate ) : 0x0;

    dwc_ddrphy_phyinit_cmnt("[phyinit_C_initPhyConfig] Programming EnPhyUpdZQCalUpdate to 0x%x\n", EnPhyUpdZQCalUpdate);
    dwc_ddrphy_phyinit_io_write32((tPPGC | csr_EnPhyUpdZQCalUpdate_ADDR), EnPhyUpdZQCalUpdate);

  /**
   * - Program DisableZQupdateOnSnoop:
   *   - Description: Disable ZQUpdate (part of ctrlupd) if snoop_osc_running asserted
   *   - Dependencies:
   *     - user_input_advanced.EnWck2DqoTracking
   *     - user_input_advanced.UseSnpsController
   */

    uint16_t  DisableZQupdateOnSnoop = (EnWck2DqoSnoopTracking != 0) && (pUserInputAdvanced->UseSnpsController == 1) ? 0x1 : 0x0;
    dwc_ddrphy_phyinit_cmnt("[%s] Programming DisableZQupdateOnSnoop to 0x%x\n", __func__, DisableZQupdateOnSnoop);
    dwc_ddrphy_phyinit_io_write32((tPPGC | csr_DisableZQupdateOnSnoop_ADDR), DisableZQupdateOnSnoop);

  // Only enable the tracking during PPT2 training
  uint16_t EnDqsSampNegRxEn = 0;
  uint16_t DqsSampNegRxEnSense = pUserInputAdvanced->DqsSampNegRxEnSense[pstate];

  uint16_t EnRxDqsTrackingVal = (EnDqsSampNegRxEn << csr_EnDqsSampNegRxEn_LSB)
                              | (DqsSampNegRxEnSense << csr_DqsSampNegRxEnSense_LSB);

  uint16_t RxDqsTrackingThreshold = pUserInputAdvanced->RxDqsTrackingThreshold[pstate];
  uint16_t DqsOscRunTimeSel = pUserInputAdvanced->DqsOscRunTimeSel[pstate];
  uint16_t Tdqs2dqTrackingLimit = 0; // no limit (default)
  uint16_t TrackingModeCntrl = (EnWck2DqoSnoopTracking << csr_EnWck2DqoSnoopTracking_LSB)
                | (Twck2dqoTrackingLimit << csr_Twck2dqoTrackingLimit_LSB)
                | (Tdqs2dqTrackingLimit << csr_Tdqs2dqTrackingLimit_LSB)
                | (DqsOscRunTimeSel << csr_DqsOscRunTimeSel_LSB)
                | (RxDqsTrackingThreshold << csr_RxDqsTrackingThreshold_LSB);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = byte * c1;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TrackingModeCntrl::EnDqsSampNegRxEn to 0x%x\n", __func__, pstate, freq, EnDqsSampNegRxEn);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TrackingModeCntrl::RxDqsTrackingThreshold to 0x%x\n", __func__, pstate, freq, RxDqsTrackingThreshold);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TrackingModeCntrl::DqsOscRunTimeSel to 0x%x\n", __func__, pstate, freq, DqsOscRunTimeSel);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TrackingModeCntrl to 0x%x\n", __func__, pstate, freq, TrackingModeCntrl);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_TrackingModeCntrl_ADDR), TrackingModeCntrl);
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming EnRxDqsTracking::EnDqsSampNegRxEn to 0x%x\n", __func__, pstate, freq, EnDqsSampNegRxEn);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming EnRxDqsTracking::DqsSampNegRxEnSense to 0x%x\n", __func__, pstate, freq, DqsSampNegRxEnSense);
  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_EnRxDqsTracking_ADDR), EnRxDqsTrackingVal);

  /**
   * - Program TxImpedanceAC, TxImpedanceDq, TxImpedanceDqs, TxImpedanceAC:
   *   - Description: Program TX impedance for AC/DQ/DQS
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.TxImpedanceAc
   *     - user_input_advanced.TxImpedanceDq
   *     - user_input_advanced.TxImpedanceDqs
   *     - user_input_advanced.TxImpedanceWCK
   *     - user_input_advanced.TxImpedanceCk
   */
  uint32_t TxStrenCodePU = 0;
  uint32_t TxStrenCodePD = 0;
  int TxImpedance = 0;
  int TxStrenCodePUCsCke;
  int TxStrenCodePDCsCke;
  int TxImpedanceCsCke;
  char msgCsCke[] = "CS";

  // Start TX Impedance for DBYTE
  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;
    // *** DBYTE SE *** //
    switch (pUserInputAdvanced->TxImpedanceDq[pstate]) {
      case 120:
        TxStrenCodePU = 0x1;
        break;
      case 60:
        TxStrenCodePU = 0x3;
        break;
      case 40:
        TxStrenCodePU = 0x7;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->TxImpedanceDq[%d]=%d\n", __func__, pstate, pUserInputAdvanced->TxImpedanceDq[pstate]);
        break;
    }
    TxStrenCodePD = TxStrenCodePU;

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxImpedanceDq::TxStrenCodeDqPU to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodePU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxImpedanceDq::TxStrenCodeDqPD to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodePD);
    TxImpedance = (TxStrenCodePU << csr_TxStrenCodeDqPU_LSB) | (TxStrenCodePD << csr_TxStrenCodeDqPD_LSB);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0  | csr_TxImpedanceDq_ADDR), TxImpedance);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1  | csr_TxImpedanceDq_ADDR), TxImpedance);

    // *** DBYTE DQS *** //
    switch (pUserInputAdvanced->TxImpedanceDqs[pstate]) {
      case 120:
        TxStrenCodePU = 0x1;
        break;
      case 60:
        TxStrenCodePU = 0x3;
        break;
      case 40:
        TxStrenCodePU = 0x7;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->TxImpedanceDqs[%d]=%d\n", __func__, pstate, pUserInputAdvanced->TxImpedanceDqs[pstate]);
        break;
    }

      /*
       * In Rx Strobeless Mode, DQS T/C is set IO TX Drive-Strength CSR to high-z.
       */
      if (((mb1D[pstate].MR20_A0 & 0x3) == 0x0) && ((freq * ratio * 2) <= 1600)) {
        TxStrenCodePU = 0;
      }

      /*
       * TxStrenCodeDqsPUC and TxStrenCodeDqsPDC set to high-z.
       */
      uint16_t TxStrenCodeHiZ = 0;
      TxStrenCodePD = TxStrenCodePU;

      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxImpedanceDqs::TxStrenCodeDqsPUT to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodePU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxImpedanceDqs::TxStrenCodeDqsPDT to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodePD);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxImpedanceDqs::TxStrenCodeDqsPUC to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodeHiZ);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxImpedanceDqs::TxStrenCodeDqsPDC to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodeHiZ);      
      TxImpedance = (TxStrenCodePU << csr_TxStrenCodeDqsPUT_LSB) | (TxStrenCodeHiZ << csr_TxStrenCodeDqsPUC_LSB) | (TxStrenCodePD << csr_TxStrenCodeDqsPDT_LSB) | (TxStrenCodeHiZ << csr_TxStrenCodeDqsPDC_LSB);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_TxImpedanceDqs_ADDR), TxImpedance);


      // *** DBYTE WCK *** //
    switch (pUserInputAdvanced->TxImpedanceWCK[pstate]) {
      case 120:
        TxStrenCodePU = 0x1;
        break;
      case 60:
        TxStrenCodePU = 0x3;
        break;
      case 40:
        TxStrenCodePU = 0x7;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->TxImpedanceWCK[%d]=%d\n", __func__, pstate, pUserInputAdvanced->TxImpedanceWCK[pstate]);
        break;
    }
    TxStrenCodePD = TxStrenCodePU;

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d WCK TxImpedanceDqs::TxStrenCodeDqsPUT/C to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodePU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x%x\n", __func__, pstate, freq, byte, TxStrenCodePD);
    TxImpedance = (TxStrenCodePU << csr_TxStrenCodeDqsPUT_LSB) | (TxStrenCodePU << csr_TxStrenCodeDqsPUC_LSB) | (TxStrenCodePD << csr_TxStrenCodeDqsPDT_LSB) | (TxStrenCodePD << csr_TxStrenCodeDqsPDC_LSB);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_TxImpedanceDqs_ADDR), TxImpedance);
  } // foreach dbyte
  // End TX Impedance for DBYTE

  // Start TX Impedance for AC
  for (int acx = 0; acx < NumAchnActive; acx++) {
    int c_addr;
    int instance;

    // *** AC SE *** //
    switch (pUserInputAdvanced->TxImpedanceAc[pstate]) {
      case 120:
        TxStrenCodePU = 0x1;
        break;
      case 60:
        TxStrenCodePU = 0x3;
        break;
      case 40:
        TxStrenCodePU = 0x7;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->TxImpedanceAc[%d]=%d\n", __func__, pstate, pUserInputAdvanced->TxImpedanceAc[pstate]);
        break;
    }
    TxStrenCodePD = TxStrenCodePU;

    // *** AC CS *** //
    switch (pUserInputAdvanced->TxImpedanceCsCke) {
      case 400:
         TxStrenCodePUCsCke = 0x1;
        break;
      case 100:
         TxStrenCodePUCsCke = 0x3;
        break;
      case 66:
         TxStrenCodePUCsCke = 0x7;
        break;
      case 50:
         TxStrenCodePUCsCke = 0xf;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->TxImpedanceCsCke=%d\n", __func__, pUserInputAdvanced->TxImpedanceCsCke);
        break;
    }
    TxStrenCodePDCsCke = TxStrenCodePUCsCke;
    TxImpedanceCsCke = (TxStrenCodePUCsCke << csr_TxStrenCodePUAC_LSB) | (TxStrenCodePDCsCke << csr_TxStrenCodePDAC_LSB);

    TxImpedance = (TxStrenCodePU << csr_TxStrenCodePUAC_LSB) | (TxStrenCodePD << csr_TxStrenCodePDAC_LSB);
    //for each ACX_IO + CS
    for (int hmac = 0; hmac < 5; hmac++) {
      c_addr = (hmac + acx*NumHmacPerChan)*c1;
      instance = hmac + acx*NumHmacPerChan;
      if(hmac < 4){
        dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d SE TxImpedanceAC::TxStrenCodePUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxStrenCodePU);
        dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d SE TxImpedanceAC::TxStrenCodePDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxStrenCodePD);
        dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_TxImpedanceAC_ADDR), TxImpedance);
      }else{
        dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d %s TxImpedanceAC::TxStrenCodePUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, msgCsCke, TxImpedanceCsCke);
        dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming AC%d HMAC%d Instance%d %s TxImpedanceAC::TxStrenCodePDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, msgCsCke, TxImpedanceCsCke);
        dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_TxImpedanceAC_ADDR), TxImpedanceCsCke);
      }
    }
      if (pUserInputAdvanced->DtoEnable == 1){
        dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c14 | csr_TxImpedanceAC_ADDR), TxImpedance);
      }

    // *** AC DIFF *** //
    switch (pUserInputAdvanced->TxImpedanceCk[pstate]) {
      case 120:
        TxStrenCodePU = 0x1;
        break;
      case 60:
        TxStrenCodePU = 0x3;
        break;
      case 40:
        TxStrenCodePU = 0x7;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->TxImpedanceCk[%d]=%d\n", __func__, pstate, pUserInputAdvanced->TxImpedanceCk[pstate]);
        break;
    }
    TxStrenCodePD = TxStrenCodePU;
    TxImpedance = (TxStrenCodePU << csr_TxStrenCodePUAC_LSB) | (TxStrenCodePD << csr_TxStrenCodePDAC_LSB);

    for (int hmac = 5; hmac < 7; hmac ++) {
      c_addr = (hmac + acx*NumHmacPerChan)*c1;
      instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d TxImpedanceAC::TxStrenCodePU to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxStrenCodePU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d TxImpedanceAC::TxStrenCodePD to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxStrenCodePD);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_TxImpedanceAC_ADDR), TxImpedance);
    }
} // foreach AC channel

  // End TX Impedance for AC

  /**
   * - Program OdtImpedanceAC, OdtImpedanceDq, OdtImpedanceDqs
   *   - Description: Program ODT impedance for AC/DQ/DQS
   *   - Dependencies
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.OdtImpedanceDq
   *     - user_input_advanced.OdtImpedanceCa
   *     - user_input_advanced.OdtImpedanceCk
   *     - user_input_advanced.OdtImpedanceDqs
   *     - user_input_advanced.OdtImpedanceWCK
   *     - user_input_advanced.OdtImpedanceCs
   */

  int OdtStrenCodePU = 0;
  int OdtStrenCodePD = 0;
  int OdtImpedance = 0;

  // ********* Start ODT Impedance for DBYTE ********* //
  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;

    OdtStrenCodePU = 0;
    OdtStrenCodePD = 0;
    // *** DBYTE SE *** //
    switch (pUserInputAdvanced->OdtImpedanceDq[pstate]) {
      case 120:
        OdtStrenCodePD = 0x1;
        break;
      case 60:
        OdtStrenCodePD = 0x3;
        break;
      case 40:
        OdtStrenCodePD = 0x7;
        break;
      case 0:
        OdtStrenCodePD = 0x0;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->OdtImpedanceDq[%d]=%d\n", __func__, pstate, pUserInputAdvanced->OdtImpedanceDq[pstate]);
        break;
    }


    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d OdtImpedanceDq::OdtStrenCodeDqPU to 0x%x\n", __func__, pstate, freq, byte, OdtStrenCodePU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d OdtImpedanceDq::OdtStrenCodeDqPD to 0x%x\n", __func__, pstate, freq, byte, OdtStrenCodePD);
    OdtImpedance = (OdtStrenCodePU << csr_OdtStrenCodeDqPU_LSB) | (OdtStrenCodePD << csr_OdtStrenCodeDqPD_LSB);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_OdtImpedanceDq_ADDR), OdtImpedance);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_OdtImpedanceDq_ADDR), OdtImpedance);

    OdtStrenCodePU = 0;
    OdtStrenCodePD = 0;

    // *** DBYTE DQS *** /
    switch (pUserInputAdvanced->OdtImpedanceDqs[pstate]) {
      case 120:
        OdtStrenCodePD = 0x1;
        break;
      case 60:
        OdtStrenCodePD = 0x3;
        break;
      case 40:
        OdtStrenCodePD = 0x7;
        break;
      case 0:
        OdtStrenCodePD = 0x0;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->OdtImpedanceDqs[%d]=%d\n", __func__, pstate, pUserInputAdvanced->OdtImpedanceDqs[pstate]);
        break;
    }


    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d OdtImpedanceDqs::OdtStrenCodeDqsPU to 0x%x\n", __func__, pstate, freq, byte, OdtStrenCodePU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x%x\n", __func__, pstate, freq, byte, OdtStrenCodePD);
    OdtImpedance = (OdtStrenCodePU << csr_OdtStrenCodeDqsPUT_LSB) | (OdtStrenCodePU << csr_OdtStrenCodeDqsPUC_LSB) | (OdtStrenCodePD << csr_OdtStrenCodeDqsPDT_LSB) | (OdtStrenCodePD << csr_OdtStrenCodeDqsPDC_LSB);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_OdtImpedanceDqs_ADDR), OdtImpedance);

    OdtStrenCodePU = 0;
    OdtStrenCodePD = 0;

      // *** DBYTE WCK *** //
    switch (pUserInputAdvanced->OdtImpedanceWCK[pstate]) {
      case 120:
        OdtStrenCodePD = 0x1;
        break;
      case 60:
        OdtStrenCodePD = 0x3;
        break;
      case 40:
        OdtStrenCodePD = 0x7;
        break;
      case 0:
        OdtStrenCodePD = 0x0;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->OdtImpedanceWCK[%d]=%d\n", __func__, pstate, pUserInputAdvanced->OdtImpedanceWCK[pstate]);
        break;
    }

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d WCK OdtImpedanceDqs::OdtStrenCodeWckPU to 0x%x\n", __func__, pstate, freq, byte, OdtStrenCodePU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x%x\n", __func__, pstate, freq, byte, OdtStrenCodePD);
    OdtImpedance = (OdtStrenCodePU << csr_OdtStrenCodeDqsPUT_LSB) | (OdtStrenCodePU << csr_OdtStrenCodeDqsPUC_LSB) | (OdtStrenCodePD << csr_OdtStrenCodeDqsPDT_LSB) | (OdtStrenCodePD << csr_OdtStrenCodeDqsPDC_LSB);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_OdtImpedanceDqs_ADDR), OdtImpedance);
  } // foreach dbyte
  // End ODT Impedance for DBYTE

  // ********* Start ODT Impedance for AC ********* //
  for (int acx = 0; acx < NumAchnActive; acx++) { // for each AC channel

    OdtStrenCodePU = 0;
    OdtStrenCodePD = 0;

    // *** AC SE *** //
    switch (pUserInputAdvanced->OdtImpedanceCa[pstate]) {
      case 120:
        OdtStrenCodePD = 0x1;
        break;
      case 60:
        OdtStrenCodePD = 0x3;
        break;
      case 40:
        OdtStrenCodePD = 0x7;
        break;
      case 0:
        OdtStrenCodePD = 0x0;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->OdtImpedanceCa[%d]=%d\n", __func__, pstate, pUserInputAdvanced->OdtImpedanceCa[pstate]);
        break;
    }


    OdtImpedance = (OdtStrenCodePU << csr_OdtStrenCodePUAC_LSB) | (OdtStrenCodePD << csr_OdtStrenCodePDAC_LSB);
    //for each ACX_IO + CS
    int c_addr;
    int instance;
    for (int hmac = 0; hmac < 5; hmac++) {
      c_addr = (hmac + acx*NumHmacPerChan)*c1;
      instance = hmac + acx*NumHmacPerChan;
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d SE OdtImpedanceAC::OdtStrenCodePUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, OdtStrenCodePU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d SE OdtImpedanceAC::OdtStrenCodePDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, OdtStrenCodePD);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_OdtImpedanceAC_ADDR), OdtImpedance);
      _PROG_DTO(DtoEnable, acx, hmac, "OdtImpedanceAC", (p_addr | tHMAC | c14 | csr_OdtImpedanceAC_ADDR), OdtImpedance)
    }
    // *** AC DIFF *** //
    switch (pUserInputAdvanced->OdtImpedanceCk[pstate]) {
      case 120:
        OdtStrenCodePD = 0x1;
        break;
      case 60:
        OdtStrenCodePD = 0x3;
        break;
      case 40:
        OdtStrenCodePD = 0x7;
        break;
      case 0:
        OdtStrenCodePD = 0x0;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid pUserInputAdvanced->OdtImpedanceCk[%d]=%d\n", __func__, pstate, pUserInputAdvanced->OdtImpedanceCk[pstate]);
        break;
    }


    OdtImpedance = (OdtStrenCodePU << csr_OdtStrenCodePUAC_LSB) | (OdtStrenCodePD << csr_OdtStrenCodePDAC_LSB);


    for (int hmac = 5; hmac < 7; hmac ++) {
      c_addr = (hmac + acx*NumHmacPerChan)*c1;
      instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d DIFF%d OdtImpedanceAC::OdtStrenCodePUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, OdtStrenCodePU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d DIFF%d OdtImpedanceAC::OdtStrenCodePDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, OdtStrenCodePD);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d DIFF%d OdtImpedanceAC::OdtStrenCodePUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, OdtStrenCodePU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d DIFF%d OdtImpedanceAC::OdtStrenCodePDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, OdtStrenCodePD);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_OdtImpedanceAC_ADDR), OdtImpedance);
    }
   }

  // End ODT Impedance for AC

  /*
   * - Program Tx Slew Rate Control registers
   *   - Description: Program TX slew rate controls
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.TxSlewRiseDq
   *     - user_input_advanced.TxSlewFallDq
   *     - user_input_advanced.TxSlewRiseCA
   *     - user_input_advanced.TxSlewFallCA
   *     - user_input_advanced.TxSlewRiseCK
   *     - user_input_advanced.TxSlewRiseCs
   *     - user_input_advanced.TxSlewFallCs
   */
  uint16_t TxSlewPU = 0;
  uint16_t TxSlewPD = 0;
  uint16_t TxSlew = 0;
  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;

    // *** DBYTE *** //
    TxSlewPU = pUserInputAdvanced->TxSlewRiseDq[pstate];
    TxSlewPD = pUserInputAdvanced->TxSlewFallDq[pstate];

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxDQSlew::TxDQSlewPU to 0x%x\n", __func__, pstate, freq, byte, TxSlewPU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HMDBYTE %d TxDQSlew::TxDQSlewPD to 0x%x\n", __func__, pstate, freq, byte, TxSlewPD);
    TxSlew = (TxSlewPU << csr_TxDQSlewPU_LSB) | (TxSlewPD << csr_TxDQSlewPD_LSB);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_TxDQSlew_ADDR), TxSlew);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_TxDQSlew_ADDR), TxSlew);
  }

  for (int acx = 0; acx < NumAchnActive; acx++) {
    int c_addr;
    int instance;


    //for each ACX_IO
    TxSlewPU = pUserInputAdvanced->TxSlewRiseCA[pstate];
    TxSlewPD = pUserInputAdvanced->TxSlewFallCA[pstate];
    TxSlew = (TxSlewPU << csr_TxSlewPUAC_LSB) | (TxSlewPD << csr_TxSlewPDAC_LSB);
    for (int hmac = 0;hmac < 4; hmac++) {
      c_addr =  (hmac + acx*NumHmacPerChan)*c1;
      instance = hmac + acx*NumHmacPerChan;

      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d SE TxSlewAC::TxSlewPUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxSlewPU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d SE TxSlewAC::TxSlewPDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxSlewPD);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_TxSlewAC_ADDR), TxSlew);
      _PROG_DTO(DtoEnable, acx, hmac, "TxSlewAC", (p_addr | tHMAC | c14 | csr_TxSlewAC_ADDR), TxSlew)
    }

    TxSlewPU = pUserInputAdvanced->TxSlewRiseCS[pstate];
    TxSlewPD = pUserInputAdvanced->TxSlewFallCS[pstate];
    TxSlew = (TxSlewPU << csr_TxSlewPUAC_LSB) | (TxSlewPD << csr_TxSlewPDAC_LSB);

    c_addr =  (4 + acx*NumHmacPerChan)*c1;
    instance = 4 + acx*NumHmacPerChan;

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d CS TxSlewAC::TxSlewPUAC to 0x%x\n", __func__, pstate, freq, acx, 4, instance, TxSlewPU);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d CS TxSlewAC::TxSlewPDAC to 0x%x\n", __func__, pstate, freq, acx, 4, instance, TxSlewPD);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_TxSlewAC_ADDR), TxSlew);

    // *** AC DIFF *** //
    TxSlewPU = pUserInputAdvanced->TxSlewRiseCK[pstate];
    TxSlewPD = pUserInputAdvanced->TxSlewFallCK[pstate];


    TxSlew = (TxSlewPU << csr_TxSlewPUAC_LSB) | (TxSlewPD << csr_TxSlewPDAC_LSB);
    for (int hmac = 5; hmac < NumHmacPerChan; hmac ++) {
      c_addr = (hmac + acx*NumHmacPerChan)*c1;
      instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY (hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d TxSlewAC::TxSlewPUAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxSlewPU);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d TxSlewAC::TxSlewPDAC to 0x%x\n", __func__, pstate, freq, acx, hmac, instance, TxSlewPD);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_TxSlewAC_ADDR), TxSlew);
    }
  } // achn


  /**
   * - Program RxDQSCtrl
   *   - Description: Program single-ended mode controls
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Lp4xMode
   *     - mb1D[ps].MR51_A0[1:1] (LPDDR4 mode)
   *     - mb1D[ps].MR20_A0[1:0] (LPDDR5 mode)
   */
    int RxDQSCtrl;
    uint16_t singleEndedModeRDQS;
    uint8_t RxDiffSeCtrl = 0;
    uint8_t RxDQSDiffSeVrefDACEn = 0;

    singleEndedModeRDQS = (mb1D[pstate].MR20_A0 & 0x3);

    // Check if DQS is in Single-ended mode
    switch (singleEndedModeRDQS) {
      case 0:
        break; // Strobless mode
      case 1: // DQS_t used
        RxDiffSeCtrl = 0x1;
        RxDQSDiffSeVrefDACEn = 0x1;
        break;
      case 2: // differential
        RxDiffSeCtrl = 0x0;
        RxDQSDiffSeVrefDACEn = 0x0;
        break;
      case 3: // DQS_c used
        RxDiffSeCtrl = 0x2;
        RxDQSDiffSeVrefDACEn = 0x1;
        break;
      default:
        dwc_ddrphy_phyinit_assert(0, "[%s] Invalid singleEndedModeRDQS = %d, pstate = %d\n", __func__, singleEndedModeRDQS, pstate);
        break;
    }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMDBYTE RxDQSCtrl::RxDiffSeCtrl to 0x%x\n", __func__, pstate, RxDiffSeCtrl);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMDBYTE RxDQSCtrl::RxDQSDiffSeVrefDACEn to 0x%x\n", __func__, pstate, RxDQSDiffSeVrefDACEn);
  RxDQSCtrl = (RxDiffSeCtrl << csr_RxDiffSeCtrl_LSB) | (RxDQSDiffSeVrefDACEn << csr_RxDQSDiffSeVrefDACEn_LSB);
  for (int byte = 0; byte < NumDbyteActive; byte++) { // for each dbyte
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;

    dwc_ddrphy_phyinit_io_write32(p_addr | (tHMDBYTE | c_addr0 | csr_RxDQSCtrl_ADDR), RxDQSCtrl);
    dwc_ddrphy_phyinit_io_write32(p_addr | (tHMDBYTE | c_addr1 | csr_RxDQSCtrl_ADDR), RxDQSCtrl);
  } // dbyte

    /*
     * - Program WriteLinkEcc
     *   - Description: Enable write link data ECC
     *   - Dependencies:
     *     - user_input_basic.DramType
     *     - user_input_basic.NumCh
     *     - user_input_basic.NumDbytesPerCh
     *     - mb1D[pstate].MR22_A0[5:4]
     */
    regData = ((mb1D[pstate].MR22_A0 & 0x30) == 0x10) ? 0x1 : 0x0;
    dwc_ddrphy_phyinit_cmnt("[%s] Programming WriteLinkEcc to %d\n", __func__, regData);
    for (int byte = 0; byte < NumDbyteActive; byte++) { // for each dbyte
      int c_addr = byte * c1;
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_EnableWriteLinkEcc_ADDR), regData);
    }

  /**
   * - Program PPTTrainSetup, PPTTrainSetup2, PhyMstrFreqOverride:
   *   - Description: Program setup intervals for DFI PHY Master operations
   *   - Fields:
   *     - PhyMstrTrainInterval
   *     - PhyMstrMaxReqToAck
   *     - TxPptMode (RFU)
   *     - RxClkPptMode (RFU)
   *     - PhyMstrFreqOverride
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.PhyMstrTrainInterval
   *     - user_input_advanced.PhyMstrMaxReqToAck
   *     - user_input_advanced.RetrainMode
   */
  uint16_t PhyMstrFreqOverride;
  uint16_t PPTTrainSetup;

  if (freq >= freqThreshold) {
    PPTTrainSetup = (pUserInputAdvanced->PhyMstrTrainInterval[pstate] << csr_PhyMstrTrainInterval_LSB) |
            (pUserInputAdvanced->PhyMstrMaxReqToAck[pstate] << csr_PhyMstrMaxReqToAck_LSB);
    PhyMstrFreqOverride = 0xf;
  } else {
    PhyMstrFreqOverride = 0x0;
    PPTTrainSetup = 0x0;
  }

    uint8_t rdqsMode = mb1D[pstate].MR20_A0 & 0x3;

    if (rdqsMode == 0 && pUserInputAdvanced->PhyMstrTrainInterval[pstate] != 0) {
      dwc_ddrphy_phyinit_assert(0, "[%s] Pstate=%d RDQS cannot be disabled when PHY Master Interface is enabled (PhyMstrTrainInterval=%d)\n", __func__, pstate, pUserInputAdvanced->PhyMstrTrainInterval[pstate]);
    }
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming PPTTrainSetup::PhyMstrTrainInterval to 0x%x\n", __func__, pstate, freq, pUserInputAdvanced->PhyMstrTrainInterval[pstate]);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming PPTTrainSetup::PhyMstrMaxReqToAck to 0x%x\n", __func__, pstate, freq, pUserInputAdvanced->PhyMstrMaxReqToAck[pstate]);
  dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_PPTTrainSetup_ADDR), PPTTrainSetup);


  if (pUserInputAdvanced->RetrainMode[pstate] == 4) {
    uint16_t TxPptMode = (pUserInputAdvanced->RetrainMode[pstate] == 4) ? 1 : 0;
    uint16_t RxClkPptMode = (pUserInputAdvanced->RetrainMode[pstate] == 4) ? 1 : 0;
    for (int byte = 0; byte < NumDbyteActive; byte++) {
      int c_addr = byte * c1;
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming PPTTrainSetup2 to 0x%x\n", __func__, pstate, freq, ((TxPptMode << csr_TxPptMode_LSB) | (RxClkPptMode << csr_RxClkPptMode_LSB)));
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE| c_addr | csr_PPTTrainSetup2_ADDR),  (TxPptMode << csr_TxPptMode_LSB) | (RxClkPptMode << csr_RxClkPptMode_LSB));
    }
  }
  dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_PhyMstrFreqOverride_ADDR), PhyMstrFreqOverride);

  /**
   * - Program RxTrainPattern8BitMode:
   *   - Description: RxGate training pattern match 8-bit/4-bit selection for PPT
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerch
   *     - user_input_basic.DfiFreqRatio
   */
  for (int byte = 0; byte < NumDbyteActive; byte++) { // for each chiplet
    int c_addr = byte * c1;
    uint16_t RxTrnPtrn = (pUserInputBasic->DfiFreqRatio[pstate] == 0x2) ? 0x1 : 0x0;

    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxTrainPattern8BitMode_ADDR), RxTrnPtrn);
  }

  /**
   * - Program RxReplicaRangeVal
   *   - Description: Program controls for RxClk timing modes
   *   - Fields:
   *     - RxReplicaShortCalRangeA
   *     - RxReplicaShortCalRangeB
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t RxReplicaShortRange = ((RxReplicaShortRangeA << csr_RxReplicaShortCalRangeA_LSB) & csr_RxReplicaShortCalRangeA_MASK)
                  | ((RxReplicaShortRangeB << csr_RxReplicaShortCalRangeB_LSB) & csr_RxReplicaShortCalRangeB_MASK);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming RxReplicaRangeVal 0x%x\n", __func__, pstate, RxReplicaShortRange);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr = byte * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxReplicaRangeVal_ADDR), RxReplicaShortRange);
  }



  /**
   * - Program RxReplicaCtl04
   *   - Description: Program RxClkDly tracking of tPHY_tDQS2DQ control for RxReplica
   *   - Fields
   *     - RxReplicaTrackEn
   *     - RxReplicaLongCal
   *     - RxReplicaStride
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t RxReplicaCtl = (0 << csr_RxReplicaTrackEn_LSB) // disable RxClk tracking before training
              | (1 << csr_RxReplicaLongCal_LSB) // long cal during boot
              | (1 << csr_RxReplicaStride_LSB) // Keep the default value of 1 step
              | (0 << csr_RxReplicaPDenFSM_LSB); // FSM-driven RxReplica Receiver Powerdown is not needed due to HM port RxReplica_RxPowerDown_DQS removed.
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming RxReplicaCtl04 0x%x\n", __func__, pstate, RxReplicaCtl);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr = c1 * byte;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxReplicaCtl04_ADDR), RxReplicaCtl);
  }

  /**
   * - Program PipeCtl
   *   - Description: Program delay enables for PIPE block
   *   - Fields:
   *     - DxInPipeEn
   *     - DxOutPipeEn
   *     - AcInPipeEn
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_advanced.DxInPipeEn
   *     - user_input_advanced.DxOutPipeEn
   *     - user_input_advanced.AcInPipeEn
   */
  uint16_t DxOutPipeEn         = 0x0;
  uint16_t DxInPipeEn          = 0x0;
  uint16_t AlertNPipeEn        = 0x0;
  uint16_t AcInPipeEn          = 0x0;
  uint16_t PipeCtl             = 0x0;
  uint16_t NumDxInPipeEn       = 0x0;
  uint16_t NumAcInPipeEn       = 0x0;
  uint16_t MiscPipeEn          = 0x0;
  uint16_t NumMiscPipeEn       = 0x0;
  uint16_t LP5DfiDataEnLatency = 0x0;
  uint16_t LP5RLm13            = 0x0;

    if (DataRateMbps > 3200) {
      LP5RLm13 = csr_LP5RLm13_MASK;
    } else {
      LP5RLm13 = 0;
    }

  uint16_t DfiFreq = freq;

  if (DfiFreq > 800) {
    DxOutPipeEn = 1;
    DxInPipeEn = 1;
    AcInPipeEn = 1;
  }

  // Override the calculated values if user input is set (note that AcInPipeEn = DxInPipeEn for LPDDR5 only, unless overridden from userInput)
  DxInPipeEn = (pUserInputAdvanced->DxInPipeEnOvr == 1) ? pUserInputAdvanced->DxInPipeEn[pstate] : DxInPipeEn;
  DxOutPipeEn = (pUserInputAdvanced->DxOutPipeEnOvr == 1) ? pUserInputAdvanced->DxOutPipeEn[pstate] : DxOutPipeEn;
  AlertNPipeEn = (pUserInputAdvanced->AlertNPipeEnOvr == 1) ? pUserInputAdvanced->AlertNPipeEn[pstate] : AlertNPipeEn;
  AcInPipeEn = (pUserInputAdvanced->AcInPipeEnOvr == 1) ? pUserInputAdvanced->AcInPipeEn[pstate] : AcInPipeEn;

  // Save the number of pipeline stages for other steps of PHYINIT to use
  pRuntimeConfig->NumDxOutPipeEn[pstate]  = dwc_ddrphy_phyinit_getNumPipeStages(DxOutPipeEn);
  pRuntimeConfig->NumDxInPipeEn[pstate]   = dwc_ddrphy_phyinit_getNumPipeStages(DxInPipeEn);
  pRuntimeConfig->NumAlertNPipeEn[pstate] = dwc_ddrphy_phyinit_getNumPipeStages(AlertNPipeEn);
  pRuntimeConfig->NumAcInPipeEn[pstate]   = dwc_ddrphy_phyinit_getNumPipeStages(AcInPipeEn);

  // Save AcInPipeEn/DxInPipeEn number of pipeline stages for other parts of PHYINIT to use (e.g. ACSM timing)
  NumAcInPipeEn = pRuntimeConfig->NumAcInPipeEn[pstate];
  NumDxInPipeEn = pRuntimeConfig->NumDxInPipeEn[pstate];

  PipeCtl = ((AcInPipeEn<<csr_AcInPipeEn_LSB) | (AlertNPipeEn<<csr_AlertNPipeEn_LSB) | (DxInPipeEn<<csr_DxInPipeEn_LSB) | (DxOutPipeEn<<csr_DxOutPipeEn_LSB));
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming PipeCtl[DxOutPipeEn]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, DxOutPipeEn, pUserInputBasic->DfiFreqRatio[pstate]);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming PipeCtl[DxInPipeEn]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, DxInPipeEn, pUserInputBasic->DfiFreqRatio[pstate]);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming PipeCtl[AlertNPipeEn]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, AlertNPipeEn, pUserInputBasic->DfiFreqRatio[pstate]);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming PipeCtl[AcInPipeEn]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, AcInPipeEn, pUserInputBasic->DfiFreqRatio[pstate]);
  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_PipeCtl_ADDR), PipeCtl);

    /**
     * - Program LP5DfiDataEnLatency:
     *   - Description: Program the depth of the data pipes in the PUB relative to AC pipes
     *   - Fields:
     *     - LP5RLm13
     *   - Dependencies:
     *     - user_input_basic.DramType
     *     - user_input_basic.NumCh
     *     - user_input_basic.NumDbytesPerCh
     */
    for (int byte = 0; byte < NumDbyteActive; byte++) {
      int c_addr = c1 * byte;

      LP5DfiDataEnLatency = LP5RLm13<< csr_LP5RLm13_LSB;
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming DBYTE%d.LP5DfiDataEnLatency[LP5RLm13]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, byte, LP5RLm13, pUserInputBasic->DfiFreqRatio[pstate]);
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_LP5DfiDataEnLatency_ADDR), LP5DfiDataEnLatency);
    }
  MiscPipeEn = 0x0;
  // Save the number of pipeline stages for other steps of PHYINIT to use
  pRuntimeConfig->NumMiscPipeEn[pstate] = dwc_ddrphy_phyinit_getNumPipeStages(MiscPipeEn);
  NumMiscPipeEn = pRuntimeConfig->NumMiscPipeEn[pstate];

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, NumDxOutPipeEn=%d, NumDxInPipeEn=%d, NumAlertNPipeEn=%d, NumAcInPipeEn=%d, NumMiscPipeEn=%d\n",
                              __func__, pstate, freq, DfiFreq, pRuntimeConfig->NumDxOutPipeEn[pstate], pRuntimeConfig->NumDxInPipeEn[pstate], pRuntimeConfig->NumAlertNPipeEn[pstate], pRuntimeConfig->NumAcInPipeEn[pstate], pRuntimeConfig->NumMiscPipeEn[pstate]);

  /**
   * - Program DfiRespHandshakeDelays0,1, DfiHandshakeDelays0,1:
   *   - Description: Program delays on handshake signals per AC channel
   *   - Fields:
   *     - LpCtrlAckDelay
   *     - LpDataAckDelay
   *     - CtrlUpdReqDelay
   *     - CtrlUpdAckDelay
   *     - PhyUpdReqDelay
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_advanced.DxInPipeEn
   *     - user_input_advanced.AcInPipeEn
   *     - user_input_advanced.CtrlUpdReqDelay
   *     - user_input_advanced.CtrlUpdAckDelay
   */
  uint16_t LpDataAckDelay;
  uint16_t LpCtrlAckDelay;
  uint16_t CtrlUpdAckDelay;
  uint16_t PhyUpdReqDelay; //needs to reenable once after lp5 tb changes.
  uint16_t DfiHandshakeDelays; //needs to reenable once after lp5 tb changes.
  uint16_t DfiRespHandshakeDelays;
  uint16_t M0;

    uint16_t CtrlUpdReqDelay;
    M0 =  1;
    LpDataAckDelay = (((NumMiscPipeEn + 2 * M0) - NumDxInPipeEn)> 0) ? ((NumMiscPipeEn + 2 * M0) - NumDxInPipeEn) : 0;
    LpCtrlAckDelay = (((NumMiscPipeEn + 2 * M0) - NumAcInPipeEn)> 0) ? ((NumMiscPipeEn + 2 * M0) - NumAcInPipeEn) : 0;
    CtrlUpdReqDelay = (pUserInputAdvanced->UseSnpsController && pUserInputAdvanced->EnWck2DqoTracking[pstate]) ? (((6*tck_ps) > 9000.0) ? 6 : (int)ceil(9000.0/tck_ps)) : 0; // UseSnpsController=1 and MRR Snoop enabled: Round-up(Max(9ns, 6nCK)/tCK); UseSnpsController=0: 0
    CtrlUpdAckDelay = (pUserInputAdvanced->UseSnpsController && pUserInputAdvanced->EnWck2DqoTracking[pstate]) ? (((3*tck_ps) > 7000.0) ? 5 : ((int)ceil(7000.0/tck_ps) + 2)) : ((((NumMiscPipeEn + 2 * M0) - NumAcInPipeEn)> 0) ? ((NumMiscPipeEn + 2 * M0) - NumAcInPipeEn) : 0); // UseSnpsController=1 and MRR Snoop enabled: 2 + Round-up(Max(7ns, 3nCK)/tCK);  UseSnpsController=0: calculated with pipe
    PhyUpdReqDelay =  (((NumMiscPipeEn + 2 * M0) - NumAcInPipeEn)> 0) ? ((NumMiscPipeEn + 2 * M0) - NumAcInPipeEn) : 0; //needs to reenable once after lp5 tb changes.

    DfiRespHandshakeDelays = CtrlUpdAckDelay << csr_CtrlUpdAckDelay0_LSB | LpDataAckDelay<< csr_LpDataAckDelay0_LSB | LpCtrlAckDelay<< csr_LpCtrlAckDelay0_LSB;
    DfiHandshakeDelays = (pUserInputAdvanced->UseSnpsController && pUserInputAdvanced->EnWck2DqoTracking[pstate]) ? (CtrlUpdReqDelay << csr_CtrlUpdReqDelay0_LSB | PhyUpdReqDelay << csr_PhyUpdReqDelay0_LSB) : (PhyUpdReqDelay << csr_PhyUpdReqDelay0_LSB); //needs to reenable once after lp5 tb changes. Program CtrlUpdReqDelay only when UseSnpsController=1 and MRR Snoop enabled.

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming DfiRespHandshakeDelays[LpDataAckDelay]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, LpDataAckDelay, pUserInputBasic->DfiFreqRatio[pstate]);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming DfiRespHandshakeDelays[LpCtrlAckDelay]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, LpCtrlAckDelay, pUserInputBasic->DfiFreqRatio[pstate]);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming DfiRespHandshakeDelays[CtrlUpdAckDelay]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, CtrlUpdAckDelay, pUserInputBasic->DfiFreqRatio[pstate]);
    if (pUserInputAdvanced->UseSnpsController && pUserInputAdvanced->EnWck2DqoTracking[pstate]) {
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming DfiHandshakeDelays[CtrlUpdReqDelay]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, CtrlUpdReqDelay, pUserInputBasic->DfiFreqRatio[pstate]);
    }
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, DfiFreq=%dMHz, Programming DfiHandshakeDelays[PhyUpdReqDelay]=0x%x DFI ratio is %d\n", __func__, pstate, freq, DfiFreq, PhyUpdReqDelay, pUserInputBasic->DfiFreqRatio[pstate]); //needs to reenable once after lp5 tb changes.
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_DfiRespHandshakeDelays0_ADDR), DfiRespHandshakeDelays);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_DfiHandshakeDelays0_ADDR), DfiHandshakeDelays); //needs to reenable once after lp5 tb changes.
    if (NumAchnActive > 1) {
      dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_DfiRespHandshakeDelays1_ADDR), DfiRespHandshakeDelays);
      dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_DfiHandshakeDelays1_ADDR), DfiHandshakeDelays); //needs to reenable once after lp5 tb changes.
    }


  // Program ACSM Delay for LP5/X/4
  dwc_ddrphy_phyinit_ACSM_delay(phyctx, pstate, "[phyinit_C_initPhyConfigPsLoop]");

  /* - Register EnaRxStrobeEnB
   *   - Description: Program enables for RxEn strobe to be clocked by odd-phyase Pclk reg for 1UI delay adjustment
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_basic.Frequency
   */
  // for each chiplet
  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;
    regData = (DataRateMbps < 2667) ? 0x1 : 0x0;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming csr_EnaRxStrobeEnB to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr0 | tHMDBYTE | csr_EnaRxStrobeEnB_ADDR), regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr1 | tHMDBYTE | csr_EnaRxStrobeEnB_ADDR), regData);
  }


  if (pUserInputAdvanced->DisablePclkDca == 0) {
    if (DataRateMbps > 3200) {
      dwc_ddrphy_phyinit_programPclkDca(phyctx, pstate);
    }
  }

  /* - Program RxDFECtrlDq:
   *   - Description: Program mode bits for DFE
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.RxDFECtrlDq
   */
  uint8_t RxDFECtrlDq = pUserInputAdvanced->RxDFECtrlDq[pstate];

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMDBYTE RxDFECtrlDq to 0x%x\n", __func__, pstate, RxDFECtrlDq);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_RxDFECtrlDq_ADDR), RxDFECtrlDq);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_RxDFECtrlDq_ADDR), RxDFECtrlDq);
  }

  /**
   * - Program InhibitTxRdPtrInit based on Frequency and SkipFlashCopy
   *   - Description: Program prevention of TxRdPtrInit from affecting parts of the PHY
   *   - Fields:
   *     - DisableRxEnDlyLoad
   *     - DisableTxDqDly
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_basic.Frequency
   *     - user_input_advanced.DisableRetraining
   */
    dwc_ddrphy_phyinit_cmnt ("[%s] Programming InhibitRxRdPtrInit*\n", __func__);

    uint16_t DisableRxEnDlyLoad;
    uint16_t DisableTxDqDly;

    // Enable only if above frequency threshould, and current Pstate is not strobe-less mode
    DisableRxEnDlyLoad = pUserInputAdvanced->DisableRetraining==0 ? ((freq<freqThreshold || (NoRDQS != 0)) ? 0 : 1) : 0;
    DisableTxDqDly = pUserInputAdvanced->DisableRetraining==0 ? ((freq<freqThreshold || (NoRDQS != 0)) ? 0 : 1) : 0;

    dwc_ddrphy_phyinit_cmnt ("[%s] Pstate=%d, Memclk=%dMHz, freqThreshold=%dMHz, NoRDQS=%d Programming InhibitTxRdPtrInit::DisableRxEnDlyLoad to 0x%x, InhibitTxRdPtrInit::DisableTxDqDly to 0x%x\n", __func__, pstate, freq, freqThreshold, NoRDQS, DisableRxEnDlyLoad, DisableTxDqDly);
    regData = ((DisableRxEnDlyLoad << csr_DisableRxEnDlyLoad_LSB) | (DisableTxDqDly << csr_DisableTxDqDly_LSB));

    for (int byte = 0; byte < NumDbyteActive; byte++) {
      int c_addr = byte * c1;
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_InhibitTxRdPtrInit_ADDR), regData);
    }



  /**
   * - Program LpDqPowerDnDly:
   *   - Description: Program 5ns delay
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_advanced.EnLpRxDqPowerDown
   */


 
    dwc_ddrphy_phyinit_programLCDLSeed(phyctx, 0, "[phyinit_C_initPhyConfigPsLoop]");
    
  /*
   * - Program UcclkHclkEnables:
   *   - Description: Program UcClk full or half rate
   *   - Fields:
   *     - UcclkFull
   *   - Dependencies:
   *     - user_input_advanced.PmuClockDiv
   */
  uint16_t pmuClkEnables = csr_HclkEn_MASK | csr_UcclkEn_MASK;
  if (pUserInputAdvanced->PmuClockDiv[pstate] == 0) {
    pmuClkEnables |= csr_UcclkFull_MASK;
  }
  dwc_ddrphy_phyinit_cmnt("[%s] Programming UcclkHclkEnables to 0x%x\n", __func__, pmuClkEnables);
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save UcclkHclkEnables to S3 list as if this
  //       CSR is progrmamed at the begining/end of dwc_ddrphy_phyinit_restore_sequence in dwc_ddrphy_phyinit_restore_sequence.c.
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  /*
   * - Program RxDQSSeVrefDAC0
   *   - Description: Program RX VREF controls for TXRXDQ
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t RxDQSSeVrefDAC0 = 0x80;


  dwc_ddrphy_phyinit_cmnt("[%s] Programming RxDQSSeVrefDAC0 to 0x%x\n", __func__, RxDQSSeVrefDAC0 );

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_RxDQSSeVrefDAC0_ADDR), RxDQSSeVrefDAC0);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_RxDQSSeVrefDAC0_ADDR), RxDQSSeVrefDAC0);

  }


  /**
   * - Program Seq0BGPR23:
   *   - Description: Save ACSMOuterLoopRepeatCnt to GPR23 to achieve tRFCab delay of tXSR
   *                  tRFCab - 380ns when Enhanced DVFSC disabled (dvfsc = 0/1); 
   *                         - 410ns when Enhanced DVFSC enabled (dvfsc = 2).
   *                  tXSR = tRFCab + Max(7.5ns, 2nCK)
   *                  NumMemClk = (ACSMOuterLoopRepeatCnt + 1) * 4
   *   - Dependencies:
   *     - pUserInputBasic->Frequency[pstate]
   */
  float NumMemClk_tRFCab =  410.0 * pUserInputBasic->Frequency[pstate] / 1000; 
  float NumMemClk_7p5ns  = 7.5 * pUserInputBasic->Frequency[pstate] / 1000;
  float NumMemClk_tXSR   = NumMemClk_tRFCab + (NumMemClk_7p5ns > 2 ? NumMemClk_7p5ns : 2);
  int   RepeatCntr = ceil(NumMemClk_tXSR / 4.0) - 1;
  if (RepeatCntr < 0) {RepeatCntr = 0;}
  dwc_ddrphy_phyinit_cmnt("[%s] Programming PState %d Seq0BGPR23 to 0x%x, NumMemClk_tRFCab=%.1f, NumMemClk_7p5ns=%.1f, NumMemClk_tXSR=%.1f\n", __func__, pstate, RepeatCntr, NumMemClk_tRFCab, NumMemClk_7p5ns, NumMemClk_tXSR);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR23_ADDR), RepeatCntr << csr_ACSMOuterLoopRepeatCnt_LSB);

  /**
   * - Program Seq0BGPR24:
   *   - Description: Save CK singleEndedMode to GPR24 to indicate CK singleEndedMode to the PIE
   *   - Dependencies:
   *     - mb1D[ps].MR1_A0[3:3]
   */
  regData = (mb1D[pstate].MR1_A0 & 0x08u) >> 3; // CK SingleEndedMode
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR24_ADDR), regData << csr_SingleEndedCK_LSB);

  /**
   * - Program Seq0BGPR25:
   *   - Description: Save WCK singleEndedMode to GPR25 to indicate WCK singleEndedMode to the PIE
   *   - Dependencies:
   *     - mb1D[ps].MR20_A0[3:2]
   */
  regData = (mb1D[pstate].MR20_A0 & 0x0cu) >> 2; // WCK SingleEndedMode
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR25_ADDR), regData << csr_SingleEndedWCK_LSB);


  /**
   * - Program AcLcdlUpdInterval:
   *   - Description: Disable controls for the clock ACX2 DLLs
   *   - Dependencies:
   *     - None
   */
  regData = 0x0000;
  dwc_ddrphy_phyinit_cmnt("[%s] Programming PState %d AC0 AcLcdlUpdInterval to 0x%x\n", __func__, pstate, regData);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tAC | csr_AcLcdlUpdInterval_ADDR), regData);
  if (NumAchn > 1) {
    dwc_ddrphy_phyinit_cmnt("[%s] Programming PState %d AC1 AcLcdlUpdInterval to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | c1 | tAC | csr_AcLcdlUpdInterval_ADDR), regData);
  }

  /**
  * - Program ZCalStopClk:
  *   - Description: 
  *   - Fields:
  *     - ZCalStopClk
  *   - Dependencies:
  *     - user_input_advanced.PHYZCalPowerSaving
  */
  uint16_t ZCalStopClk = ((pUserInputAdvanced->PHYZCalPowerSaving) && (DataRateMbps<=3200)) ? 1 : 0;

  if (ZCalStopClk == 1) {
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, DataRateMbps=%d, Programming ZCalStopClk to 0x%x\n", __func__, pstate, DataRateMbps, ZCalStopClk);

    // Note: S3 waiver
    //       Purposely using userCustom_io_write32(), do not want to save ZCalStopClk to S3 list as if this
    //       CSR restored prior to HMZCAL CSR, HMZCAL will not be restored. 
    //       This CSR will be restored at the end of restore sequence 
    //       dwc_ddrphy_phyinit_restore_sequence.c
    dwc_ddrphy_phyinit_userCustom_io_write32((p_addr | tZCAL | csr_ZCalStopClk_ADDR), ZCalStopClk);
  } 
  // Disable DFI channels based on userInput
  dwc_ddrphy_phyinit_programDfiMode(phyctx, disableDfiMode);
  
  dwc_ddrphy_phyinit_cmnt("End of %s(), Pstate=%d\n", __func__, pstate);

} // End of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop()



 
  /** \brief Program the ACSM Latency Delays that the PIE/ACSM will use when doing PPT
   *
   * - Program ACSMWckWriteStaticLoPulse, ACSMWckWriteStaticHiPulse, ACSMWckWriteTogglePulse, ACSMWckWriteFastTogglePulse, ACSMWckReadStaticLoPulse, ACSMWckReadStaticHiPulse, ACSMWckReadTogglePulse
   *           ACSMWckReadFastTogglePulse, ACSMWckFreqSwStaticLoPulse, ACSMWckFreqSwStaticHiPulse, ACSMWckFreqSwTogglePulse, ACSMWckFreqSwFastTogglePulse:
   *   - Description: Program timing parameters for ACSM
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.DramDataWidth
   *     - mb1D[ps].MR19_A0[1:0]
   *     - mb1D[ps].MR22_A0[7:6]
   *     - mb1D[ps].MR21_A0[5:4]
   *     - mb1D[ps].MR3_A0[5:5]
   *     - mb1D[ps].MR10_A0[3:2]
   *
   * \param phyctx	 Data structure to hold user-defined parameters
   * \param pstate	 Current PState being executed
   * \param print_header String used for logging
   *
   * \return void
   */
void dwc_ddrphy_phyinit_ACSM_delay(phyinit_config_t *phyctx, uint8_t pstate, const char* print_header)
{

  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;

  uint16_t freq = pUserInputBasic->Frequency[pstate];
  const char* h = print_header;
  uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
  uint32_t p_addr = (uint32_t) pstate << 20;

  dwc_ddrphy_phyinit_cmnt("Start of %s(), PState=%d\n", __func__, pstate);

  /**
   * - Program ACSMWckWriteStaticLoPulse, ACSMWckWriteStaticHiPulse, ACSMWckWriteTogglePulse, ACSMWckWriteFastTogglePulse, ACSMWckReadStaticLoPulse, ACSMWckReadStaticHiPulse, ACSMWckReadTogglePulse
   *           ACSMWckReadFastTogglePulse, ACSMWckFreqSwStaticLoPulse, ACSMWckFreqSwStaticHiPulse, ACSMWckFreqSwTogglePulse, ACSMWckFreqSwFastTogglePulse:
   *   - Description: Program timing parameters for ACSM
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.DramDataWidth
   *     - mb1D[ps].MR19_A0[1:0]
   *     - mb1D[ps].MR22_A0[7:6]
   *     - mb1D[ps].MR21_A0[5:4]
   *     - mb1D[ps].MR3_A0[5:5]
   *     - mb1D[ps].MR10_A0[3:2]
   */
  const uint16_t RD_AC_FREQ_LOWER = 0;
  const uint16_t RD_AC_FREQ_UPPER = 1;
  const uint16_t RD_AC_RL_SETA = 2;
  const uint16_t RD_AC_RL_SETB = 3;
  const uint16_t RD_AC_RL_SETC = 4;
  const uint16_t RD_AC_TWCKENL_RD_SETA = 5;
  const uint16_t RD_AC_TWCKENL_RD_SETB = 6;
  const uint16_t RD_AC_TWCKENL_RD_SETC = 7;
  const uint16_t RD_AC_TWCKENL_RD_ECC_A = 5;
  const uint16_t RD_AC_TWCKENL_RD_ECC_B = 6;
  const uint16_t RD_AC_TWCKEPRE_STATIC = 8;
  const uint16_t RD_AC_TWCKEPRE_TOGGLE_RD = 9;
  const uint16_t FS_AC_TWCKENL_FS = 3;
  const uint16_t WR_AC_WL_SETA = 2;
  const uint16_t WR_AC_WL_SETB = 3;
  const uint16_t WR_AC_TWCKENL_WR_SETA = 4;
  const uint16_t WR_AC_TWCKENL_WR_SETB = 5;
  const uint16_t WR_AC_TWCKEPRE_TOGGLE_WR = 7;
  
  //WCK2CK Sync AC Parameters for Read operation
  // DVFSC disabled, Read Link ECC disabled
  static const uint16_t WCK2CK_Sync_RD_lookup_A[2][15][11] = {
    {
      {10, 133, 6, 6, 6, 0, 0, 0, 1, 6, 7},
      {133, 267, 8, 8, 8, 0, 0, 0, 2, 7, 9},
      {267, 400, 10, 10, 12, 1, 1, 3, 2, 8, 10},
      {400, 533, 12, 14, 14, 2, 4, 4, 3, 8, 11},
      {533, 688, 16, 16, 18, 3, 3, 5, 4, 10, 14},
      {688, 800, 18, 20, 20, 5, 7, 7, 4, 10, 14},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    }, {
      {5, 67, 3, 3, 3, 0, 0, 0, 1, 3, 4},
      {67, 133, 4, 4, 4, 0, 0, 0, 1, 4, 5},
      {133, 200, 5, 5, 6, 1, 1, 2, 1, 4, 5},
      {200, 267, 6, 7, 7, 1, 2, 2, 2, 4, 6},
      {267, 344, 8, 8, 9, 2, 2, 3, 2, 5, 7},
      {344, 400, 9, 10, 10, 3, 4, 4, 2, 5, 7},
      {400, 467, 10, 11, 12, 3, 4, 5, 3, 5, 8},
      {467, 533, 12, 13, 14, 4, 5, 6, 3, 6, 9},
      {533, 600, 13, 14, 15, 5, 6, 7, 3, 6, 9},
      {600, 688, 15, 16, 17, 6, 7, 8, 4, 6, 10},
      {688, 750, 16, 17, 19, 6, 7, 9, 4, 7, 11},
      {750, 800, 17, 18, 20, 7, 8, 10, 4, 7, 11},
      {800, 937, 20, 22, 24, 7, 9, 11, 5, 9, 14},
      {937, 1066, 23, 25, 26, 8, 10, 11, 6, 10, 16},
      {1066, 1200, 25, 28, 29, 8, 11, 12, 7, 11, 18}
    }
  };
  
  // WCK2CK Sync AC Parameters for Read operation
  // DVFSC enabled, Read Link ECC disabled
  static const uint16_t WCK2CK_Sync_RD_lookup_B[2][3][11] = {
    {
      {10, 133, 6, 6, 6, 0, 0, 0, 1, 6, 7},
      {133, 267, 8, 10, 10, 0, 2, 2, 2, 7, 9},
      {267, 400, 12, 12, 14, 3, 3, 5, 2, 8, 10}
    }, {
      {5, 67, 3, 3, 3, 0, 0, 0, 1, 3, 4},
      {67, 133, 4, 5, 5, 0, 1, 1, 1, 4, 5},
      {133, 200, 6, 6, 7, 2, 2, 3, 1, 4, 5}
    }
  };

  //WCK2CK Sync AC Parameters for Read operation
  // DVFSC disabled, Read Link ECC enabled
  static const uint16_t WCK2CK_Sync_RD_lookup_C[1][9][11] = {
    {
      {400, 467, 12, 13, 0, 5, 6, 0, 3, 5, 8},
      {467, 533, 13, 14, 0, 5, 6, 0, 3, 6, 9},
      {533, 600, 15, 16, 0, 7, 8, 0, 3, 6, 9},
      {600, 688, 17, 18, 0, 8, 9, 0, 4, 6, 10},
      {688, 750, 18, 20, 0, 8, 10, 0, 4, 7, 11},
      {750, 800, 19, 21, 0, 9, 11, 0, 4, 7, 11},
      {800, 937, 23, 24, 0, 10, 11, 0, 5, 9, 14},
      {937, 1066, 26, 28, 0, 11, 13, 0, 6, 10, 16},
      {1066, 1200, 29, 30, 0, 12, 13, 0, 7, 11, 18}
    }
  };

  // WCK2CK Sync AC Parameters for Read operation
  // Enhanced DVFSC enabled, Read Link ECC disabled
  static const uint16_t WCK2CK_Sync_RD_lookup_D[2][6][11] = {
    {
      { 10, 133,  6,  6,  6,  0,  0,  0, 1,  6,  7},
      {133, 267,  9, 10, 10,  1,  2,  2, 2,  7,  9},
      {267, 400, 13, 13, 14,  4,  4,  5, 2,  8, 10},
      {400, 533, 16, 16, 20,  6,  6, 10, 3,  8, 11},
      {533, 688, 20, 20, 24,  7,  7, 11, 4, 10, 14},
      {688, 800, 24, 24, 28, 11, 11, 15, 4, 10, 14}
    }, {
      {  5,  67,  3,  3,  3, 0, 0, 0, 1, 3, 4},
      { 67, 133,  5,  5,  5, 1, 1, 1, 1, 4, 5},
      {133, 200,  7,  7,  7, 3, 3, 3, 1, 4, 5},
      {200, 267,  8,  8, 10, 3, 3, 5, 2, 4, 6},
      {267, 344, 10, 10, 12, 4, 4, 6, 2, 5, 7},
      {344, 400, 12, 12, 14, 6, 6, 8, 2, 5, 7}
    }
  }; 

  // WCK2CK Sync AC Parameters for WRITE operation
  static const uint16_t WCK2CK_Sync_WR_lookup[2][15][9] = {
    {
      {10, 133, 4, 4, 1, 1, 1, 3, 4},
      {133, 267, 4, 6, 0, 2, 2, 3, 5},
      {267, 400, 6, 8, 1, 3, 2, 4, 6},
      {400, 533, 8, 10, 2, 4, 3, 4, 7},
      {533, 688, 8, 14, 1, 7, 4, 4, 8},
      {688, 800, 10, 16, 3, 9, 4, 4, 8},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0}
    }, {
      {5, 67, 2, 2, 0, 0, 1, 2, 3},
      {67, 133, 2, 3, 0, 1, 1, 2, 3},
      {133, 200, 3, 4, 1, 2, 1, 2, 3},
      {200, 267, 4, 5, 1, 2, 2, 2, 4},
      {267, 344, 4, 7, 1, 4, 2, 2, 4},
      {344, 400, 5, 8, 2, 5, 2, 2, 4},
      {400, 467, 6, 9, 2, 5, 3, 2, 5},
      {467, 533, 6, 11, 2, 7, 3, 2, 5},
      {533, 600, 7, 12, 3, 8, 3, 2, 5},
      {600, 688, 8, 14, 3, 9, 4, 2, 6},
      {688, 750, 9, 15, 4, 10, 4, 2, 6},
      {750, 800, 9, 16, 4, 11, 4, 2, 6},
      {800, 937, 11, 19, 5, 13, 5, 2, 7},
      {937, 1066, 12, 22, 5, 15, 6, 2, 8},
      {1066,1200, 14, 24, 6, 16, 7, 2, 9}
    }
  };

  //WCK2CK Sync AC Parameters for CAS(WS_FS=1)
  static const uint16_t WCK2CK_Sync_FS_lookup[2][15][5] = {
    {
      {10, 133, 0x0, 0, 1},
      {133, 267, 0x1, 0, 2},
      {267, 400, 0x2, 1, 2},
      {400, 533, 0x3, 1, 3},
      {533, 688, 0x4, 1, 4},
      {688, 800, 0x5, 2, 4},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0}
    }, {
      {5, 67, 0x0, 0, 1},
      {67, 133, 0x1, 0, 1},
      {133, 200, 0x2, 1, 1},
      {200, 267, 0x3, 1, 2},
      {267, 344, 0x4, 1, 2},
      {344, 400, 0x5, 1, 2},
      {400, 467, 0x6, 1, 3},
      {467, 533, 0x7, 1, 3},
      {533, 600, 0x8, 2, 3},
      {600, 688, 0x9, 2, 4},
      {688, 750, 0xa, 2, 4},
      {750, 800, 0xb, 2, 4},
      {800, 937, 0xc, 3, 5},
      {937, 1066, 0xd, 3, 6},
      {1066, 1200, 0xe, 3, 7}
    }
  };

    const uint16_t *WCK2CK_Sync_RD_lookup;
    uint16_t RD_AC_RL;
    uint16_t WR_AC_WL;
    uint16_t RD_AC_TWCKENL_RD;
    uint16_t WR_AC_TWCKENL_WR;
    uint16_t BLnmax;
    uint16_t tWCKPST;
    uint8_t ratioIndex;
	uint16_t Dfiratio = pUserInputBasic->DfiFreqRatio[pstate];
    uint16_t ratio = 1u << Dfiratio;
    uint8_t numSpeeds;
    uint8_t RD_AC_RL_DBI;

    uint16_t BLdiv2 = 8;
    uint16_t readLatency = 3;
    uint8_t readLatencyDbi = 3;
    uint16_t writeLatency = 3;
    uint16_t tWCKENL_WR = 0;
    uint16_t tWCKENL_RD = 0;
    uint16_t tWCKENL_FS = 0;
    uint16_t tWCKPRE_static = 2;
    uint16_t tWCKPRE_Toggle_WR = 3;
    uint16_t tWCKPRE_Toggle_RD = 6;
    uint16_t tWCKPRE_Toggle_FS = 3;

    uint8_t dvfsc = mb1D[pstate].MR19_A0 & 0x3u; // MR19 OP[1:0] DVFSC, 'b00 : DVFSC disabled; 'b01 : DVFSC mode; 'b10 : Enhanced DVFSC mode
    uint8_t readLinkEcc = (mb1D[pstate].MR22_A0 >> 6) & 0x3u;
    uint8_t readDbi = (mb1D[pstate].MR3_A0 >> 6) & 1u;
    uint8_t readCpy = (mb1D[pstate].MR21_A0 >> 5) & 1u;
    uint8_t readEither = (readDbi | readCpy) & 1u;
    uint8_t wls = (mb1D[pstate].MR3_A0 >> 5) & 1u;
    uint8_t bankOrg = (mb1D[pstate].MR3_A0 >> 3) & 0x3u; // MR3  OP[4:3] BK/BG ORG, b00 : BG mode, b10 : 16B mode, b01 8B mode
    uint8_t byteMode = (pUserInputBasic->DramDataWidth == 8) ? 1 : 0;

    uint16_t rxPulseDly;
    uint16_t rxPulseDlyDbi;
    uint16_t rxPulseWd;

    if ( (dvfsc == 2) && (( DataRateMbps< 40) || ( DataRateMbps > 3200)) ) {
      dwc_ddrphy_phyinit_assert(0, "[%s] %s Enhanced DVFSC enable, invalid DataRateMbps = %d. Please set DataRateMbps >= 40MHz && DataRateMbps <=3200MHz.\n", __func__, h, DataRateMbps);
    } else if ( (dvfsc == 1) && (( DataRateMbps < 40) || (DataRateMbps> 1600)) ) {
      dwc_ddrphy_phyinit_assert(0, "[%s] %s DVFSC enable, invalid DataRateMbps = %d. Please set DataRateMbps >= 40MHz && DataRateMbps <=1600MHz.\n", __func__, h, DataRateMbps);
    } else {
      dwc_ddrphy_phyinit_cmnt("[%s] %s Enhanced DVFSC %s, DVFSC %s, DataRateMbps = %d\n", __func__, h, (dvfsc==2?"Enabled":"Disabled"), (dvfsc==1?"Enabled":"Disabled"),  DataRateMbps);
    }

    if (dvfsc == 2) { // Enhanced DVFSC mode
      ratioIndex = ratio == 2 ? 0 : 1;
      numSpeeds = 6;
      WCK2CK_Sync_RD_lookup = WCK2CK_Sync_RD_lookup_D[ratioIndex][0];
    } else if (dvfsc == 1) { // DVFSC mode
      ratioIndex = ratio == 2 ? 0 : 1;
      numSpeeds = 3;
      WCK2CK_Sync_RD_lookup = WCK2CK_Sync_RD_lookup_B[ratioIndex][0];
    } else if (readLinkEcc) {
      ratioIndex = 0;
      numSpeeds = 9;
      WCK2CK_Sync_RD_lookup = WCK2CK_Sync_RD_lookup_C[ratioIndex][0];
    } else {
      ratioIndex = ratio == 2 ? 0 : 1;
      numSpeeds = (ratioIndex != 0u) ? 15 : 6;
      WCK2CK_Sync_RD_lookup = WCK2CK_Sync_RD_lookup_A[ratioIndex][0];
    }

    if (readLinkEcc) {
      if (byteMode) {
        RD_AC_RL = RD_AC_RL_SETB;
        RD_AC_TWCKENL_RD = RD_AC_TWCKENL_RD_ECC_B;
        RD_AC_RL_DBI = RD_AC_RL_SETB;
      } else {
        RD_AC_RL = RD_AC_RL_SETA;
        RD_AC_TWCKENL_RD = RD_AC_TWCKENL_RD_ECC_A;
        RD_AC_RL_DBI = RD_AC_RL_SETA;
      }
    } else {
      switch (readEither + byteMode) {
      case 2:
        RD_AC_RL = RD_AC_RL_SETC;
        RD_AC_TWCKENL_RD = RD_AC_TWCKENL_RD_SETC;
        RD_AC_RL_DBI = RD_AC_RL_SETC;
        break;
      case 1:
        RD_AC_RL = RD_AC_RL_SETB;
        RD_AC_TWCKENL_RD = RD_AC_TWCKENL_RD_SETB;
        if (byteMode == 1) {
          RD_AC_RL_DBI = RD_AC_RL_SETC;
        } else {
          RD_AC_RL_DBI = RD_AC_RL_SETB;
        }
        break;
      case 0:
      default:
        RD_AC_RL = RD_AC_RL_SETA;
        RD_AC_TWCKENL_RD = RD_AC_TWCKENL_RD_SETA;
        RD_AC_RL_DBI = RD_AC_RL_SETB;
        break;
      }
    }

    // Write Latency Set
    if (wls) {
      WR_AC_WL = WR_AC_WL_SETB;
      WR_AC_TWCKENL_WR = WR_AC_TWCKENL_WR_SETB;
    } else {
      WR_AC_WL = WR_AC_WL_SETA;
      WR_AC_TWCKENL_WR = WR_AC_TWCKENL_WR_SETA;
    }

    // BL/n_max
    switch (bankOrg) {
    case 2: // 16B Mode
      BLnmax = (ratio == 2) ? 4 : 2;
      break;
    case 1: // 8B Mode
    case 0: // BG Mode
    default:
      BLnmax = (ratio == 2) ? 8 : 4;
      break;
    }

    switch ((mb1D[pstate].MR10_A0 >> 2) & 0x3u) {
    case 2: // 6.5*tWCK
      tWCKPST = 6 + 1;
      break;
    case 1: // 4.5*tWCK
      tWCKPST = 4 + 1;
      break;
    case 0: // 2.5*tWCK (default)
    default:
      tWCKPST = 2 + 1;
      break;
    }

    uint16_t lowFreqBuffer = 0;

    // Read parameters
    for (int i = 0; i < numSpeeds; ++i) {
      if ((freq) > WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_FREQ_LOWER] && (freq) <= WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_FREQ_UPPER]) {
        if (freq <= 133 && ratio == 4) {
          lowFreqBuffer = 1;
        } else if (freq <= 267 && ratio == 2) {
          lowFreqBuffer = 2;
        } else if (freq <= 688 && freq >= 267 && ratio == 2) {
          lowFreqBuffer = 1;
        } else {
          lowFreqBuffer = 0;
        }

        readLatency = WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_RL] + lowFreqBuffer;
        readLatencyDbi = WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_RL_DBI] + lowFreqBuffer;
        tWCKENL_RD = WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_TWCKENL_RD] + lowFreqBuffer;
        tWCKPRE_static = WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_TWCKEPRE_STATIC];
        tWCKPRE_Toggle_RD = WCK2CK_Sync_RD_lookup[i * 11 + RD_AC_TWCKEPRE_TOGGLE_RD];
        break;
      }
    }

    // Write and Fast Toggle parameters
    ratioIndex = ratio == 2 ? 0 : 1;
    numSpeeds = (ratioIndex != 0u) ? 15 : 6;
    for (int i = 0; i < numSpeeds; ++i) {
      if ((freq) > WCK2CK_Sync_WR_lookup[ratioIndex][i][RD_AC_FREQ_LOWER] && (freq) <= WCK2CK_Sync_WR_lookup[ratioIndex][i][RD_AC_FREQ_UPPER]) {
        writeLatency = WCK2CK_Sync_WR_lookup[ratioIndex][i][WR_AC_WL] + lowFreqBuffer;
        tWCKENL_WR = WCK2CK_Sync_WR_lookup[ratioIndex][i][WR_AC_TWCKENL_WR] + lowFreqBuffer;
        tWCKENL_FS = WCK2CK_Sync_FS_lookup[ratioIndex][i][FS_AC_TWCKENL_FS] + lowFreqBuffer;
        tWCKPRE_Toggle_WR = WCK2CK_Sync_WR_lookup[ratioIndex][i][WR_AC_TWCKEPRE_TOGGLE_WR];
        tWCKPRE_Toggle_FS = WCK2CK_Sync_WR_lookup[ratioIndex][i][WR_AC_TWCKEPRE_TOGGLE_WR];
        break;
      }
    }
	
	uint16_t NumAcInPipeEn = pRuntimeConfig->NumAcInPipeEn[pstate];
	uint16_t NumDxInPipeEn = pRuntimeConfig->NumDxInPipeEn[pstate];

    uint16_t wrSdly = (tWCKENL_WR * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t wrSwd = tWCKPRE_static * ratio;
    uint16_t wrTGdly = ((tWCKENL_WR + tWCKPRE_static) * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t wrTGwd = 1 * ratio;
    uint16_t wrFTGdly = ((tWCKENL_WR + tWCKPRE_static + 1) * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t wrFTGwd = ((tWCKPRE_Toggle_WR - 1) * ratio) + (BLnmax * ratio) + tWCKPST;

    // For PPT2, increase the WRCK Fast Toggle width by 1 to meet WFF->RFF timing
    if (pUserInputAdvanced->RetrainMode[pstate] == 4) {
      // Save PPT2 adjustments for WRCK Fast Toggle for Step I to reprogram and Training FW complete
      phyctx->wrFTGdly[pstate] = wrFTGdly;
      phyctx->wrFTGwd[pstate]  = wrFTGwd;

      // Depending on tWCKPST, increase WCK Fast Toggle width to ensure WCK toggling for WFF->RFF timing
      if (tWCKPST == 7) {
        phyctx->wrFTGwd[pstate] += 1;
        dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, PPT2 with tWCKPST=%d, adjusting ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth by 1\n", __func__, h, pstate, freq, tWCKPST);
      } else if (tWCKPST == 5) {
        phyctx->wrFTGwd[pstate] += 3;
        dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, PPT2 with tWCKPST=%d, adjusting ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth by 3\n", __func__, h, pstate, freq, tWCKPST);
      } else if (tWCKPST == 3) {
        phyctx->wrFTGwd[pstate] += 5;
        dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, PPT2 with tWCKPST=%d, adjusting ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth by 5\n", __func__, h, pstate, freq, tWCKPST);
      } else {
        dwc_ddrphy_phyinit_assert(0, "[%s] %s PPT2 WCK WR Fast Toggle adjust, invalid tWCKPST=%d\n", __func__, h, tWCKPST);
      }

      // If x8 mode, increase WRCK Fast Toggle width to ensure WCK toggling for WFF->RFF timing
      if (byteMode) {
        dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, PPT2 with byteMode=%d, adjusting ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth by 4\n", __func__, h, pstate, freq, byteMode);
        phyctx->wrFTGwd[pstate] += 8;
      }
    }

    uint16_t rdSdly = (tWCKENL_RD * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t rdSwd = tWCKPRE_static * ratio;
    uint16_t rdTGdly = ((tWCKENL_RD + tWCKPRE_static) * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t rdTGwd = 1 * ratio;
    uint16_t rdFTGdly = ((tWCKENL_RD + tWCKPRE_static + 1) * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t rdFTGwd = ((tWCKPRE_Toggle_RD - 1) * ratio) + (BLnmax * ratio) + tWCKPST;

    uint16_t fsSdly = (tWCKENL_FS * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t fsSwd = tWCKPRE_static * ratio;
    uint16_t fsTGdly = ((tWCKENL_FS + tWCKPRE_static) * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t fsTGwd = 1 * ratio;
    uint16_t fsFTGdly = ((tWCKENL_FS + tWCKPRE_static + 1) * ratio) - 4 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t fsFTGwd = ((tWCKPRE_Toggle_FS - 1) * ratio) + BLdiv2 + tWCKPST;

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckWriteStaticLoPulse::ACSMWckWriteStaticLoWidth to 0x%x, ACSMWckWriteStaticLoPulse::ACSMWckWriteStaticLoDelay to 0x%x\n", __func__, h, pstate, freq, wrSwd, wrSdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckWriteStaticHiPulse::ACSMWckWriteStaticHiWidth to 0x%x, ACSMWckWriteStaticHiPulse::ACSMWckWriteStaticHiDelay to 0x%x\n", __func__, h, pstate, freq, wrSwd, wrSdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckWriteTogglePulse::ACSMWckWriteToggleWidth to 0x%x, ACSMWckWriteTogglePulse::ACSMWckWriteToggleDelay to 0x%x\n", __func__, h, pstate, freq, wrTGwd, wrTGdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth to 0x%x, ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleDelay to 0x%x\n", __func__, h, pstate, freq, wrFTGwd, wrFTGdly);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckWriteStaticLoPulse_ADDR), (wrSwd << csr_ACSMWckWriteStaticLoWidth_LSB) | (wrSdly << csr_ACSMWckWriteStaticLoDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckWriteStaticHiPulse_ADDR), (wrSwd << csr_ACSMWckWriteStaticHiWidth_LSB) | (wrSdly << csr_ACSMWckWriteStaticHiDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckWriteTogglePulse_ADDR), (wrTGwd << csr_ACSMWckWriteToggleWidth_LSB) | (wrTGdly << csr_ACSMWckWriteToggleDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckWriteFastTogglePulse_ADDR), (wrFTGwd << csr_ACSMWckWriteFastToggleWidth_LSB) | (wrFTGdly << csr_ACSMWckWriteFastToggleDelay_LSB));

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckReadStaticLoPulse::ACSMWckReadStaticLoWidth to 0x%x, ACSMWckReadStaticLoPulse::ACSMWckReadStaticLoDelay to 0x%x\n", __func__, h, pstate, freq, rdSwd, rdSdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckReadStaticHiPulse::ACSMWckReadStaticHiWidth to 0x%x, ACSMWckReadStaticHiPulse::ACSMWckReadStaticHiDelay to 0x%x\n", __func__, h, pstate, freq, rdSwd, rdSdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckReadTogglePulse::ACSMWckReadToggleWidth to 0x%x, ACSMWckReadTogglePulse::ACSMWckReadToggleDelay to 0x%x\n", __func__, h, pstate, freq, rdTGwd, rdTGdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleWidth to 0x%x, ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleDelay to 0x%x\n", __func__, h, pstate, freq, rdFTGwd, rdFTGdly);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckReadStaticLoPulse_ADDR), (rdSwd << csr_ACSMWckReadStaticLoWidth_LSB) | (rdSdly << csr_ACSMWckReadStaticLoDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckReadStaticHiPulse_ADDR), (rdSwd << csr_ACSMWckReadStaticHiWidth_LSB) | (rdSdly << csr_ACSMWckReadStaticHiDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckReadTogglePulse_ADDR), (rdTGwd << csr_ACSMWckReadToggleWidth_LSB) | (rdTGdly << csr_ACSMWckReadToggleDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckReadFastTogglePulse_ADDR), (rdFTGwd << csr_ACSMWckReadFastToggleWidth_LSB) | (rdFTGdly << csr_ACSMWckReadFastToggleDelay_LSB));

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckFreqStaticLoPulse::ACSMWckFreqStaticLoWidth to 0x%x, ACSMWckFreqStaticLoPulse::ACSMWckFreqStaticLoDelay to 0x%x\n", __func__, h, pstate, freq, fsSwd, fsSdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckFreqStaticHiPulse::ACSMWckFreqStaticHiWidth to 0x%x, ACSMWckFreqStaticHiPulse::ACSMWckFreqStaticHiDelay to 0x%x\n", __func__, h, pstate, freq, fsSwd, fsSdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckFreqTogglePulse::ACSMWckFreqToggleWidth to 0x%x, ACSMWckFreqTogglePulse::ACSMWckFreqToggleDelay to 0x%x\n", __func__, h, pstate, freq, fsTGwd, fsTGdly);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleWidth to 0x%x, ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleDelay to 0x%x\n", __func__, h, pstate, freq, fsFTGwd, fsFTGdly);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckFreqSwStaticLoPulse_ADDR), (fsSwd << csr_ACSMWckFreqSwStaticLoWidth_LSB) | (fsSdly << csr_ACSMWckFreqSwStaticLoDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckFreqSwStaticHiPulse_ADDR), (fsSwd << csr_ACSMWckFreqSwStaticHiWidth_LSB) | (fsSdly << csr_ACSMWckFreqSwStaticHiDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckFreqSwTogglePulse_ADDR), (fsTGwd << csr_ACSMWckFreqSwToggleWidth_LSB) | (fsTGdly << csr_ACSMWckFreqSwToggleDelay_LSB));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckFreqSwFastTogglePulse_ADDR), (fsFTGwd << csr_ACSMWckFreqSwFastToggleWidth_LSB) | (fsFTGdly << csr_ACSMWckFreqSwFastToggleDelay_LSB));

    /**
     * - Program ACSMRxEnPulse, ACSMRxValPulse, ACSMRdcsPulse, ACSMTxEnPulse, ACSMWrcsPulse:
     *   - Description: Program timing parameters for RxEn pulse, RxVal pulse, TxEn pulse, Wrcs pulse, Rdcs pulse
     *   - Dependencies:
     *     - user_input_basic.DramType
     *     - user_input_basic.Frequency
     *     - user_input_advanced.DxInPipeEn
     *     - user_input_advanced.AcInPipeEn
     */
    int WDQSExt = 0;

    if (DataRateMbps > 3200) {
      rxPulseDly = (ratio * readLatency) - 13 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
      rxPulseDlyDbi = (ratio * readLatencyDbi) - 13 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
      rxPulseWd = BLdiv2;

    } else {
      rxPulseDly = (ratio * readLatency) - 5 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
      rxPulseDlyDbi = (ratio * readLatencyDbi) - 5 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
      rxPulseWd = BLdiv2;
    }
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMRxEnPulse::ACSMRxEnDelay to 0x%x, ACSMRxEnPulse::ACSMRxEnWidth to 0x%x\n", __func__, h, pstate, freq, rxPulseDly, rxPulseWd);
    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMRxValPulse::ACSMRxValDelay to 0x%x, ACSMRxValPulse::ACSMRxValWidth to 0x%x\n", __func__, h, pstate, freq, rxPulseDly, rxPulseWd);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMRxEnPulse_ADDR), ((rxPulseDly << csr_ACSMRxEnDelay_LSB) & csr_ACSMRxEnDelay_MASK) | ((rxPulseWd << csr_ACSMRxEnWidth_LSB) & csr_ACSMRxEnWidth_MASK));
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMRxValPulse_ADDR), ((rxPulseDly << csr_ACSMRxValDelay_LSB) & csr_ACSMRxValDelay_MASK) | ((rxPulseWd << csr_ACSMRxValWidth_LSB) & csr_ACSMRxValWidth_MASK));

    if (WDQSExt) {
      rxPulseDly -= 2;
      rxPulseDlyDbi -=2;
      rxPulseWd += 2;
    }

    mb1D[pstate].ALT_RL = rxPulseDlyDbi;
    mb1D[pstate].MAIN_RL = rxPulseDly;

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMRdcsPulse::ACSMRdcsDelay to 0x%x, ACSMRdcsPulse::ACSMRdcsWidth to 0x%x\n",  __func__, h, pstate, freq, rxPulseDly, rxPulseWd);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMRdcsPulse_ADDR), ((rxPulseDly << csr_ACSMRdcsDelay_LSB) & csr_ACSMRdcsDelay_MASK) | ((rxPulseWd << csr_ACSMRdcsWidth_LSB) & csr_ACSMRdcsWidth_MASK));

    uint16_t txPulseDly = (ratio * writeLatency) - 5 + (NumAcInPipeEn - NumDxInPipeEn) * ratio/2;
    uint16_t txPulseWd = BLdiv2;

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMTxEnPulse::ACSMTxEnDelay to 0x%x, ACSMTxEnPulse::ACSMTxEnWidth to 0x%x\n",  __func__, h, pstate, freq, txPulseDly, txPulseWd);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMTxEnPulse_ADDR), ((txPulseDly << csr_ACSMTxEnDelay_LSB) & csr_ACSMTxEnDelay_MASK) | ((txPulseWd << csr_ACSMTxEnWidth_LSB) & csr_ACSMTxEnWidth_MASK));

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming ACSMWrcsPulse::ACSMWrcsDelay to 0x%x, ACSMWrcsPulse::ACSMWrcsWidth to 0x%x\n",  __func__, h, pstate, freq, txPulseDly, txPulseWd);
    dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWrcsPulse_ADDR), ((txPulseDly << csr_ACSMWrcsDelay_LSB) & csr_ACSMWrcsDelay_MASK) | ((txPulseWd << csr_ACSMWrcsWidth_LSB) & csr_ACSMWrcsWidth_MASK));

    /**
     * - Program AcPipeEn:
     *   - Description: Enable DfiClk pipeline on the command address
     *   - Dependencies:
     *     - user_input_basic.Frequency
     *     - user_input_basic.DfiFreqRatio
     *     - user_input_basic.NumCh
     */
	uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
	uint32_t tck_ps = pRuntimeConfig->tck_ps[pstate];

    uint16_t AcPipeEn = ((pUserInputBasic->DfiFreqRatio[pstate] == 1) ? ((freq <= 267) ? 2 : ((freq <= 688) ? 1 : 0)) : ((freq <= 133) ? 1 : 0));
    for (int achn = 0; achn < NumAchnActive; achn++) {
      uint32_t c_addr = achn * c1;
      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, Memclk=%dMHz, Programming AcPipeEn AC%d to %d. DFI ratio is %d\n",  __func__, h, pstate, freq, achn, AcPipeEn, pUserInputBasic->DfiFreqRatio[pstate]);
      dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | csr_AcPipeEn_ADDR), AcPipeEn);
    }

    // If PPT2 enabled, calculate the ACSM SRAM {WFF,RFF}->CAS(WS_off) delay adjustments based on current PState
    if (pUserInputAdvanced->RetrainMode[pstate] == 4) {

      // WR/RD-FIFO/RDC command delay optimization (updates for JEDEC-5B, table 357):
      //  1. WFF command delay = WL + BL/n_max + RD(tWCKPST/tCK) + 1
      //  2. RFF command delay = RL + BL/n_max + RD(tWCKPST/tCK) + 1
      //  3. RDC command delay is same as RFF command delay
      uint32_t ppt2Wff2CasWsoffDly = 0x0;
      uint32_t ppt2Rff2CasWsoffDly = 0x0;
      uint32_t tHWTMRL = 16;  // Max HWTMRL @6400Mbps
      uint32_t tHWTMRL_freq ; // Scaled HWTMRL for lower frequency
      uint32_t twck_ps = (pUserInputBasic->DfiFreqRatio[pstate]==1) ? tck_ps/2 : tck_ps/4;
      uint32_t tWCKPST_ps = (tWCKPST * twck_ps);
      uint32_t tWCKPST_cycle;

      // Max tCK=938ps (1066MHz/8533Mbps)
      tHWTMRL_freq = (((tHWTMRL*938) % tck_ps) != 0u) ? ((tHWTMRL*938)/tck_ps + 1) : ((tHWTMRL*938)/tck_ps);

      // Calculate RD(tWCKPST/tCK) and round down to nearest integer value (integer divide will round down)
      tWCKPST_cycle = (tWCKPST_ps/tck_ps);

      ppt2Wff2CasWsoffDly = (uint32_t) (writeLatency + BLnmax + tWCKPST_cycle + 1);

      ppt2Rff2CasWsoffDly = (uint32_t) (readLatency + BLnmax + tWCKPST_cycle + 1 + tHWTMRL_freq);

      // Define ACSM delay, divide by 2 (even/odd ACSM execution) and subtract 1 (ACSM rptcnt[7:0] is N+1)
      uint32_t wffDly = ((ppt2Wff2CasWsoffDly)/2)-1;
      uint32_t rffDly = ((ppt2Rff2CasWsoffDly)/2)-1;

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, twck_ps=%d, WL (write latency)=%d, BLnmax=%d tWCKPST=%d, tWCKPST_cycle=%d,                  ppt2Wff2CasWsoffDly=%d, AcsmMrkrCnt=%d\n",
                               __func__, h, pstate, DataRateMbps, freq, tck_ps, twck_ps, writeLatency, BLnmax, tWCKPST, tWCKPST_cycle, ppt2Wff2CasWsoffDly, wffDly);
      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, twck_ps=%d, RL (read latency)=%d,  BLnmax=%d tWCKPST=%d, tWCKPST_cycle=%d, tHWTMRL_freq=%d, ppt2Rff2CasWsoffDly=%d, AcsmMrkrCnt=%d\n",
                               __func__, h, pstate, DataRateMbps, freq, tck_ps, twck_ps, readLatency, BLnmax, tWCKPST, tWCKPST_cycle, tHWTMRL_freq, ppt2Rff2CasWsoffDly, rffDly);

      // WFF->RFF command delay optimization (JEDEC-6B, table 210, using Min Note 4 equations)
      //  1. NT-ODT Disabled: Max(3nCK, WL+BL/n_max-RL + Max[RU(10ns/tCK),4nCK])
      //  2. NT-ODT Enabled : Max(3nCK, WL+BL/n_max-RL + RU[tODToff(max)/tCK)] + Max[RU(10ns/tCK),4nCK])
      //  Note 1: tODToff(max)=3.5ns (see table 258)
      //  Note 2: RU is round up
      //  Note 3: These equation variables must be int type because (WL+BL/n_max-RL) can be negative, cast to final uint32_t wff2RffDlyMin variable at the end
      int ppt2Wff2RffDly = 0x0;
      int tenNs_ps = (10*1000);
      int ntOdtEn = 0;
      int mr11NtOdt = ((mb1D[pstate].MR11_A0 & 0x08u) >> 3);
      int mr41NtDqOdt = ((mb1D[pstate].MR41_A0 & 0xe0u) >> 5);
      int tODToffMax_ps = 3500;
      int ppt2Wff2RffWL = (int) writeLatency;
      int ppt2Wff2RffRL = (int) readLatency;
      int ppt2Wff2RffBLnmax = (int) BLnmax;
      int ppt2Wff2RffTwckpstCycle = (int) tWCKPST_cycle;
      int ppt2Wff2RffLatencies = 0x0;
      int max10ns4nCK = 0x0;
      int tODToffMaxRU = 0x0;

      // Calculate latency term (WL + BL/n_max - RL)
      ppt2Wff2RffLatencies = (ppt2Wff2RffWL + ppt2Wff2RffBLnmax - ppt2Wff2RffRL);

      // Calculate Max[RU(10ns/tCK),4nCK]
      max10ns4nCK = ((tenNs_ps % tck_ps) != 0u) ? ((tenNs_ps/tck_ps) + 1) : (tenNs_ps/tck_ps);
      max10ns4nCK = (max10ns4nCK > 4) ? max10ns4nCK : 4;

      // Caclulate RU[tODToff(max)/tCK)
      tODToffMaxRU = (tODToffMax_ps % tck_ps != 0u) ? ((tODToffMax_ps/tck_ps) + 1) : (tODToffMax_ps/tck_ps);

      // NT-ODT is enabled if:
      //  - MR11[NT-ODT]==1 and MR41[NT-DQ-ODT]!=0
      if ((mr11NtOdt==1) && (mr41NtDqOdt!=0)) {
        ntOdtEn = 1;
      } else {
        ntOdtEn = 0;
      }

      // Depending on NT-ODT enable/disable, calculate either:
      //  1. NT-ODT Disabled: Max(3nCK, (ppt2Wff2RffLatency + max10ns4nCK))
      //  2. NT-ODT Enabled : Max(3nCK, (ppt2Wff2RffLatency + tODToffMaxRU + max10ns4nCK))
      if (ntOdtEn == 0) {
        // NT-ODT Disabled
        ppt2Wff2RffDly = ((ppt2Wff2RffLatencies+max10ns4nCK) > 3) ? (ppt2Wff2RffLatencies+max10ns4nCK) : (3);
      } else {
        // NT-ODT Enabled
        ppt2Wff2RffDly = ((ppt2Wff2RffLatencies+max10ns4nCK+tODToffMaxRU) > 3) ? (ppt2Wff2RffLatencies+max10ns4nCK+tODToffMaxRU) : (3);
      }

      // Create uint32_t version of ppt2Wff2RffDly to assign to phyctx->AcsmMrkrCnt[] array
      uint32_t wff2RffDlyMin = (uint32_t) ppt2Wff2RffDly;
      uint32_t wff2RffDlyMax = (uint32_t) (ppt2Wff2RffWL + ppt2Wff2RffBLnmax + ppt2Wff2RffTwckpstCycle);

      uint8_t cmntRlSet;
      if (readLinkEcc) {
        cmntRlSet = (byteMode==1) ? 1 : 0; 
      } else {
        switch (readEither + byteMode) {
          case 2:
            cmntRlSet  = 2;
            break;
          case 1:
            cmntRlSet  = 1;
            break;
          default:
            cmntRlSet = 0;
            break;
        }
      }
      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, Set %s, WL=%d, BLnmax=%d, RL=%d, RL Set %d, ReadLinkECC %s, DVFSC %s,Enhanced DVFSC %s, ntOdtEn=%s\n",
                               __func__, h, pstate, DataRateMbps, freq, (wls==0?"A":"B"), writeLatency, BLnmax, readLatency, cmntRlSet, (readLinkEcc==1?"Enabled":"Disabled"), (dvfsc==1?"Enabled":"Disabled"),(dvfsc==2?"Enabled":"Disabled"), (ntOdtEn==1?"Enabled":"Disabled"));

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, WL=%d, BLnmax=%d, RL=%d, max10ns4nCK=%d, ntOdtEn=%d (MR11[NT-ODT]=%d, MR41[NT-DQ-ODT]=%d), tODToffMaxRU=%d, ppt2Wff2RffDly(min)=%d, ppt2Wff2RffDly(max)=%d\n",
                               __func__, h, pstate, DataRateMbps, freq, tck_ps, writeLatency, BLnmax, readLatency, max10ns4nCK, ntOdtEn, mr11NtOdt, mr41NtDqOdt, tODToffMaxRU, wff2RffDlyMin, wff2RffDlyMax);

      // Save RFF cmd-to-cmd delay to GPR20 for PIE PPT2 code to use, RFF delay is 2 pairs of NOPs (4 cmds per loop)
      uint32_t acsmRptCntWff2Rff = ((wff2RffDlyMin/4) - (((wff2RffDlyMin%4u) != 0u) ? 0 : 1));
      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, acsmRptCntWff2Rff=%d\n", __func__, h, pstate, DataRateMbps, freq, tck_ps, acsmRptCntWff2Rff);
      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_pst=%d, Programming Seq0BGPR20 to acsmRptCntWff2Rff=%d\n", __func__, h, pstate, DataRateMbps, freq, tck_ps, acsmRptCntWff2Rff);
      dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR20_ADDR), acsmRptCntWff2Rff);

      // Calculate the current PState's tMRD (tMRD=max(14ns,5nCK))
      uint32_t tMRDPpt2 = (5*tck_ps > 14000) ? (5*tck_ps) : 14000;
      uint32_t tMRDPpt2_ck = ((tMRDPpt2 % tck_ps) != 0u) ? ((tMRDPpt2/tck_ps) + 1) : (tMRDPpt2/tck_ps);
      uint32_t mrwDly = 0x0;

      // If tMRD is odd number of clocks, round up since ACSM does 2 NOPs per delay
      tMRDPpt2_ck = ((tMRDPpt2_ck % 2) != 0u) ? (tMRDPpt2_ck + 1) : tMRDPpt2_ck;
      mrwDly = ((tMRDPpt2_ck)/2)-1;

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, tMRDPpt2=%d, tMRDPpt2_ck=%d AcsmMrkrCnt=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, tMRDPpt2, tMRDPpt2_ck, mrwDly);

      // Calculate the current PState's CAS(ws_off) delay, Max(tWCKPST, tWCKSTOP)
      uint32_t ppt2CasOffDly = 0x0;
      uint32_t casDly = 0x0;
      uint32_t tWCKSTOP = 0x0;

      // Calculate tWCKSTOP, Max(2nCK, 6ns)
      tWCKSTOP = (2*tck_ps > 6000) ? (2*tck_ps) : 6000;

      // Calculate Max(tWCKPST, tWCKSTOP), then convert to tCK's
      ppt2CasOffDly = (tWCKPST_ps > tWCKSTOP) ? tWCKPST_ps : tWCKSTOP;
      ppt2CasOffDly = ((ppt2CasOffDly % tck_ps) != 0u) ? ((ppt2CasOffDly/tck_ps)+1) : (ppt2CasOffDly/tck_ps);

      // In the TxDq2 ACSM sequence, there's a NOP (2 tCK's) after the CAS(ws_off) so reduce the ppt2CasOffDly by 2 tCK's only if current delay > 3 (else casDly will go negative creating huge inner loop delay)
      ppt2CasOffDly = (ppt2CasOffDly > 3 ) ? (ppt2CasOffDly-2) : ppt2CasOffDly;

      // Convert ppt2CasOffDly to ACSM inner loop repeat count
      casDly = (ppt2CasOffDly/2)-1;

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, tWCKPST_ps=%d, tWCKSTOP=%d ppt2CasOffDly=%d, casDly=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, tWCKPST_ps, tWCKSTOP, ppt2CasOffDly, casDly);


      // Program the ACSM cmd-to-cmd delays in the proper set of upper/lower data rate ACSM markers
      if (DataRateMbps > 4267) {
        // Upper data rates 8533Mbps-4800Mbps

        // Use PIE PPT2 start address sequence 0 for upper/middle data rates
        phyctx->Ppt2PieSeqNum[pstate] = 0;

        // Program/log ratio speicific ACSM SRAM addresses
        if (ratio == 4) {
          // 1:4 ACSM marker adjustments

          // WCK:CK 4:1 - only update phyctx->AcsmMrkrCnt[i] if the currently calculated ACSM delays are larger than what is already saved (higher data rate means larger delays)
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF];  // RxClk/TxDq1 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF];  // RxClk/TxDq1 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF];  // RxClk/TxDq1 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF];  // RxClk/TxDq1 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG0_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG0_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG0_RDC];         // RxEn tg0 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG1_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG1_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_RXEN_TG1_RDC];         // RxEn tg1 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW];        // TxDq2 tg0 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF];        // TxDq2 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF];        // TxDq2 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS];        // TxDq2 tg0 CAS
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW];        // TxDq2 tg1 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF];        // TxDq2 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF];        // TxDq2 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS];        // TxDq2 tg1 CAS

          // Log the PPT2 ACSM SRAM rptcnt[7:0] overrides
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[34]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[34]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[35]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[35]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[36]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[36]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[37]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[37]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, Rxen        tg0 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[38]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[38]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, Rxen        tg1 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[39]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[39]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 MRW->CAS(WS_wr)  phyctx->AcsmMrkrCnt[40]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[40]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[41]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[41]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[42]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[42]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[43]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[43]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 MRW->CAS(WS_wr)  phyctx->AcsmMrkrCnt[44]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[44]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[45]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[45]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[46]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[46]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[47]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[47]);

        } else {
          // 1:2 ACSM marker adjustments

          // WCK:CK 2:1 - only update phyctx->AcsmMrkrCnt[i] if the currently calculated ACSM delays are larger than what is already saved (higher data rate means larger delays)
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF];  // RxClk/TxDq1 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF];  // RxClk/TxDq1 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF];  // RxClk/TxDq1 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF];  // RxClk/TxDq1 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG0_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG0_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG0_RDC];         // RxEn tg0 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG1_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG1_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_RXEN_TG1_RDC];         // RxEn tg1 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW];        // TxDq2 tg0 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF];        // TxDq2 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF];        // TxDq2 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS];        // TxDq2 tg0 CAS
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW];        // TxDq2 tg1 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF];        // TxDq2 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF];        // TxDq2 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_UDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS];        // TxDq2 tg1 CAS

          // Log the PPT2 ACSM SRAM rptcnt[7:0] overrides
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[0]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[0]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[1]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[1]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[2]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[2]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[3]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[3]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, Rxen        tg0 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[4]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[4]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, Rxen        tg1 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[5]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[5]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 MRW->CAS(WS_ws)  phyctx->AcsmMrkrCnt[6]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[6]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[7]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[7]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[8]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[8]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[9]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[9]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 MRW->CAS(WS_wr)  phyctx->AcsmMrkrCnt[10]=%d\n", __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[10]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[11]=%d\n", __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[11]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[12]=%d\n", __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[12]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Upper Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[13]=%d\n", __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[13]);
        }
      } else if ((DataRateMbps > 2750) && (DataRateMbps <= 4267)) {
        // Middle data rates 4267Mbps-3200Mbps

        // Use PIE PPT2 start address sequence 0 for upper/middle data rates
        phyctx->Ppt2PieSeqNum[pstate] = 0;

        // Program/log ratio speicific ACSM SRAM addresses
        if (ratio == 4) {
          // 1:4 ACSM marker adjustments

          // WCK:CK 4:1 - only update phyctx->AcsmMrkrCnt[i] if the currently calculated ACSM delays are larger than what is already saved (higher data rate means larger delays)
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF];  // RxClk/TxDq1 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF];  // RxClk/TxDq1 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF];  // RxClk/TxDq1 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF];  // RxClk/TxDq1 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG0_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG0_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG0_RDC];         // RxEn tg0 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG1_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG1_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_RXEN_TG1_RDC];         // RxEn tg1 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_MRW];        // TxDq2 tg0 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_WFF];        // TxDq2 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_RFF];        // TxDq2 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG0_CAS];        // TxDq2 tg0 CAS
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_MRW];        // TxDq2 tg1 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_WFF];        // TxDq2 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_RFF];        // TxDq2 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_4to1_TXDQ2_TG1_CAS];        // TxDq2 tg1 RFF

          // Log the PPT2 ACSM SRAM rptcnt[7:0] overrides
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[48]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[48]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[49]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[49]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[50]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[50]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[51]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[51]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, Rxen        tg0 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[52]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[52]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, Rxen        tg1 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[53]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[53]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 MRW->CAS(WS_wr)  phyctx->AcsmMrkrCnt[54]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[54]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[55]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[55]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[56]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[56]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg0 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[57]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[57]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 MRW->CAS(WS_wr)  phyctx->AcsmMrkrCnt[58]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[58]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[59]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[59]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[60]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[60]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, TxDq2       tg1 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[61]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[61]);

        } else {
          // 1:2 ACSM marker adjustments

          // WCK:CK 2:1 - only update phyctx->AcsmMrkrCnt[i] if the currently calculated ACSM delays are larger than what is already saved (higher data rate means larger delays)
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF];  // RxClk/TxDq1 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF];  // RxClk/TxDq1 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF];  // RxClk/TxDq1 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF];  // RxClk/TxDq1 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG0_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG0_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG0_RDC];         // RxEn tg0 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG1_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG1_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_RXEN_TG1_RDC];         // RxEn tg1 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_MRW];        // TxDq2 tg0 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_WFF];        // TxDq2 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_RFF];        // TxDq2 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG0_CAS];        // TxDq2 tg0 CAS
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW]       = (mrwDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW])       ? mrwDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_MRW];        // TxDq2 tg1 MRW
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF]       = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF])       ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_WFF];        // TxDq2 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF]       = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF])       ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_RFF];        // TxDq2 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS]       = (casDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS])       ? casDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_MDR_ACSM_MRKR_2to1_TXDQ2_TG1_CAS];        // TxDq2 tg1 CAS

          // Log the PPT2 ACSM SRAM rptcnt[7:0] overrides
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[14]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[14]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[15]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[15]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[16]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[16]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[17]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[17]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, Rxen        tg0 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[18]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[18]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, Rxen        tg1 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[19]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[19]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 MRW->CAS(WS_wr)  phyctx->AcsmMrkrCnt[20]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[20]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[21]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[21]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[22]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[22]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg0 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[23]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[23]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 MWR->CAS(WS_wr)  phyctx->AcsmMrkrCnt[24]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[24]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[25]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[25]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[26]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[26]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Middle Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, TxDq2       tg1 CAS(ws_off)->MRW phyctx->AcsmMrkrCnt[27]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[27]);
        }
      } else {
        // Lower data rates 2750Mbps-1600Mbps

        // Use PIE PPT2 start address sequence 1 for lower data rates
        phyctx->Ppt2PieSeqNum[pstate] = 1;

        // Program/log ratio speicific ACSM SRAM addresses
        if (ratio == 4) {
          // 1:4 ACSM marker adjustments

          // WCK:CK 4:1 - only update phyctx->AcsmMrkrCnt[i] if the currently calculated ACSM delays are larger than what is already saved (higher data rate means larger delays)
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_WFF];  // RxClk/TxDq1 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG0_RFF];  // RxClk/TxDq1 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_WFF];  // RxClk/TxDq1 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXCLK_TXDQ1_TG1_RFF];  // RxClk/TxDq1 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG0_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG0_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG0_RDC];         // RxEn tg0 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG1_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG1_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_4to1_RXEN_TG1_RDC];         // RxEn tg1 RDC

          // Log the PPT2 ACSM SRAM rptcnt[7:0] overrides
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[62]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[62]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[63]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[63]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[64]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[64]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, RxClk/TxDq1 tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[65]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[65]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, Rxen        tg0 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[66]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[66]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 4:1, Rxen        tg1 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[67]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[67]);

        } else {
          // 1:2 ACSM marker adjustments

          // WCK:CK 2:1 - only update phyctx->AcsmMrkrCnt[i] if the currently calculated ACSM delays are larger than what is already saved (higher data rate means larger delays)
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_WFF];  // RxClk/TxDq1 tg0 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG0_RFF];  // RxClk/TxDq1 tg0 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF] = (wffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF]) ? wffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_WFF];  // RxClk/TxDq1 tg1 WFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF] = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF]) ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXCLK_TXDQ1_TG1_RFF];  // RxClk/TxDq1 tg1 RFF
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG0_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG0_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG0_RDC];         // RxEn tg0 RDC
          phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG1_RDC]        = (rffDly > phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG1_RDC])        ? rffDly : phyctx->AcsmMrkrCnt[DWC_DDRPHY_PHYINIT_LDR_ACSM_MRKR_2to1_RXEN_TG1_RDC];         // RxEn tg1 RDC

          // Log the PPT2 ACSM SRAM rptcnt[7:0] overrides
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg0 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[28]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[28]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg0 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[29]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[29]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg1 WFF->CAS(WS_off) phyctx->AcsmMrkrCnt[30]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[30]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, RxClk/TxDq1 tg1 RFF->CAS(WS_off) phyctx->AcsmMrkrCnt[31]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[31]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, Rxen        tg0 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[32]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[32]);
          dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d, DataRateMbps=%d, Memclk=%d MHz, tck_ps=%d, PPT2 Lower Data Rate ACSM SRAM instruction rptcnt[7:0] override WCK:CK 2:1, Rxen        tg1 RDC->CAS(WS_off) phyctx->AcsmMrkrCnt[33]=%d\n",  __func__, h, pstate, DataRateMbps, freq, tck_ps, phyctx->AcsmMrkrCnt[33]);
        }
      }
      // <-- WR/RD-FIFO command delay optimization by M.Iijima
    }



  dwc_ddrphy_phyinit_cmnt("End of %s(), PState=%d\n", __func__, pstate);

} // dwc_ddrphy_phyinit_ACSM_delay



/** \brief Program the PLL settings according to the selected mode setting
 *
 * This function programs PLL control registers PllCtrl5 and PllCtrl6.
 *
 * \param phyctx       Data structure to hold user-defined parameters
 * \param mode         Selected configuration mode, 0 for step C, 1 for step I
 * \param print_header String used for logging
 *
 * \return void
 */
void dwc_ddrphy_phyinit_programPLL(phyinit_config_t *phyctx, int mode, const char* print_header)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

  uint8_t pstate = pRuntimeConfig->curPState;
  uint32_t p_addr = (uint32_t) pstate << 20;
  uint16_t freq = pUserInputBasic->Frequency[pstate];
  const char* h = print_header;

  


  // PLL normal operation modes, with x2 or x4 ratio settings
  // Note: lookup frequency table(s) below use PllRefClk frequency x 4


  // PLL reference input clock freq: 89.4, 106.0, 130.25, 156.25, 178.8, 212.0, 260.5, 312.5, 357.5, 424.0, 521.25, 625.0, 675.0, 810.0, 1067.0
  uint16_t CpllInMax_normal_x4[] = { 358, 424, 521, 625, 715, 848, 1042, 1250, 1430, 1696, 2085, 2500, 2700, 3240, 4268 };
  uint16_t CpllDivSel_normal_x4[] = { 0x32, 0x32, 0x32, 0x36, 0x162, 0x162, 0x162, 0x166, 0x296, 0x296, 0x296, 0x29a, 0x29a, 0x29a, 0x29a };
  uint16_t CpllV2IMode_normal_x4[] = { 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3 };
  uint16_t CpllVCOFreq_normal_x4[] = { 0x3, 0x2, 0x1, 0x0, 0x3, 0x2, 0x1, 0x0, 0x3, 0x2, 0x1, 0x0, 0x2, 0x1, 0x0 };
  unsigned int Cfreq_list_len_normal_x4 = 15;

  // PLL reference input clock freq: 89.4, 106, 130.25, 156.25 178.8, 212.0, 260.5, 312.5, 357.5, 424.0, 521.25, 625.0, 675.0, 810.0, 1067.0
  uint16_t CpllInMax_fast_relock_x4[] = { 357, 424, 521, 625, 715, 848, 1042, 1250, 1430, 1696, 2085, 2500, 2700, 3240, 4268 };
  uint16_t CpllDivSel_fast_relock_x4[] = { 0x32, 0x32, 0x32, 0x36, 0x22, 0x22, 0x22, 0x22, 0x156, 0x156, 0x156, 0x156, 0x156, 0x156, 0x156 };
  uint16_t CpllV2IMode_fast_relock_x4[] = { 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3 };
  uint16_t CpllVCOFreq_fast_relock_x4[] = { 0x3, 0x2, 0x1, 0x0, 0x3, 0x2, 0x1, 0x0, 0x3, 0x2, 0x1, 0x0, 0x2, 0x1, 0x0 };
  unsigned int Cfreq_list_len_fast_relock_x4 = 15;

  uint16_t *pCFreqList = mode ? CpllInMax_fast_relock_x4 : CpllInMax_normal_x4;
  uint16_t *pCPllDivSel = mode ? CpllDivSel_fast_relock_x4 : CpllDivSel_normal_x4;
  uint16_t *pCPllV2IMode = mode ? CpllV2IMode_fast_relock_x4 : CpllV2IMode_normal_x4;
  uint16_t *pCPllVcoLowFreq = mode ? CpllVCOFreq_fast_relock_x4 : CpllVCOFreq_normal_x4;
  unsigned int Cfreq_list_len = mode ? Cfreq_list_len_fast_relock_x4 : Cfreq_list_len_normal_x4;

  int ClookupFreq;


    // The frequency table above uses PllRefClk frequency x 4
    ClookupFreq = freq*4;

    if ((pUserInputBasic->Lp5xMode) ? (freq > 1200) : (freq > 800)) {
      dwc_ddrphy_phyinit_assert(0, "[%s] %s specified frequency %d MHz is out of range (pUserInputBasic->Frequency, pstate=%d)\n", __func__, h, freq, pstate);
    }


  dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, ClookupFreq=%d mode=%d \n", __func__, h, pstate, freq, ClookupFreq, mode);

  // default to max frequency settings
  uint16_t CpllDivSel = pCPllDivSel[Cfreq_list_len - 1];
  uint16_t CpllV2IMode = pCPllV2IMode[Cfreq_list_len - 1];
  uint16_t CpllVcoLowFreq = pCPllVcoLowFreq[Cfreq_list_len - 1];

  for (unsigned int freq_i = 0; freq_i < Cfreq_list_len; freq_i++) {
    if (ClookupFreq <= pCFreqList[freq_i]) {
      CpllDivSel = pCPllDivSel[freq_i];
      CpllV2IMode = pCPllV2IMode[freq_i];
      CpllVcoLowFreq = pCPllVcoLowFreq[freq_i];
      break;
    }
  }

  /**
   * - Program PLL configuration CSRs CPllCtrl5
   *   - Fields:
   *     - CPllDivSel
   *     - CPllV2IMode
   *     - CPllVcoLowFreq
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   */

  uint16_t CpllCtrl5 = (CpllVcoLowFreq << csr_CPllVcoLowFreq_LSB) | (CpllV2IMode << csr_CPllV2IMode_LSB) | (CpllDivSel << csr_CPllDivSel_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllDivSel to %x.\n", __func__, h, pstate, freq, CpllDivSel);
  dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllV2IMode to %x.\n", __func__, h, pstate, freq, CpllV2IMode);
  dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllVcoLowFreq to %x.\n", __func__, h, pstate, freq, CpllVcoLowFreq);

  dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CpllCtrl5 to 0x%x.\n", __func__, h, pstate, freq, CpllCtrl5);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMMAS | csr_CPllCtrl5_ADDR), CpllCtrl5);


  if(mode == 0) {
    dwc_ddrphy_phyinit_overridePLLSettings(phyctx, mode, "[phyinit_Step_C_overridePLLSettings]");
  } else {
    dwc_ddrphy_phyinit_overridePLLSettings(phyctx, mode, "[phyinit_Step_I_overridePLLSettings]");
  }
  
  dwc_ddrphy_phyinit_cmnt("End of %s(), PState=%d\n", __func__, pstate);
}

/** \brief Program the PLL settings according to the selected mode setting
 *
 * This function programs PLL control registers PllCtrl5, PllCtrl4, PllCtrl1 and PllUPllProg0, PllUPllProg1.
 * PllUPllProg2 and PllUPllProg3
 *
 * \param phyctx       Data structure to hold user-defined parameters
 * \param mode         Selected configuration mode, 0 for step C, 1 for step I
 * \param print_header String used for logging
 *
 * \return void
 */
void dwc_ddrphy_phyinit_overridePLLSettings(phyinit_config_t *phyctx, int mode, const char* print_header)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

  uint8_t pstate = pRuntimeConfig->curPState;
  uint32_t p_addr = (uint32_t) pstate << 20;
  uint16_t freq = (uint16_t) pUserInputBasic->Frequency[pstate];
  const char* h = print_header;

  const char *pd = getenv("PLL_SETTINGS_PATH");
  FILE *fp = NULL;
  pllTableRows pllTable[DWC_DDRPHY_PHYINIT_PLL_MAX_ROWS]; 
  int row_count = 0;
  const char* fileString = NULL;
  char* pllSettings = pRuntimeConfig->pllSettings;
  dwc_ddrphy_phyinit_cmnt("Start of %s(), PState=%d\n", __func__, pstate);

  uint16_t CpllCtrl5 = 0;
  uint16_t CPllCtrl4 = 0;
  uint16_t CPllCtrl1 = 0;
  uint16_t CPllUPllProg3 = 0;
  uint16_t CPllUPllProg2 = 0;
  uint16_t CPllUPllProg1 = 0;
  uint16_t CPllUPllProg0 = 0;

  //Reading Values affecting Pll csr's from external file
  if (pd == NULL && pllSettings != NULL && strlen(pllSettings) != 0) {
     fileString = pllSettings;
     dwc_ddrphy_phyinit_cmnt("%s Command Line Path %s set\n", h, fileString);
  }
  else if (pd != NULL && pllSettings != NULL && strlen(pllSettings) == 0) {
     fileString = pd;
     dwc_ddrphy_phyinit_cmnt("%s Environment Path %s set\n", h, fileString);
  }
  else if (pd != NULL && pllSettings != NULL && strlen(pllSettings) != 0) {
     fileString = pllSettings;          
     dwc_ddrphy_phyinit_cmnt("%s Both Command Line and Environment Path available. Command Line Path %s set\n", h, fileString);
  }
  else {
    dwc_ddrphy_phyinit_cmnt("%s Neither Comand Line or Environment path set\n", h);
    return;
  }

  // coverity[misra_c_2012_rule_21_6_violation]
  // coverity[misra_c_2012_directive_4_14_violation]
  fp = fopen(fileString, "r");
  if(fp == NULL) {
    dwc_ddrphy_phyinit_cmnt("Invalid path to Pll Settings file. Can't find the file. Exiting Phyinit\n");
    dwc_ddrphy_phyinit_assert(0,"%s Invalid path to PLL Settings file: %s, Can't find the file. Exiting Phyinit\n", h, fileString);
  }

  dwc_ddrphy_phyinit_cmnt( "%s You are using an unsupported BETA feature to program PLL CSRs\n", h);

  char file_cmnt0[DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT] = "";
  char file_cmnt1[DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT] = "";
  // coverity[misra_c_2012_rule_21_6_violation]
  fgets(file_cmnt0,DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT,fp); //reading a comment at the beginning which is the version number - for now 0.2
  // coverity[misra_c_2012_rule_21_6_violation]
  fgets(file_cmnt1,DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT,fp); //reading the column titles

  if ( (!strcmp(file_cmnt0, "#Version 0.2\n")) && (!strcmp(file_cmnt1, "pllin_min,pllin_max,CPllCtrl5,CPllCtrl1,CPllCtrl4,CPllUPllProg3,CPllUPllProg2,CPllUPllProg1,CPllUPllProg0\n")) ){
    dwc_ddrphy_phyinit_cmnt("%s Using PLL Settings file : %s\n", h, file_cmnt0);
  }
  else {
    dwc_ddrphy_phyinit_cmnt("%s You are not using the correct version i.e. #Version 0.2 supported with this PHYINIT. Ignoring the file and exiting override PLL csr FW code\n", h);
    // coverity[misra_c_2012_rule_21_6_violation]
    fclose(fp);
    return;
  }

  char rows[DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT] = "";
  uint8_t col = DWC_DDRPHY_PHYINIT_PLL_MAX_COLUMN_COUNT;

  // coverity[misra_c_2012_rule_21_6_violation]
  while ( fgets(rows, DWC_DDRPHY_PHYINIT_PLL_MAX_ROW_CHARACTERS_COUNT, fp) != 0 ) {
    // coverity[misra_c_2012_rule_21_6_violation]
    col = sscanf(rows, "%40lf,%40lf,0x%x,0x%x,0x%x,0x%x,0x%x,0x%x,0x%x", &pllTable[row_count].pllIn_min, &pllTable[row_count].pllIn_max, &pllTable[row_count].PllCtrl5,
    &pllTable[row_count].PllCtrl1, &pllTable[row_count].PllCtrl4, &pllTable[row_count].PllUPllProg3, &pllTable[row_count].PllUPllProg2,
    &pllTable[row_count].PllUPllProg1, &pllTable[row_count].PllUPllProg0);
    row_count++;

    if (col != DWC_DDRPHY_PHYINIT_PLL_MAX_COLUMN_COUNT) {
      dwc_ddrphy_phyinit_assert(0,"%s Incorrect number of entries scanned within pll file\n", h);
    }
    else if (row_count >= DWC_DDRPHY_PHYINIT_PLL_MAX_ROWS) {
      dwc_ddrphy_phyinit_assert(0,"%s Limit for Maximum number of rows scanned has been reached\n", h);
    }
    else {
      //else statement placed here to remove coverity errors
    }
  }

  // coverity[misra_c_2012_rule_21_6_violation]
  fclose(fp); //Close the CSV
  
  //Parsing the PLL Table struct
  if (row_count != 0) { 
    dwc_ddrphy_phyinit_cmnt ("%s Overriding PLL CSRs for pstate = %d, from input PLL Settings file\n", h, pstate);
    int rownum = 0;
    for (rownum = 0; rownum < row_count; rownum++) {
      //PLL min/max are forced to int, so that the checks below are consistent with the other pUserInputBasic->Frequency[] checks above.
      //If we're overclocking, use the first row (highest frequency)
      if ( (((rownum == (rownum-1)) || ((float)pUserInputBasic->Frequency[pstate]) > (float)pllTable[rownum].pllIn_min)) &&
            ((rownum == 0) || ((float)pUserInputBasic->Frequency[pstate] <= (float)pllTable[rownum].pllIn_max)) ){
        CpllCtrl5         = pllTable[rownum].PllCtrl5;
        CPllCtrl1         = pllTable[rownum].PllCtrl1;
        CPllCtrl4         = pllTable[rownum].PllCtrl4;
        CPllUPllProg3     = pllTable[rownum].PllUPllProg3;
        CPllUPllProg2     = pllTable[rownum].PllUPllProg2;
        CPllUPllProg1     = pllTable[rownum].PllUPllProg1;
        CPllUPllProg0     = pllTable[rownum].PllUPllProg0;
        //dwc_ddrphy_phyinit_cmnt ("In the Loop\n");
      }//freq check
    }//checking row

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, From external csv file Programming CPllCtrl1 to 0x%x.\n", __func__, h, pstate, freq, CPllCtrl1);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMMAS | csr_CPllCtrl1_ADDR), CPllCtrl1);

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, From external csv file Programming CPllCtrl4 to 0x%x.\n", __func__, h, pstate, freq, CPllCtrl4);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMMAS | csr_CPllCtrl4_ADDR), CPllCtrl4);        

    dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, From external csv file Programming CpllCtrl5 to 0x%x.\n", __func__, h, pstate, freq, CpllCtrl5);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMMAS | csr_CPllCtrl5_ADDR), CpllCtrl5);

    if (pstate == pUserInputBasic->FirstPState){
      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllUPllProg0 to 0x%x.\n", __func__, h, pstate, freq, CPllUPllProg0);
      dwc_ddrphy_phyinit_io_write32((tHMMAS | csr_CPllUPllProg0_ADDR), CPllUPllProg0);

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllUPllProg1 to 0x%x.\n", __func__, h, pstate, freq, CPllUPllProg1);
      dwc_ddrphy_phyinit_io_write32((tHMMAS | csr_CPllUPllProg1_ADDR), CPllUPllProg1);

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllUPllProg2 to 0x%x.\n", __func__, h, pstate, freq, CPllUPllProg2);
      dwc_ddrphy_phyinit_io_write32((tHMMAS | csr_CPllUPllProg2_ADDR), CPllUPllProg2);

      dwc_ddrphy_phyinit_cmnt("[%s] %s Pstate=%d,  Memclk=%dMHz, Programming CPllUPllProg3 to 0x%x.\n", __func__, h, pstate, freq, CPllUPllProg3);
      dwc_ddrphy_phyinit_io_write32((tHMMAS | csr_CPllUPllProg3_ADDR), CPllUPllProg3);
    } // pstate == pUserInputBasic->FirstPState
  } //row_count != 0
}

void dwc_ddrphy_phyinit_programLCDLSeed(phyinit_config_t *phyctx, int mode, const char* print_header)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  user_input_sim_t *pUserInputSim = &phyctx->userInputSim;

  uint8_t pstate = pRuntimeConfig->curPState;
  uint32_t p_addr = (uint32_t) pstate << 20;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
  uint8_t NumHmacPerChan = NUM_HMAC_PER_CHAN;
  uint8_t DtoEnable = pUserInputAdvanced->DtoEnable;

  uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];  //  Data Rate in JEDEC



 if(mode==0){
 /**	 
   * - Program HMTxLcdlSeed, HMRxLcdlSeed, and HMRxReplicaLcdlSeed:
   *   - Description: Program seed in 2 places: Step C here and also progCsrSkiptraion.  Step C needs to set a seed for initial locking where the code is more or less uknown, whereas progCsrSkipTrain
   *                  needs to set a seed for fast locking to simulate what PIE code would see after training (SkipTrain only used when skipping FW training)
   *   - Fields:
   *     - TxLcdlSeed
   *     - TxCalModeIs1UI
   *     - TxLcdlCalDelta
   *     - RxLcdlSeed
   *     - RxCalModeIs1UI
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
	
  uint32_t LcdlCalModeIs1UI;
  uint16_t HMRxLcdlSeed;
  uint16_t HMTxLcdlSeed;
  uint16_t training_seed = (1000000/DataRateMbps)/3; //ceiling=503; floor=64.
  uint16_t ACHMTxLcdlSeed;
  uint16_t ac_training_seed = training_seed;


  if (DataRateMbps < 2667) {
    LcdlCalModeIs1UI = 1;
  } else {
    LcdlCalModeIs1UI = 0;
    training_seed = (2*(1000000/DataRateMbps))/3; //ceiling=503; floor=64.

    if((pUserInputAdvanced->AcQuarterDataRate == 0x1) && (DataRateMbps>=5500)) {
      ac_training_seed = (2*(1000000/(DataRateMbps/2)))/3;
    } else {
      ac_training_seed = training_seed;
    }
  }

  if (training_seed > 503) {
    training_seed = 503;
  }
  if (training_seed < 64) {
    training_seed = 64;
  }

  if (ac_training_seed > 503) {
    ac_training_seed = 503;
  }
  if (ac_training_seed < 64) {
    ac_training_seed = 64;
  }



  ACHMTxLcdlSeed = (ac_training_seed << csr_TxLcdlSeed_LSB) | (LcdlCalModeIs1UI << csr_TxCalModeIs1UI_LSB);
  HMTxLcdlSeed = (training_seed << csr_TxLcdlSeed_LSB) | (LcdlCalModeIs1UI << csr_TxCalModeIs1UI_LSB);
  HMRxLcdlSeed = (training_seed << csr_RxLcdlSeed_LSB) | (LcdlCalModeIs1UI << csr_RxCalModeIs1UI_LSB);


  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming Training Seed to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], training_seed);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming AC Training Seed to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], ac_training_seed);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming HMRxLcdlSeed HMRxSeed to 0x%x HMRxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], training_seed, LcdlCalModeIs1UI);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming HMRxReplicaLcdlSeed HMRxSeed to 0x%x HMRxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], training_seed, LcdlCalModeIs1UI);

  for (int acx = 0; acx < NumAchnActive; acx++) {
    for (int hmac = 0; hmac < NumHmacPerChan; hmac++) {
      int c_addr = (hmac + acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)

 
      dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d HMTxLcdlSeed HMTxSeed to 0x%x HMTxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], acx, hmac, instance, ac_training_seed, LcdlCalModeIs1UI);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_HMTxLcdlSeed_ADDR), ACHMTxLcdlSeed);
      _PROG_DTO(DtoEnable, acx, hmac, "HMTxLcdlSeed", (p_addr | tHMAC | c14 | csr_HMTxLcdlSeed_ADDR), ACHMTxLcdlSeed)
    }
  }

  /**
   * - Program Seq0BGPR10, Seq0BGPR11:
   *   - Description: Save HMTxLcdlSeed in GPR10/11 for PIE PclkDCA
   *   - Dependencies:
   *     - None
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Programming Seq0BGPR10 to HMTxLcdlSeed Full search value = 0x%x\n", __func__, HMTxLcdlSeed|csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR10_ADDR), HMTxLcdlSeed|csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR11_ADDR), HMTxLcdlSeed);

  /**
   * - Program Seq0BGPR21, Seq0BGPR22:
   *   - Description: Save AC HMTxLcdlSeed in GPR21/22 for PIE PclkDCA
   *   - Dependencies:
   *     - None
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Programming Seq0BGPR21 to ACHMTxLcdlSeed Full search value = 0x%x\n", __func__, HMTxLcdlSeed|csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR21_ADDR), ACHMTxLcdlSeed|csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR22_ADDR), ACHMTxLcdlSeed);


  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr0 = ((byte*2) & 0xf) * c1;
    uint32_t c_addr1 = (((byte*2)+1) & 0xf) * c1;


    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_HMTxLcdlSeed_ADDR), HMTxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_HMRxLcdlSeed_ADDR), HMRxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_HMRxReplicaLcdlSeed_ADDR), HMRxLcdlSeed);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_HMTxLcdlSeed_ADDR), HMTxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_HMRxLcdlSeed_ADDR), HMRxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_HMRxReplicaLcdlSeed_ADDR), HMRxLcdlSeed);
  }

 } else{  //mode=1 for progCSRSkipTrain
 /**
   *
   * Program HMTxLcdlSeed, HMRxLcdlSeed, and HMRxReplicaLcdlSeed
   *   - HMTxLcdlSeed is programmed in 2 places: Step C and also here in progCsrSkipTrain.  Step C needs to set a seed for
   *     initial locking where the code is more or less unknown, whereas porgCsrSkipTrain needs to set a seed for fast
   *     locking to simulate what pie code would see after training (SkipTrain only used when skipping FW training).
   *
   */
  float LcdlStepSize = (pUserInputSim->LcdlStepSizex10 / 10.0);
  int stepsize_x10 = LcdlStepSize*10;
  int DxFreq = pUserInputBasic->Frequency[pstate];
  DxFreq *= (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 2 : 4;
  uint16_t DxSeed = (1000000 * 10 * 100) / (2 * DxFreq * stepsize_x10 * 100); // *100/105 is to bias the seed low
  uint16_t DxSeedX2 = 2 * DxSeed;
  uint16_t HMTxSeed;
  uint16_t HMTxSeedIs1UI;
  uint16_t HMRxSeed;
  uint16_t HMRxSeedIs1UI;
  uint16_t AcQdrDxSeed = (1000000 * 10 * 100) / (2 * (DxFreq/2) * stepsize_x10 * 100);
  uint32_t wdACHMTxLcdlSeed;
  int wdHMTxLcdlSeed;
  int wdHMRxLcdlSeed;


  if (DxSeed > 503) {
    DxSeed = 503;
  }
  if (DxSeed < 8) {
    DxSeed = 8;
  }
  if (DxSeedX2 > 503) {
    DxSeedX2 = 503;
  }

  if (DataRateMbps < 2667) { // JEDEC DataRate
    HMTxSeed = DxSeed;
    HMTxSeedIs1UI = 1;
  } else {
    if (DxSeedX2 < 64) {
      HMTxSeed = 64; // relocking will have time to take it smaller if required for extreme high freq
      HMTxSeedIs1UI = 0;
    } else {
      HMTxSeed = ((95 * DxSeedX2)/100); // JUST FOR TESTING LOCK TIME FOR 5 percent low
      HMTxSeedIs1UI = 0;
    }
  }

  if (DataRateMbps < 2667) { // JEDEC DataRate
    HMRxSeed = DxSeed;
    HMRxSeedIs1UI = 1; // 1 for low-freq if 2UI seed is more than 9'h1ff; posedge pclk is a 2UI clock
  } else {
    if (DxSeedX2 < 64) {
      HMRxSeed = 64; // relocking will have time to take it smaller if required for extreme high freq
      HMRxSeedIs1UI = 0;
    } else {
      HMRxSeed = (95 * DxSeedX2)/100; // JUST FOR TESTING LOCK TIME FOR 5 percent low
      HMRxSeedIs1UI = 0;
    }
  }
  // Calculate AC quater data rate seed if userInput enabled and data rate >= 5500 Mbps
  if ((pUserInputAdvanced->AcQuarterDataRate == 0x1) && (DataRateMbps>=5500)) {
    // 2UI mode
    AcQdrDxSeed = (95 * (2 * AcQdrDxSeed))/100;
  } else {
    AcQdrDxSeed = HMTxSeed;
  }

  uint16_t ExtendPhdTime;
  if (DataRateMbps < 1333) { // JEDEC DataRate
     ExtendPhdTime = 3;
  } else if (DataRateMbps < 2667) { // JEDEC DataRate
     ExtendPhdTime = 4;
  } else if (DataRateMbps < 5333) { // JEDEC DataRate
     ExtendPhdTime = 5;
  } else if (DataRateMbps <= 8533) {
     ExtendPhdTime = 6;
  } else {
     ExtendPhdTime = 8;
  }


  wdACHMTxLcdlSeed = (AcQdrDxSeed << csr_TxLcdlSeed_LSB) | (HMTxSeedIs1UI << csr_TxCalModeIs1UI_LSB);
  wdHMTxLcdlSeed = (HMTxSeed << csr_TxLcdlSeed_LSB) | (HMTxSeedIs1UI << csr_TxCalModeIs1UI_LSB);
  wdHMRxLcdlSeed = (HMRxSeed << csr_RxLcdlSeed_LSB) | (HMRxSeedIs1UI << csr_RxCalModeIs1UI_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming DxSeed to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate],DxSeed   );
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming AcSeed to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate],AcQdrDxSeed   );
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming HMTxLcdlSeed HMTxSeed to 0x%x HMTxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], HMTxSeed, HMTxSeedIs1UI);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming HMRxLcdlSeed HMRxSeed to 0x%x HMRxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], HMRxSeed, HMRxSeedIs1UI);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming HMRxReplicaLcdlSeed HMRxSeed to 0x%x HMRxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], HMRxSeed, HMRxSeedIs1UI);

  dwc_ddrphy_phyinit_io_write32((p_addr | tMASTER | csr_DllTrainParam_ADDR), ((ExtendPhdTime<<csr_RxReplicaExtendPhdTime_LSB) | (ExtendPhdTime<<csr_ExtendPhdTime_LSB)));

  for (unsigned acx=0; acx<NumAchnActive; acx++) {
    for (unsigned hmac=0; hmac<NumHmacPerChan; hmac++) {
      unsigned c_addr = (hmac + acx*NumHmacPerChan)*c1;
      unsigned instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)

	      
      dwc_ddrphy_phyinit_cmnt("[%s] LcdlSeed Pstate=%d, Memclk=%dMHz, Programming ACX%d HMAC%d Instance%d HMTxLcdlSeed HMTxSeed to 0x%x HMTxSeedIs1UI 0x%x \n", __func__, pstate, pUserInputBasic->Frequency[pstate], acx, hmac, instance, AcQdrDxSeed, HMTxSeedIs1UI);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_HMTxLcdlSeed_ADDR), wdACHMTxLcdlSeed);
      _PROG_DTO(DtoEnable, acx, hmac, "HMTxLcdlSeed", (p_addr | tHMAC | c14 | csr_HMTxLcdlSeed_ADDR), wdACHMTxLcdlSeed)
    }
  }

  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr0 = ((byte*2) & 0xf) * c1;
    unsigned c_addr1 = (((byte*2)+1) & 0xf) * c1;


    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_HMTxLcdlSeed_ADDR), wdHMTxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_HMRxLcdlSeed_ADDR), wdHMRxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_HMRxReplicaLcdlSeed_ADDR), wdHMRxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_HMTxLcdlSeed_ADDR), wdHMTxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_HMRxLcdlSeed_ADDR), wdHMRxLcdlSeed);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_HMRxReplicaLcdlSeed_ADDR), wdHMRxLcdlSeed);
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Programming Seq0bGPR10 to mission mode HMTxLcdlSeed value 0x%x\n", __func__, pstate, wdHMTxLcdlSeed | csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR10_ADDR), wdHMTxLcdlSeed | csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Programming Seq0bGPR11 to mission mode HMTxLcdlSeed value 0x%x\n", __func__, pstate, wdHMTxLcdlSeed);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR11_ADDR), wdHMTxLcdlSeed);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Programming Seq0bGPR21 to mission mode HMTxLcdlSeed value 0x%x\n", __func__, pstate, wdACHMTxLcdlSeed | csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR21_ADDR), wdACHMTxLcdlSeed | csr_TxCalModeIs1UI_MASK);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Programming Seq0bGPR22 to mission mode HMTxLcdlSeed value 0x%x\n", __func__, pstate, wdACHMTxLcdlSeed);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | c0 | csr_Seq0BGPR22_ADDR), wdACHMTxLcdlSeed);

  /**
  * - Program RDqRDqsCntrl
  * Sets Dq/Dqs receiver control
  *
  */
  uint16_t RDqRDqsCntrl;
  RDqRDqsCntrl = (HMRxSeed << csr_RxPubLcdlSeed_LSB) | (HMRxSeedIs1UI << csr_RxPubCalModeIs1UI_LSB) | (HMRxSeedIs1UI << csr_RxPubRxReplicaCalModeIs1UI_LSB);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming RDqRDqsCntrl to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], RDqRDqsCntrl);
  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RDqRDqsCntrl_ADDR), RDqRDqsCntrl);
  }
 }
}

/** \brief Count the number of pipeline stages for a given PipeEn setting
 *
 * This function returns the number of pipeline stages that are programmed in a corresponding PipeCtl CSR field
 *
 * \param PipeEn       PipeCtl PipeEn field programmed into PipeCtl CSR
 *
 * \return uint16_t
 */
uint16_t dwc_ddrphy_phyinit_getNumPipeStages(uint16_t PipeEn) {
  uint16_t count = 0;
  while (PipeEn) {
    count += PipeEn & 1;
    PipeEn >>= 1;
  }

  return count;
}

/** \brief Program the PclkDca feature CSRs
 *
 * \param phyctx       Data structure to hold user-defined parameters
 * \param pstate       Current PState PhyInit is executing
 *
 * \return void
 */
void dwc_ddrphy_phyinit_programPclkDca(phyinit_config_t *phyctx, int pstate) {
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint16_t regData;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive; 
  uint8_t NumHmacPerChan = NUM_HMAC_PER_CHAN;
  uint8_t DtoEnable = pUserInputAdvanced->DtoEnable;
  uint32_t p_addr = pstate << 20;


  uint8_t DfiFreqRatio = pUserInputBasic->DfiFreqRatio[pstate];
  uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
  uint16_t DfiFreq = pRuntimeConfig->DfiFreq[pstate];
  float DfiClkPeriod = 1000.0/DfiFreq;

  /**
   * - Program PclkDCALcdlAddDlySampEn (HMAC, HMDBYTE)
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   */
  uint8_t PclkDCALcdlAddDlySampEn = (DfiFreqRatio == 1) ? 2 : 4;

  for (int acx = 0; acx < NumAchnActive; acx++) {
    for (int hmac = 0; hmac < NumHmacPerChan; hmac++) {
      int c_addr = (hmac + acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming ACX%d HMAC%d Instance%d PclkDCALcdlAddDlySampEn to 0x%x\n", __func__, pstate, acx, hmac, instance, PclkDCALcdlAddDlySampEn);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_PclkDCALcdlAddDlySampEn_ADDR), PclkDCALcdlAddDlySampEn);
      _PROG_DTO(DtoEnable, acx, hmac, "PclkDCALcdlAddDlySampEn", (p_addr | tHMAC | c14 | csr_PclkDCALcdlAddDlySampEn_ADDR), PclkDCALcdlAddDlySampEn)
    }
  }

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMDBYTE%d PclkDCALcdlAddDlySampEn to 0x%x\n", __func__, pstate, byte, PclkDCALcdlAddDlySampEn);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_PclkDCALcdlAddDlySampEn_ADDR), PclkDCALcdlAddDlySampEn);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_PclkDCALcdlAddDlySampEn_ADDR), PclkDCALcdlAddDlySampEn);
  }

  /*
   * - Program PclkDCASampDelayLCDLAC and PclkDCASampDelayLCDLDB
   */
  uint8_t PclkDCASampDelayLCDL;

    PclkDCASampDelayLCDL = (phyctx->PclkPtrInitVal[pstate] + 1) / 8;

  for (int acx=0; acx < NumAchnActive; acx++) {
    for (int hmac=0; hmac < NumHmacPerChan; hmac++) {
      int c_addr = (hmac + acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Programming ACX%d HMAC%d Instance%d PclkDCASampDelayLCDLAC to 0x%x\n", __func__, acx, hmac, instance, PclkDCASampDelayLCDL);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_PclkDCASampDelayLCDLAC_ADDR), PclkDCASampDelayLCDL);
      _PROG_DTO(DtoEnable, acx, hmac, "PclkDCASampDelayLCDLAC", (p_addr | tHMAC | c14 | csr_PclkDCASampDelayLCDLAC_ADDR), PclkDCASampDelayLCDL)
    }
  }

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr = byte * c1;

    dwc_ddrphy_phyinit_cmnt("[%s] Programming DBYTE%d PclkDCASampDelayLCDLDB to 0x%x\n", __func__, byte, PclkDCASampDelayLCDL);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PclkDCASampDelayLCDLDB_ADDR), PclkDCASampDelayLCDL);
  }

  /**
   * - Program PclkDCAStaticCtrl0AC/DB DCA/DCD related CSR's.
   *   - Fields:
   *     -PclkDCACalMode
   *     -PclkDCAEn
   *     -PclkDCATxLcdlPhSel
   *     -PclkDCDSettle
   *     -PclkDCDSampTime
   *   - Dependencies:
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   */

  // pick LCDL @ < DDR4800
  uint32_t PclkDCACalMode = 0x0; // Keep DCA CAl Mode = 0 such that DCD will be selected for PClkDCA

  // turn off DCA @ < DDR2400
  uint32_t PclkDCAEn = (DataRateMbps <= 3200) ? 0x0 : 0x1;

  // LCDL phase code section for DCA calibration.
  uint32_t PclkDCATxLcdlPhSel = (DataRateMbps < 2667) ? 0x0 : // LCDL is 1UI
                                                      (DataRateMbps < 4800) ? 0x1 : // LCDL is 2UI
                                                      0x2 ; // DCM is used.

  uint32_t PclkDCDSettle = ceil((((DfiClkPeriod + ((phyctx->PclkPtrInitVal[pstate] + 3)*(1000.0/(DataRateMbps/2.0))) + 0.0845 + 10.0)/DfiClkPeriod) + 1.0)/2.0);
  uint32_t PclkDCDSampTime = 0x2;

  regData = (PclkDCACalMode << csr_PclkDCACalModeAC_LSB) |
                      (PclkDCAEn << csr_PclkDCAEnAC_LSB) |
                      (PclkDCATxLcdlPhSel << csr_PclkDCATxLcdlPhSelAC_LSB) |
                      (PclkDCDSettle << csr_PclkDCDSettleAC_LSB) |
                      (PclkDCDSampTime << csr_PclkDCDSampTimeAC_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming PclkDCAStaticCtr0AC to 0x%x\n", __func__, pstate, regData);

  for (int achn = 0; achn < NumAchnActive; achn++) {
    int c_addr = achn * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | csr_PclkDCAStaticCtrl0AC_ADDR), regData);
  }

  regData = (PclkDCACalMode << csr_PclkDCACalModeDB_LSB) |
                      (PclkDCAEn << csr_PclkDCAEnDB_LSB) |
                      (PclkDCATxLcdlPhSel << csr_PclkDCATxLcdlPhSelDB_LSB) |
                      (PclkDCDSettle << csr_PclkDCDSettleDB_LSB) |
                      (PclkDCDSampTime << csr_PclkDCDSampTimeDB_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming PclkDCAStaticCtr0DB to 0x%x\n", __func__, pstate, regData);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr = byte * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PclkDCAStaticCtrl0DB_ADDR), regData);
  }

  /*
   * Program PclkDCAStaticCtrl1 AC/DB
   *
   *   Fields:
   *     PclkDCAInvertSampAC/DB --   depends on PclkDCACalMode
   */

  // set InvertSamp if needed.
  uint8_t PclkDCAInvertSamp = 0x1;
  uint8_t PclkDCALcdlEn4p = 0;
  uint8_t PclkDCDMissionModeDelay = ceil((((DfiClkPeriod + ((phyctx->PclkPtrInitVal[pstate] + 3)*(1000.0/(DataRateMbps/2))) + 0.0845 + 13)/DfiClkPeriod) + 1.0)/2.0);

  PclkDCALcdlEn4p = (DfiFreqRatio == 2) ? 1 : 0;

  regData = (PclkDCAInvertSamp << csr_PclkDCAInvertSampAC_LSB) | (PclkDCALcdlEn4p << csr_PclkDCALcdlEn4pAC_LSB) | (PclkDCDMissionModeDelay << csr_PclkDCDMissionModeDelayAC_LSB);

  for (int acx=0; acx < NumAchnActive; acx++) {
    for (int hmac=0; hmac < NumHmacPerChan; hmac++) {
      int c_addr = (hmac + acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming ACX%d HMAC%d Instance%d PclkDCAStaticCtrl1AC to 0x%x\n", __func__, pstate, acx,  hmac, instance, regData);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_PclkDCAStaticCtrl1AC_ADDR), regData);
      _PROG_DTO(DtoEnable, acx, hmac, "PclkDCAStaticCtrl1AC", (p_addr | tHMAC | c14 | csr_PclkDCAStaticCtrl1AC_ADDR), regData)
    }
  }

  regData = (PclkDCAInvertSamp << csr_PclkDCAInvertSampDB_LSB) | (PclkDCALcdlEn4p << csr_PclkDCALcdlEn4pDB_LSB) | (PclkDCDMissionModeDelay << csr_PclkDCDMissionModeDelayDB_LSB);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming PclkDCAStaticCtrl1DB to 0x%x\n", __func__, pstate, regData);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr = byte * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PclkDCAStaticCtrl1DB_ADDR), regData);
    }

  /*
   * - Program PclkDCATxLcdlPhase
   */
  regData = 0x1f;
  for (int acx = 0; acx < NumAchnActive; acx++) {
    for (int hmac = 0; hmac < NumHmacPerChan; hmac++) {
      int c_addr = (hmac + acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;
      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming ACX%d HMAC%d Instance%d PclkDCATxLcdlPhase to 0x%x\n", __func__, pstate, acx, hmac, instance, regData);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c_addr | csr_PclkDCATxLcdlPhase_ADDR), regData);
      _PROG_DTO(DtoEnable, acx, hmac, "PclkDCATxLcdlPhase", (p_addr | tHMAC | c14 | csr_PclkDCATxLcdlPhase_ADDR), regData)
    }
  }

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf) * c1;

    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMDBYTE%d PclkDCATxLcdlPhase to 0x%x\n", __func__, pstate, byte, regData);

    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr0 | csr_PclkDCATxLcdlPhase_ADDR), regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMDBYTE | c_addr1 | csr_PclkDCATxLcdlPhase_ADDR), regData);
  }

  /*
   * - Program Quick and Full Search durations
   */

  uint16_t Seq0BDLY8_data, Seq0BDLY9_data;
  uint16_t DCDSampleTime = 4 + (2*PclkDCDSettle) + PclkDCDSampTime;
  Seq0BDLY8_data = ceil(0.25 * (4+(4*DCDSampleTime)));
  Seq0BDLY9_data = ceil(0.25 * (4+(14*DCDSampleTime)));
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming Seq0BDLY8 to %d\n", __func__, pstate, Seq0BDLY8_data);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming Seq0BDLY9 to %d\n", __func__, pstate, Seq0BDLY9_data);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY8_ADDR), Seq0BDLY8_data); // quick search
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BDLY9_ADDR), Seq0BDLY9_data); // full search
}

/** @} */


