/** \file
 *  \brief routine to save registers for IO retention restore
 *  \addtogroup CustFunc
 *  @{
 */
#include <stdlib.h>
#include <math.h>
#include "dwc_ddrphy_phyinit.h"

/** \brief This function can be used to implement saving of PHY registers to be
 * restored on retention exit.
 *
 * The requirement of this function is to issue register reads and store the
 * value to be recovered on retention exit.  The following is an example
 * implementation and the user may implement alternate methods that suit their
 * specific SoC system needs.
 *
 * In this implementation PhyInit saves register values in an internal C array.
 * During retention exit it restores register values from the array.  The exact
 * list of registers to save and later restore can be seen in the output txt
 * file with an associated calls to dwc_ddrphy_phyinit_usercustom_io_read32().
 *
 * PhyInit provides a register interface and a tracking mechanism to minimize
 * the number registers needing restore. Refer to source code for
 * dwc_ddrphy_phyinit_regInterface() for detailed implementation of tracking
 * mechanism. Tracking is disabled from step D to Step H as these involve
 * loading, executing and checking the state of training firmware execution
 * which are not required to implement the retention exit sequence. The registers
 * specified in firmware training App Note representing training results are
 * also saved in addition to registers written by PhyInit during PHY
 * initialization.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns \c void
 */
void dwc_ddrphy_phyinit_userCustom_saveRetRegs(phyinit_config_t *phyctx) {
  uint16_t regData;
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  int numHwPStates = DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;

  dwc_ddrphy_phyinit_cmnt(" [%s] Start of %s\n", __func__, __func__);
  dwc_ddrphy_phyinit_cmnt("\n\n");
  dwc_ddrphy_phyinit_cmnt("//##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// Customer Save Retention Registers\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// This function can be used to implement saving of PHY registers to be\n");
  dwc_ddrphy_phyinit_cmnt("// restored on retention exit. the following list of register reads can\n");
  dwc_ddrphy_phyinit_cmnt("// be used to compile the exact list of registers.\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("//##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n\n");

  /// In short the implementation of this function performs tasks:

  // --------------------------------------------------------------------------
  /// 1. Enable tracking of training firmware result registers\n
  ///    \note  The tagged registers in this step are in
  ///    addition to what is automatically tagged during Steps C to I.
  ///
  // --------------------------------------------------------------------------

  // 95% of users should not require to change the code below.
  uint32_t pstate;
  uint32_t NumPStates;
  uint32_t anib;
  uint32_t byte;
  uint32_t lane;
  uint32_t p_addr;
  uint32_t c_addr;
  uint32_t r_addr;

  uint8_t NumDbyte = pRuntimeConfig->NumDbyte;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;

  NumPStates = DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;

  dwc_ddrphy_phyinit_trackReg(tHMMAS | csr_CPllCtrl3_ADDR);
  dwc_ddrphy_phyinit_trackReg(tZCAL | csr_ZCalCompResult_ADDR);
  dwc_ddrphy_phyinit_trackReg(tAPBONLY | csr_DctWriteProt_ADDR);
  dwc_ddrphy_phyinit_trackReg(tDRTUB | csr_UctWriteProt_ADDR);
  dwc_ddrphy_phyinit_trackReg(tDRTUB | csr_UctDatWriteOnly_ADDR);
  dwc_ddrphy_phyinit_trackReg(tDRTUB | csr_UctlErr_ADDR);

  // Non-PState Dbyte Registers
  for (byte = 0; byte < NumDbyteActive; byte++) {
    c_addr = byte << 12;
    for (lane = r_min; lane <= r_max; lane++) {
      r_addr = lane << 8;
      dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | r_addr | csr_TrainingIncDecDtsmEn_ADDR);
    }
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_DtsmByteCtrl0_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq0LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq1LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq2LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq3LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq4LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq5LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq6LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq7LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_Dq8LnSel_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_RxReplicaUICalWait_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_RxClkCntl_ADDR);
    dwc_ddrphy_phyinit_trackReg(tDBYTE | c_addr | csr_RxClkCntl1_ADDR);
  } // c_addr
  for (byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr0 = ((byte*2) & 0xfu) * c1;
    uint32_t c_addr1 = (((byte*2)+1) & 0xfu) * c1;
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr0 | csr_RxModeCtl_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr1 | csr_RxModeCtl_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr0 | csr_RxDFEBiasSelLn0_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr1 | csr_RxDFEBiasSelLn0_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr0 | csr_RxDFEBiasSelLn1_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr1 | csr_RxDFEBiasSelLn1_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr0 | csr_RxDFEBiasSelLn2_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr1 | csr_RxDFEBiasSelLn2_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr0 | csr_RxDFEBiasSelLn3_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr1 | csr_RxDFEBiasSelLn3_ADDR);
    dwc_ddrphy_phyinit_trackReg(tHMDBYTE | c_addr1 | csr_RxDFEBiasSelLn4_ADDR);
  }

  // PState variable registers
  for (pstate = 0; pstate < NumPStates; pstate++) {
    uint32_t cfgPStates = pUserInputBasic->CfgPStates;
    if ((cfgPStates & (0x1u << pstate)) == 0) {
      continue;
    }
    p_addr = pstate << 20;

    // MASTER Registers
    dwc_ddrphy_phyinit_trackReg(p_addr | tMASTER | csr_DllTrainParam_ADDR);

    // Anib Registers
    for (anib = 0; anib < NumAchnActive; anib++) {
      c_addr = anib << 12;
      dwc_ddrphy_phyinit_trackReg(p_addr | tAC | c_addr | csr_CKXTxDly_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tAC | c_addr | csr_ACSingleEndedMode_ADDR);
      for (lane = 0; lane < 10; lane++) {
        r_addr = lane << 8;
        dwc_ddrphy_phyinit_trackReg(p_addr | tAC | c_addr | r_addr | csr_ACXTxDly_ADDR);
      } // lane
    } // numch
    for (anib = 0; anib < NumAchnActive; anib++) {
      for (uint8_t hmac = 0; hmac < 5; hmac++) {
        c_addr = (hmac + anib*NUM_HMAC_PER_CHAN)*c1;
        _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)
        dwc_ddrphy_phyinit_trackReg(p_addr | tHMAC | c_addr | csr_PclkDCACodeAC0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tHMAC | c_addr | csr_PclkDCACodeAC1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tHMAC | c_addr | csr_PclkDCDOffsetAC0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tHMAC | c_addr | csr_PclkDCDOffsetAC1_ADDR);
      }
    }

    // Dbyte Registers
    for (byte = 0; byte < NumDbyteActive; byte++) {
      c_addr = byte << 12;
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_DFIMRL_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaCtl01_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaCtl03_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaPathPhase0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaPathPhase1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaPathPhase2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaPathPhase3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxReplicaPathPhase4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxEnDlyTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxEnDlyTg1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxDqsDlyTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxDqsDlyTg1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxWckDlyTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxWckDlyTg1_ADDR);

      for (lane = r_min; lane <= r_max; lane++) {
        r_addr = lane << 8;

        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxDigStrbDlyTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxDigStrbDlyTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_TxDqDlyTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_TxDqDlyTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkT2UIDlyTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkT2UIDlyTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkC2UIDlyTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkC2UIDlyTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_DqRxVrefDac_ADDR);

        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkTLeftEyeOffsetTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkTLeftEyeOffsetTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkTRightEyeOffsetTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkTRightEyeOffsetTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkCLeftEyeOffsetTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkCLeftEyeOffsetTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkCRightEyeOffsetTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_RxClkCRightEyeOffsetTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_TxDqLeftEyeOffsetTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_TxDqLeftEyeOffsetTg1_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_TxDqRightEyeOffsetTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | r_addr | csr_TxDqRightEyeOffsetTg1_ADDR);

      } // r_addr

      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_PptDqsCntInvTrnTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_PptDqsCntInvTrnTg1_ADDR);

      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_PptWck2DqoCntInvTrnTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_PptWck2DqoCntInvTrnTg1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxDqsLeftEyeOffsetTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxDqsLeftEyeOffsetTg1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxDqsRightEyeOffsetTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_TxDqsRightEyeOffsetTg1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RDqRDqsCntrl_ADDR);
    } // c_addr

    // Master Registers
    dwc_ddrphy_phyinit_trackReg(p_addr | tHMMAS | csr_CPllDacValIn_ADDR);
    dwc_ddrphy_phyinit_trackReg(p_addr | tPPGC | csr_HwtMRL_ADDR);

    // Hardmacro dbyte registers
    for (byte = 0; byte < NumDbyteActive; byte++) {
      uint32_t c_addr0 = ((byte*2) & 0xfu) * c1;
      uint32_t c_addr1 = (((byte*2)+1) & 0xfu) * c1;
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelEvenSLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelEvenSLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelEvenSLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelEvenSLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelEvenSLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelEvenSLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelEvenSLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelEvenSLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelEvenSLn4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelOddSLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelOddSLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelOddSLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelOddSLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelOddSLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelOddSLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxOffsetSelOddSLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelOddSLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxOffsetSelOddSLn4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCACodeDqLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCACodeDqLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCACodeDqLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCACodeDqLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCACodeDqLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCACodeDqLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCACodeDqLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCACodeDqLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCACodeDqLn4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCACodeDQS_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCACodeDQS_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCDOffsetDqLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCDOffsetDqLn0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCDOffsetDqLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCDOffsetDqLn1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCDOffsetDqLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCDOffsetDqLn2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCDOffsetDqLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCDOffsetDqLn3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCDOffsetDqLn4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_PclkDCDOffsetDQS_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_PclkDCDOffsetDQS_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg0Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg0Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg0Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg0Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg0Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg0Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg0Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg0Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg0Ln4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg1Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg1Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg1Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg1Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg1Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg1Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap1SelTg1Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg1Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap1SelTg1Ln4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg0Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg0Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg0Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg0Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg0Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg0Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg0Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg0Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg0Ln4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg1Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg1Ln0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg1Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg1Ln1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg1Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg1Ln2_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDFETap2SelTg1Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg1Ln3_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDFETap2SelTg1Ln4_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_TxDcaCtrlTTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_TxDcaCtrlTTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_TxDcaCtrlTTg1_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_TxDcaCtrlTTg0_ADDR);
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_TxDcaCtrlCTg0_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_TxDcaCtrlCTg0_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_TxDcaCtrlCTg1_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_TxDcaCtrlCTg1_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDcaCtrlTTg0_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDcaCtrlTTg0_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDcaCtrlTTg1_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDcaCtrlTTg1_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDcaCtrlCTg0_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDcaCtrlCTg0_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr0 | csr_RxDcaCtrlCTg1_ADDR );
      dwc_ddrphy_phyinit_trackReg(p_addr | tHMDBYTE | c_addr1 | csr_RxDcaCtrlCTg1_ADDR );
    } // c_addr

    // INITENG Registers
    dwc_ddrphy_phyinit_trackReg(p_addr | tINITENG | csr_Seq0BGPR7_ADDR);
    dwc_ddrphy_phyinit_trackReg(p_addr | tINITENG | csr_Seq0BGPR8_ADDR);
  } // p_addr

  // PPGC Registers
  dwc_ddrphy_phyinit_trackReg(tPPGC | csr_HwtCtrl_ADDR);

  // 2D Training Registers
  if (pRuntimeConfig->Train2D) {
    for (byte = 0; byte < NumDbyteActive; byte++) {
      c_addr = byte << 12;

      for (pstate = 0; pstate < NumPStates; pstate++) {
        uint32_t cfgPStates = pUserInputBasic->CfgPStates;
        if ((cfgPStates & (0x1u << pstate)) == 0) {
          continue;
        }
        p_addr = pstate << 20;
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxClkT2UIDlyTg0_ADDR);
        dwc_ddrphy_phyinit_trackReg(p_addr | tDBYTE | c_addr | csr_RxClkT2UIDlyTg1_ADDR);
      } // p_addr
    } // byte
  }

  // --------------------------------------------------------------------------
  /// 2. Track any additional registers\n
  ///    Register writes made using any of the PhyInit functions are
  ///    automatically tracked using the call to dwc_ddrphy_phyinit_trackReg() in
  ///    dwc_ddrphy_phyinit_io_write32(). Use this section to track
  ///    additional registers.\n
  ///    Example:\n
  ///    @code{.c}
  ///    dwc_ddrphy_phyinit_trackReg(<addr>);
  ///    @endcode
  ///
  // --------------------------------------------------------------------------


  // --------------------------------------------------------------------------
  /// 3. Prepare for register reads\n
  ///    - Write the MicroContMuxSel CSR to 0x0 to allow access to the internal CSRs
  ///    - Write the UcclkHclkEnables CSR to 0x7 to enable all the clocks so the reads can complete
  ///    - Program UcclkHclkEnables
  ///    - Program ZCAL clkdiv to 1:1
  ///    - Program PubDbyteDisable
  ///    - Program ZCalStopClk
  ///
  // --------------------------------------------------------------------------
  uint8_t lowest = 0;

  for (pstate = 0; pstate < NumPStates; pstate++) {
    uint32_t cfgPStates = pUserInputBasic->CfgPStates;
    if ((cfgPStates & (0x1u << pstate)) == 0) {
      continue;
    }
    lowest = pstate;
    break;
  }
  uint16_t pmuClkEnables = csr_HclkEn_MASK | csr_UcclkEn_MASK;

  // --------------------------------------------------------------------------
  // - Program UcclkHclkEnables:
  //   - Description: UcClk/Hclk Enables
  //   - Fields:
  //     - UcclkEn
  //     - HclkEn
  //     - UcclkFull
  // --------------------------------------------------------------------------
  if (pUserInputAdvanced->PmuClockDiv[lowest] == 0) {
    pmuClkEnables |= (uint16_t) csr_UcclkFull_MASK;
  }
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(0x0);
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  // --------------------------------------------------------------------------
  // - Program ZCAL clkdiv to 1:1
  // --------------------------------------------------------------------------
  dwc_ddrphy_phyinit_cmnt("[%s] Programming Zcalclkdiv to 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_userCustom_io_write32((tZCAL | csr_ZcalClkDiv_ADDR), 0x0);

  // Enable both DFI channels to read CSRs from either channel
  dwc_ddrphy_phyinit_programDfiMode(phyctx, enableDfiMode);


  //Disable PubDbyteDisable to all DBYTE's so reads from DBYTE will complete
  // --------------------------------------------------------------------------
  //   - Program PubDbyteDisable:
  //     - Description: Power down unused DBYTE's
  //     - Dependencies:
  //       - user_input_basic.NumCh
  //       - user_input_basic.NumDbytesPerCh
  // --------------------------------------------------------------------------

  dwc_ddrphy_phyinit_cmnt("[%s] Programming MASTER.PubDbyteDisable to 0x%x\n", __func__, 0x0u);
  dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_PubDbyteDisable_ADDR), 0x0u);

  // Disable ZCalStopClk to all PState's so reads from HMZCAL will complete
  // --------------------------------------------------------------------------
  //   - Program ZCalStopClk:
  //     - Description: Clear ZCalStopClk if user_input_advanced.PHYZCalPowerSaving is set before reading
  //                  S3 CSRs so HMZCAL CSR reads will complete 
  //     - Fields:
  //       - ZCalStopClk
  //     - Dependencies:
  //       - user_input_advanced.PHYZCalPowerSaving
  // --------------------------------------------------------------------------

  if (pUserInputAdvanced->PHYZCalPowerSaving == 0x1u) {
    for (pstate=0; pstate < numHwPStates; pstate++) {
      // Skip disabled PStates
      uint32_t cfgPStates = pUserInputBasic->CfgPStates;
      if ((cfgPStates & (0x1u << pstate)) == 0) {
        continue;
      }

      p_addr = pstate << 20;
      dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCAL.ZCalStopClk to 0x%x\n", __func__, 0x0u);
      dwc_ddrphy_phyinit_userCustom_io_write32((p_addr | tZCAL | csr_ZCalStopClk_ADDR), 0x0u);
    }
  }

  // --------------------------------------------------------------------------
  /// 4. Read and save all the registers
  ///   - The list of registers differ depending on protocol and training.
  ///
  // --------------------------------------------------------------------------
  
  dwc_ddrphy_phyinit_regInterface(saveRegs, 0, 0);

  // --------------------------------------------------------------------------
  /// 5. Prepare for mission mode
  ///    - Write the UcclkHclkEnables CSR to disable the appropriate clocks after all reads done.
  ///    - Write the MicroContMuxSel CSR to 0x1 to isolate the internal CSRs during mission mode
  ///    - Program PubDbyteDisable
  ///    - Program ZCalStopClk
  ///
  // --------------------------------------------------------------------------


  // Restore PubDbyteDisable to all DBYTE's to power down unused DBYTE's
  // --------------------------------------------------------------------------
  //   - Description: Power down unused DBYTE's
  //   - Dependencies:
  //     - user_input_basic.NumCh
  //     - user_input_basic.NumDbytesPerCh
  // --------------------------------------------------------------------------

  uint16_t pubDbyteDis = 0x0u;
  for (byte = 0; byte < NumDbyte; byte++) {
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte)) {
      pubDbyteDis |= (0x1u << byte);
    }
  }
  dwc_ddrphy_phyinit_cmnt("[%s] Programming MASTER.PubDbyteDisable to 0x%x\n", __func__, pubDbyteDis);
  dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_PubDbyteDisable_ADDR), pubDbyteDis);

  //Restore ZCalStopClk to all PState's if it is enabled
  // --------------------------------------------------------------------------
  //   - Description: Restore ZCalStopClk if user_input_advanced.PHYZCalPowerSaving is set after
  //                  S3 CSRs are read
  //   - Fields:
  //     - ZCalStopClk
  //   - Dependencies:
  //     - user_input_advanced.PHYZCalPowerSaving
  // --------------------------------------------------------------------------
  if (pUserInputAdvanced->PHYZCalPowerSaving == 0x1u) {
    for (pstate=0; pstate < numHwPStates; pstate++) {
      uint32_t cfgPStates = pUserInputBasic->CfgPStates;
      // Skip disabled PStates
      if ((cfgPStates & (0x1u << pstate)) == 0) {
        continue;
      }

      //  Data Rate in JEDEC
      uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
      uint16_t ZCalStopClk;
      p_addr = pstate << 20;
      if (DataRateMbps <= 3200) {
        ZCalStopClk = ((pUserInputAdvanced->PHYZCalPowerSaving)==1) ? 1 : 0;
        dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalStopClk:: to 0x%x\n", __func__, ZCalStopClk);
        dwc_ddrphy_phyinit_userCustom_io_write32((p_addr | tZCAL | csr_ZCalStopClk_ADDR), ZCalStopClk);
      }
    }
  }
  
  // Restore DFI channels to userInput based configuration
  dwc_ddrphy_phyinit_programDfiMode(phyctx, disableDfiMode);

  // --------------------------------------------------------------------------
  // - Restoring the value of ZCAL clkdiv 
  // --------------------------------------------------------------------------
  dwc_ddrphy_phyinit_cmnt("[%s] Programming ZcalClkDiv to 0x%x\n", __func__, pUserInputAdvanced->ZcalClkDiv[pUserInputBasic->FirstPState]);
  dwc_ddrphy_phyinit_userCustom_io_write32 ((tZCAL | csr_ZcalClkDiv_ADDR), pUserInputAdvanced->ZcalClkDiv[pUserInputBasic->FirstPState]);



  pmuClkEnables = 0x0u<<csr_HclkEn_LSB | 0x0u<<csr_UcclkEn_LSB;
  
  if (pUserInputAdvanced->PmuClockDiv[lowest] == 0) {
    pmuClkEnables |= (uint16_t) csr_UcclkFull_MASK;
  }
  
  dwc_ddrphy_phyinit_cmnt("// Disabling Ucclk (PMU) and Hclk (training hardware)\n");
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  // Isolate the APB access to internal CSRs
  regData = 0x1;
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(regData);

  dwc_ddrphy_phyinit_cmnt(" [%s] End of %s\n", __func__, __func__);
}

/** @} */
