Copyright 2024 Synopsys, Inc.
This Synopsys IP and all associated documentation are proprietary to
Synopsys, Inc. and may only be used pursuant to the terms and conditions
of a written license agreement with Synopsys, Inc. All other use,
reproduction, modification, or distribution of the Synopsys IP or the
associated documentation is strictly prohibited.
Inclusivity & Diversity - Read the Synopsys Statement on Inclusivity and Diversity at 
https://solvnetplus.synopsys.com/s/article/Synopsys-Statement-on-Inclusivity-and-Diversity
------------------------------------------------------------------
LPDDR5X/5/4X PHY PHYINIT
------------------------------------------------------------------------------

The PHYINIT software is a utility intended to provide usability assistance and
guidance to customers for PHY initialization, in the form of overall procedure
and CSR writes/configurations. The PHYINIT is intended to be a supplement to
be used in conjunction with all PHY related documentation (PUB/PHY Databooks,
Application Notes, Stars on the Web, and others). The user must follow the
procedures and CSR writes/configurations as outlined in the documentation, and
must not solely rely on the PHYINIT utility to guarantee correct operation for
their configuration, platform, SoC and other implementation specific
considerations. 

------------------------------------------------------------------------------
Version A-2024.08
July 26, 2024

Changes from version A-2024.05
(recommended)

Enhancements:
-------------
- Minor code updates

Bug fixes:
----------
- STAR 5570427: Remove UctWriteOnly from LP3 IO retention list
- STAR 5551218: PPT2 + DFI LP collision bug fix
- STAR 5720583: Remove ZCalPU/PDResult from LP3 IO retention list
- STAR 5720588: For Retrain Only/PMI when datarate <= 3200Mbps and DisZcalOnDataRate = 0, ZQ update is required

Input Changes:
--------------
- user_input_advanced.DqsSampNegRxEnSense default value changed to 0x1 for LPDDR5/5X
- Minor comment updates

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 5.2.0

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*, 2.21*, 2.22*, 2.30*, 2.40*
- Firmware:         A-2024.08


------------------------------------------------------------------------------
Version A-2024.05
May 13, 2024

Changes from version A-2024.02
(recommended)

Enhancements:
-------------
- Added support for JESD209-5C 
- Put RXDQS in powerdown mode when in strobeless mode
- Updated CK_T/C to tri-state during frequency change LP2 state to save power
- Minor code updates

Bug fixes:
----------
- STAR 5495963: Update the Datarate threshold from 4800Mbps to 5500Mbps for CPclkDivCa programming 

Input Changes:
--------------
- user_input_advanced.SnoopWAEn marked as reserved

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 5.2.0

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*, 2.30*
- Firmware:         A-2024.05


------------------------------------------------------------------------------
Version A-2024.02
December 15, 2023

Changes from version A-2023.10
(recommended)

Enhancements:
-------------
- Added support for 9600Mbps
- Added support for PPT2 feature
- Added support for programming DTO pin
- Program DisableZQUpdateOnSnoop if SNPS memory controller used
- Remove redundant DFES parameter in dwc_ddrphy_phyinit_setDefault.c
- Comments added for variable RdcfeDis and Wdcfedis in dwc_ddrphy_phyinit_setDefault.c
- Update to program CSR ACDlyScaleGatingDisable and NeverGateACDlyScaleValClk
- DisableFspOp description updates
- Minor code updates

Bug fixes:
----------
- STAR 5237180: LP5X Missing dwc_ddrphy_phyinit_userCustom_customPreTrain.c function call to print in output.txt
- STAR 5147066: Need to add additional latency between PIE programming ZQCalCOdeOvr* CSRs and turning off the ZCalStopClk
- STAR 5100051: LP5X dwc_ddrphy_phyinit_userCustom_saveRetRegs not saving upper HMAC/HMDBYTE chiplets

Input Changes:
--------------
- user_input_advanced.DisRxClkCLcdl added (reserved)
- user_input_advanced.Lp5xDeassertDramReset added (reserved)
- user_input_advanced.Lp5xFwTinit3WaitTimex1000 (reserved)
- user_input_advanced.ACDlyScaleGating added to program CSRs ACDlyScaleGatingDisable and NeverGateACDlyScaleValClk

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 5.2.0

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*, 2.30*
- Firmware:         A-2024.02


------------------------------------------------------------------------------
Version A-2023.10
September 28, 2023

Changes from version A-2023.07
(recommended)

Enhancements:
-------------
- LP5X/5 mr17.x8Odt{L,U}_r{0,1} in dwc_ddrphy_phyinit_setDefault.c changed to non PState'able subfields
- LP4X mr22.x8Odt{L,U}_r{0,1} in dwc_ddrhpy_phyinit_setDefault.c changed to non PState'able subfields
- Minor code updates

Bug fixes:
----------
- STAR 4952248: Set force_cal to 0 to match the PLL initial sequence
- STAR 4944748: Incorrect configuration for LPDDR5X/5/LPDDR4X mixed mode (x16/x8) and DBYTE swap
- STAR 4999451: CSR missing in PhyInit LP3 restore list

Input Changes:
--------------
- user_input_advanced.DisZCalOnDataRate added to enable/disable ZCal during frequency change based on data rate
- user_input_advanced.UseSnpsController added to be used with Synopsys Memory Controller
- user_input_advanced.DisableUnusedAddrLns removed, not used

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*
- Firmware:         A-2023.10


------------------------------------------------------------------------------
Version A-2023.07
June 30, 2023

Changes from version A-2023.05
(mandatory)

Enhancements:
-------------
- Program HMDBYTE TxImpedanceDqs for RDQS_C to Hi-Z
- Minor code updates

Bug fixes:
----------
- STAR 4828920: Added missing DqRxVrefDac CSR to the S3 restore list
- STAR 4812762: CPllCtrl5 does not match PLL spec
- STAR 4805966: LP5X/5 strobeless mode first dfi_init_start at 1600Mbps incorrectly executes PPT

Input Changes:
--------------
- user_input_basic.HardMacroVer updated description to add hardmacro family B
- user_input_advanced.DramByteSwap updated values in description
- user_input_advanced.PhyMstrMaxReqToAck updated values in description
- user_input_advanced.RxClkTrackWait removed as it was not used
- user_input_advanced.RxClkTrackWaitUI removed as it was not used
- user_input_advanced.EnRxDqsTracking removed as it was not used
- user_input_advanced.EnWck2DqoTracking description updated to indicate all PState's must have same value
- user_input_advanced.DtoEnable added to enable DTO pin

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  1.21a and 2.10a
- Firmware:         A-2023.07


------------------------------------------------------------------------------
Version A-2023.05
April 27, 2023

Changes from version A-2023.02
(mandatory)

Enhancements:
-------------
- In dwc_ddrphy_phyinit_setDefault.c, LP5/5X mr17 split into mr17_rank0/mr17_rank1, LP4X mr22 split into mr22_rank0/mr22_rank1
- In dwc_ddrphy_phyinit_setDefault.c, message block RFU bit SequenceCtrl[8] value changed from 1'b1 to 1'b0 to align with Training Firmware Application note

Bug fixes:
----------
- STAR 4626758: LP5/5X PIE sets MR28.ZQStop=0 before ZQLatch command in background calibration (no impact on command based calibration)

Input Changes:
--------------
- Removed user_input_advanced.RxVrefDACEnable, not used in PHYINIT
- Added user_input_advanced.RxGainCtrl for gain control

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.9x and 1.x
- Firmware:         A-2023.05


------------------------------------------------------------------------------
Version A-2023.02
February 24, 2023

Changes from version A-2022.12
(mandatory)

Enhancements:
-------------
- Added AC 1/4 data rate functionality to PHYINIT
- Added ZCalStopClk functionality to PHYINIT
- Optimized the StartDCCMClear wait time to improve performance in PHYINIT

Bug fixes:
----------
- STAR 4641050: PHYINIT incorrectly programs RL/WL/nWR values for LP5X 938MHz
- STAR 4584659: PHYINIT SW is not configuring DFIPHYUPD0 due to incorrect formatting of WRITE

Input Changes:
--------------
- Added user_input_advanced.AcQuarterDataRate to enable AC 1/4 data rate feature
- Added user_input_advanced.PHYZCalPowerSaving to enable ZCalStopClk feature

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.9x and 1.x
- Firmware:         A-2022.12


------------------------------------------------------------------------------
Version A-2022.12
December 21, 2022

Changes from version A-2022.09
(mandatory)

Enhancements:
-------------
- PHYINIT fixed arrays for MR default settings in dwc_ddrphy_phyinit_setDefault.c

Bug fixes:
----------
- STAR 4480282: Add tXSR between to move the MRW (FSP-OP) to occur after the SRX tXSR completes
- STAR 4431983: TxImpedance for CS
- STAR 4400572: Wrong MR setting in setDefault.c
- STAR 4540927: Phyinit appnote description about PclkPtrInitVal

Input Changes:
--------------
- Removed unused user_input_advanced.OnlyRestoreNonPsRegs
- Updated user_input_basic.FirstPState description, removed mention of Retention
- Added user_input_advanced.TxImpedanceCsCke to program CS/CKE impedance values

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Current Compatible Versions:
----------------------------
- PHY_TOP/PUB_TOP:  0.9x and 1.x
- Firmware:         A-2022.12


------------------------------------------------------------------------------
Version A-2022.09
Sept 9, 2022

Changes from version A-2022.05-SP1
(mandatory)

Note: This is LPDDR5X/5/4X LCA PHYINIT release

Enhancements:
-------------
- Minor code updates/improvements

Bug fixes:
----------
- PHYINIT AC Rx power down programming
- PHYINIT logging ACSM SRAM WRs to S3 list fix
- PHYINIT Missing msgBlk.UpperLowerDbyte programming

Input Changes:
--------------
- All userInput default and value lists reviewed/updated

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Minimum Required Versions:
--------------------------
- PHY_TOP/PUB_TOP:  1.10a
- Firmware:         A-2022.09


------------------------------------------------------------------------------
Version A-2022.05-SP1
July 18, 2022

Changes from version A-2022.05
(mandatory)

Note: This is LPDDR5X/5/4X LCA PHYINIT release

Enhancements:
-------------
- None 

Bug fixes:
----------
- Minor bug fixes to support GLS

Input Changes:
--------------
- user_input_sim.RxEnDlyOffset_Reserved

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Minimum Required Versions:
--------------------------
- PHY_TOP/PUB_TOP:  0.90a
- Firmware:         A-2022.05


------------------------------------------------------------------------------
Version A-2022.05
May 13, 2022

Changes from version A-2021.12
(mandatory)

Note: This is LPDDR5X/5/4X LCA PHYINIT release

Enhancements:
-------------
- DVFS

Bug fixes:
----------
- User input clean up (removed unused inputs, reviewed/updated default values)
- LP3 exit PLL relock fixed to execute 2us PLL relock time
- userInput->PmuClockDiv always set to 0 to always enable UcclkFull in PMU
- PIE disables HclkEn during mission mode
- PHYINIT code clean up (fixed unitialized variables in prints, mb1D[0] changed to mb1D[ps])

Input Changes:
--------------
- user_input_basic.EccEnable removed
- user_input_basic.NumAnib removed
- user_input_basic.Dfi1Exists removed
- user_input_basic.ComboMode removed

Firmware MessageBlock changes:
------------------------------
- See FW release notes

Limitations:
------------
- None

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Minimum Required Versions:
--------------------------
- PHY_TOP/PUB_TOP:  0.90a
- Firmware:         A-2022.05


------------------------------------------------------------------------------
Version A-2021.12
December 10, 2021

Changes from version A-2021.09
(mandatory)

Enhancements:
-------------
- ICCM/DCCM load time performance enhancements for training FW
- Code improvements

Bug fixes:
----------
- None

Input Changes:
--------------
- See below for changes with input data structures

Changes to input data structures:
- user_input_advanced.CkDisVal only support value of 0
- user_input_advanced.WDQSExt removed

Firmware MessageBlock changes:
- See FW release notes

Limitations:
------------
- No MMFW for 14-Pstate support, only 4 HW Pstate support

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2

Minimum Required Versions:
--------------------------
- PHY_TOP/PUB_TOP:  0.75a
- Firmware:         A-2021.12


------------------------------------------------------------------------------
Version A-2021.09
September 20, 2021

Changes from version N/A (Initial release)
(mandatory)

Note: This initial version of PHYINIT supports the reduced PHY functionality described in the PUB release notes

Enhancements:
-------------
- None

Bug fixes:
----------
- None

Input Changes:
--------------
- See below for changes with input data structures

Changes to input data structures:
- None

Firmware MessageBlock changes:
- None

Limitations:
------------
- No MMFW for 14-Pstate support, only 4 HW Pstate support
- Frequency change is not supported in this release

Compiler Version:
-----------------
Compiler version used during the QA testing of this release.
- gcc 4.7.2
 
Minimum Required Versions:
--------------------------
- PHY_TOP/PUB_TOP:  0.50a
- Firmware:         A-2021.09
