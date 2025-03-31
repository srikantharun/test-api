Copyright 2024 Synopsys, Inc.
This Synopsys IP and all associated documentation are proprietary to
Synopsys, Inc. and may only be used pursuant to the terms and conditions
of a written license agreement with Synopsys, Inc. All other use,
reproduction, modification, or distribution of the Synopsys IP or the
associated documentation is strictly prohibited.
Inclusivity & Diversity - Read the Synopsys Statement on Inclusivity and Diversity at 
https://solvnetplus.synopsys.com/s/article/Synopsys-Statement-on-Inclusivity-and-Diversity
------------------------------------------------------------------
LPDDR5X/5/4X PHY TRAINING FIRMWARE

Version A-2024.08
July 26, 2024

Changes from Version A-2024.05
(required)

- PMU Revision: 0x2408

Bug Fixes
---------
  STAR ID  Description                                                                                                                   
---------  ----------------------------------------------------------------------------------------------------------------------------
  5689419  Largest Empty Circle message block field shared with VREF Reuse
  5661830  Two rank systems may have non-optimal PPT2 results
  5565762  Insufficient settling time on DqRxVrefDac during RxDFE training
  5519167  LP4X Single Ended Clock mode does not follow FSP procedure with Shared Reset

Enhancements 
-------------------------------------------------------------------------------------------
- DCA step size is reduced from 3 bits down to 2 (from +/-7 down to +/-3 maximum)
- Missing MR33 - MR40 print for Channel B rank 1
- Updated DCAOpts messageblock field for clarity
- LPDDR4x FW Updated to expand additional tINIT5 spec interpretations
-------------------------------------------------------------------------------------------

Known Issues
------------
- limited verification of datarates below 533Mbps
- Vref reuse (Train2DMisc[14]) training time optimization feature missing PPT adjustments
- Pre Compute RxClk Coarse bit (Misc[5]) missing 2 rank support


Minimum Required Versions
-------------------------
- PHYINIT: A-2024.08
- PUB_TOP: 0.90*, 1.10*, 1.11*, 1.20*, 1.21*, 2.00*, 2.10*, 2.20*, 2.21*, 2.30*, 2.40*

===========================================

Version A-2024.05
May 10, 2024

Changes from Version A-2024.02
(required)

- PMU Revision: 0x2415

Bug Fixes
---------
  STAR ID  Description                                                                                          
---------  ---------------------------------------------------------------------------------------------------
  5374471  Possible incorrect CSR sweep for Rx PHY DCA training resulting in suboptimal training
  5328652  LPDDR5X Training firmware MRL calculation on systems with large "Time-of-Flight" skews between bytes of same LPDDR5x channel may be incorrect above 8533 MT/s

Enhancements
-------------------------------------------------------------------------------------------
- Align zero fill lines in .bin and .incv file and _ecc.txt for LP5X training firmware IMEM
-------------------------------------------------------------------------------------------

Known Issues
------------
- None


Minimum Required Versions
-------------------------
- PHYINIT: A-2024.05
- PUB_TOP: 0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*, 2.20*, 2.21*, 2.30*

===========================================




















Version A-2024.02
January 12, 2024

Changes from Version A-2023.10
(required)

- PMU Revision: 0x2402

Bug Fixes
---------
  STAR ID  Description                                                                
---------  -------------------------------------------------------------------------  
  5251051  Adjusting RxClk below 3200 causes DFI MRL failures                         
  5061837  [LP5X] DevInit is missing MR21 in the list of MRs                          
  4865583  Per Pin DFE may give incorrect results                                  


Known Issues
------------
- None

Enhancements
------------------------------------------------------------------------------------
- None
------------------------------------------------------------------------------------

Minimum Required Versions
-------------------------
- PHYINIT: A-2024.02
- PUB_TOP: 0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*, 2.20*, 2.21*

===========================================
A-2023.10
October 11, 2023

Changes from Version A-2023.07
(required)

- PMU Revision: 0x230a

Bug Fixes
---------
  STAR ID  Description                                                                  Status
---------  ---------------------------------------------------------------------------  --------
  5014484  Problem in cdd calculation in lpddr5/5x/4x                                   Fixed
  4913026  RX/TX DRAM DCA set to incorrect value after training                         Fixed
  4883337  RxClk1uiMinFine handled incorrectly for 1600 to 3200 datarate                Fixed
  4878880  MRLCalcAdj Negative values don't work                                        Fixed
  4865578  RX DCA Step May produce incorrect results                                    Fixed
  4645476  Misc[0] documentation wrong                                                  Fixed


Known Issues
------------
  4865583  Per Pin DFE may give incorrect results                                                               


Enhancements
-----------------------------------------------------------------------------------------------------------------
- csrAsyncDbyteTxData should be reset after CA training to drive DQSC in LPDDR4x Single-ended DQS mode
- Fixed incorrect printings during LP5 write leveling coarse training
-----------------------------------------------------------------------------------------------------------------

Minimum Required Versions
-------------------------
- PHYINIT: A-2023.10
- PUB_TOP: 0.90*, 1.10*, 1.20*, 1.21*, 2.00*, 2.10*, 2.20*

===========================================
A-2023.07
June 29, 2023

Changes from Version A-2023.05
(required)

- PMU Revision: 0x2307

Known Issues
------------
4865583 Per Pin DFE may give incorrect results
4865578 RX DCA Step May produce incorrect results


Bug Fixes
---------

  STAR ID  Description                                                                                               
---------  --------------------------------------------------------------------------------------------------------  
  4647429  [LP5X STD] Remove redundant MRW for MR51 at the end of training                                           
  4806718  LP5X_STD Training Firmware: WCK2DQO might not be saved correctly
  4843842 incorrect and redundant zcal in write_fsop1_mrs for lpddr4/4x mode for byte mode

Enhancements
------------
- Mixed mode devices is supported without dbyte swap
- Don't send ZQ calibration command  ZQ stop is set to 1 (MR28[1])


Minimum Required Versions
-------------------------
- PHYINIT: A-2023.07
- PUB_TOP: 0.90*, 1.10*, 1.20*, 1.21*, 2.00*

===========================================


A-2023.05
April 27, 2023

- PMU Revision: 0x2305

Known Issues
------------
- Mixed mode of x8/x16 devices is not supported
- 2 tap RxDFE is not supported

Bug Fixes
---------
 STAR ID        Description                                                                     Status
---------  ---------------------------------------------------------------------------------- ---------
  4637375        Incorrect non-target delay during RxDFE training                               Fixed
  4583901        [01457681] Streaming Message format contains mentions of LP54                  Fixed
  4520282        Fixed RXDCA training setting RX VREF Incorrectly                               Fixed
  4520277        Fixed RxDCA training for skewed RxClk T and C, improve tiebreaking algorithm   Fixed
  4621156        TxDfe Fixes for enabled channels, dbyte swap, and MR0/24/41 usage              Fixed
  4747560        Fixed Duty cycle distortion (DCD) list for disable ranks                       Fixed

Enhancements
------------
- Added Strobeless Mode support
- Added swizzle of DM/DBI lane support
- Enhanced DFE Gen2
- Enhance Vref Offset to train at vddq/4
- Messageblock descriptions updated for clarity 
- Deprecate LCDL based Pclk DCA
- Train lane8 if Read data copy is enabled
- Update pmu messaging related to MR12
- Add check for inconsistency between EnabledDqsChB and CsPresentChB
- Disable DxOdt during CA training
- Added shared reset support

Minimum Required Versions
-------------------------
- PHYINIT: A-2023.05
- PUB_TOP: 0.90a, 1.10a, 1.20a

===========================================

A-2022.12
December 23, 2022

- PMU Revision: 0x220c

NOTE: This release must NOT be used for production

Known Issues
------------
- RXDCA training may set RX VREF Incorrectly
- RxDCA training may not work correctly for skewed RxClk T and C
- Strobeless Mode is not supported
- LPDDR4X training needs MRLCalcAdjust=1 for some skew scenarios
- Swizzle of DM/DBI lane is not supported
- Mixed mode of x8/x16 devices is not supported
- TxDfe may not produce correct results
- RxStandby may be violated in some Skew Scenarios

Bug Fixes
---------
  Fix UserCustom Patterns 
  Fix for LPDDR4x Coarse Write Leveling with RxClk and RDC inverts enabled
  Change delay update sequence for CA training to work with newer pubs
  Don't send LPDDR5X MRS commands to LPDDR5 devices 


Enhancements
------------
None


Minimum Required Versions
-------------------------
- PHYINIT: A-2022.12
- PUB_TOP: 0.90a, 1.00a, 1.10a

===========================================
A-2022.09
September 16, 2022

- PMU Revision: 0x2209

NOTE: This release must NOT be used for production

Known Issues
------------
- CS training, CA VREF training and TxDfe training are not supported in this release.

Bug Fixes
---------
- None

Enhancements
------------
- 2D training support
- Rx Receiver Offset training and RxDFE training
- RxPHYDca (lpddr5 only), DRAM TxDCA and RxDCA (lpddr5x only)


Minimum Required Versions
-------------------------
- PHYINIT: A-2022.09
- PUB_TOP: 0.90a, 1.00a, 1.10a


============================================

A-2022.05
May 15, 2022

- PMU Revision: 0x2205

NOTE: This release must NOT be used for production

Known Issues
------------
- None

Bug Fixes
---------
- None

Enhancements
------------
- Added support for DRAM Device Initialization, Command Bus ( CA ) Training, Write Leveling training, Read Gate Enable training, Max Read Latency Training, Read Training, Write Training.
  2D training not yet supported ( Disable2D must be set to 1 ).
  SequenceCtrl = 0x121F supported.
  PHYINIT modes supported: skiptrain, devinit+skiptrain, training ( ALL ).
  Protocols supported: LPDDR5/LPDDR5X/LPDDR4X ( ALL ).

Minimum Required Versions
-------------------------
- PHYINIT: A-2022.05
- PUB_TOP: 0.80_pre1


============================================

A-2022.01-T-202479
January 15, 2022

Special Notes
-------------
- There is NO training firmware provided with this release
- The files in the firmware directory are provided to enable PHYINIT to run in skip training mode.
- This release is NOT suitable for tapeout.

Known Issues
------------
- None

Bug Fixes
---------
- None

Enhancements
------------
- None

Minimum Required Versions
-------------------------
- PHYINIT: A-2022.01-T-202479
- PUB_TOP: 0.80_pre1

