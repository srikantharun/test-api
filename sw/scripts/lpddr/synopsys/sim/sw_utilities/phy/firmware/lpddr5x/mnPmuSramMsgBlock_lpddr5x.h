typedef struct PMU_SMB_LPDDR5X_1D_t_ {
   uint8_t  Reserved00;       // Byte offset 0x00, CSR Addr 0x58000, Direction=In
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MsgMisc;          // Byte offset 0x01, CSR Addr 0x58000, Direction=In
                              // Contains various global options for training.
                              // 
                              // Bit fields:
                              // 
                              // MsgMisc[0] MTESTEnable
                              //      0x1 = Pulse primary digital test output bump at the end of each major training stage. This enables observation of training stage completion by observing the digital test output.
                              //      0x0 = Do not pulse primary digital test output bump
                              // 
                              // MsgMisc[1] SimulationOnlyReset
                              //      0x1 = Verilog only simulation option to shorten duration of DRAM reset pulse length to 1ns. 
                              //                Must never be set to 1 in silicon.
                              //      0x0 = Use reset pulse length specifed by JEDEC standard
                              // 
                              // MsgMisc[2] SimulationOnlyTraining
                              //      0x1 = Verilog only simulation option to shorten the duration of the training steps by performing fewer iterations. 
                              //                Must never be set to 1 in silicon.
                              //      0x0 = Use standard training duration.
                              // 
                              // MsgMisc[3] Disable Boot Clock 
                              //      0x1 = Disable boot frequency clock when initializing DRAM. (not recommended)
                              //      0x0 = Use Boot Frequency Clock 
                              // 
                              // MsgMisc[4] Suppress streaming messages, including assertions, regardless of HdtCtrl setting.
                              //            Stage Completion messages, as well as training completion and error messages are
                              //            Still sent depending on HdtCtrl setting.
                              // 
                              // MsgMisc[5] RFU, must be zero
                              // 
                              // MsgMisc[6] Average out WrLvl delay values
                              //      0x1 = FW calculates average of training results across both the ranks and loads this new value to delay CSRs for both ranks, i.e.
                              //            TxWckDly[db0] = (TxWckDlyTg0[db0] + TxWckDlyTg1[db0]) /2 ;
                              //            TxWckDly[db1] = (TxWckDlyTg0[db1] + TxWckDlyTg1[db1]) /2 ;
                              //      0x0 = TxWckDly delay CSR for each rank has independent value which is based on its training result (default mode)
                              // 
                              // MsgMisc[7] RFU, must be zero
                              // 
                              // Notes: 
                              // 
                              // - SimulationOnlyReset and SimulationOnlyTraining can be used to speed up simulation run times, and must never be used in real silicon. Some VIPs may have checks on DRAM reset parameters that may need to be disabled when using SimulationOnlyReset.
   uint16_t PmuRevision;      // Byte offset 0x02, CSR Addr 0x58000, Direction=Out
                              // PMU firmware revision ID
                              // After training is run, this address will contain the revision ID of the firmware
   uint8_t  Pstate;           // Byte offset 0x04, CSR Addr 0x58001, Direction=In
                              // Must be set to the target Pstate to be trained up to 15
                              //  Pstate [7] = when set will use 15 Pstate Mode DMA transfer
   uint8_t  PllBypassEn;      // Byte offset 0x05, CSR Addr 0x58001, Direction=In
                              // Set according to whether target Pstate uses PHY PLL bypass
                              //    0x0 = PHY PLL is enabled for target Pstate
                              //    0x1 = PHY PLL is bypassed for target Pstate
   uint16_t DRAMFreq;         // Byte offset 0x06, CSR Addr 0x58001, Direction=In
                              // DDR data rate for the target Pstate in units of MT/s.
                              // For example enter 0x0640 for DDR1600.
   uint8_t  DfiFreqRatio;     // Byte offset 0x08, CSR Addr 0x58002, Direction=In
                              // Frequency ratio betwen MemClk and SDRAM WCK.
                              //    0x2 = 1:2
                              //    0x4 = 1:4
   uint8_t  DcaOpts;          // Byte offset 0x09, CSR Addr 0x58002, Direction=In
                              // DcaOpts[0] Applies to Rx DCA
                              // 0: run Dram  DCA for lp5x, run Phy DCA for lp5
                              // 1: run Phy DCA
                              // DcaOpts[1] Applies to DCA using eye width training 
                              // 0: run 4UI wide scan with 2 step size
                              // 1: run 2UI wide scan with 1 step size
                              // DcaOpts[2] After DCA  using eye width training step is complete
                              // 0: run simple Rx 1D SI sequence
                              // 1: Don't run Rx 1D SI sequence
                              // DcaOpts[3] Use Phy Training instead of Dram DCM for Tx DCA
                              // 0: run JEDEC Dram DCM Training
                              // 1: run PHY largest minimum eye width training
                              // DcaOpts[4]  Applies to DCA using eye width training 
                              // 0: when running Rx Phy DCA, set TxDCACtrl to RxDcaCtrl
                              // 1: use default value for TxDCACtrl
                              // DcaOpts[6:5] DCA step value
                              // Amount that the DCA value will be incremented during Phy training. See also UseAltRxPath for LPDDR5X.
                              // DcaOpts[7] RFU
   uint16_t Train2DMisc;      // Byte offset 0x0a, CSR Addr 0x58002, Direction=In
                              // 2D Training Miscellaneous Control
                              // 
                              // Bit fields:
                              // Train2DMisc[0]: Additionally print alternate 2D eye contour format
                              //   0 = Do not print alternate eye contour  (default behavior)
                              //   1 = Print alternate eye contour
                              // 
                              // Train2DMisc[1]: Print verbose eye optimization intermediate output values
                              //   0 = Do not print verbose eye optimization intermediate output  (default behavior)
                              //   1 = Print verbose eye optimization intermediate output
                              // 
                              // Train2DMisc[5:2]: Iteration count for optimization algorithm
                              // Iteration count = Train2DMisc[5:2] << 1
                              // Iteration count == 0 is default count = 16
                              // iteration count == 2 early termination
                              // 
                              // Train2DMisc[7:6]: Number of seeds for optimization algorithm
                              // 0 = 2 seeds, left and right of center, default behavior
                              // 1 = 1 seed, center seed
                              // 2 = 2 seeds, left and right of center
                              // 3 = 3 seeds, left, center and right
                              // 
                              // Train2DMisc[8]: Print additional  eye contours for True and Complement eyes prior to optimization
                              // 0 = Do not print additional eye contours prior to optimization (default behavior)
                              // 1 = Print eye contours prior to optimization
                              // 
                              // Train2DMisc[9]: Print full eye contours (instead of half)
                              // 0 = Print half Eye Contours, only even index data (default behavior)
                              // 1 = Print Full Eye Contours, data at every index
                              // 
                              // Train2DMisc[10]: Algorithm selection for eye center search in 2D training.
                              // (LEC may provide solutions with better margins for irregularly shaped eyes.)
                              // 0 = Use weighted mean algorithm (default)
                              // 1 = Use largest empty circle algorithm (LEC)
                              // 
                              // Train2DMisc[12:11]: Weighted mean algorithm bias function.
                              // 0 = Use regular weighted mean
                              // 1 = Use weighted mean with voltage squared
                              // 2 = Use weighted mean with log2 voltage
                              // 
                              // Train2DMisc[13]: Override RxVref runtime improvement scheme
                              // 0 = runtime scheme with RxVref range set by VrefStart and Vref End
                              // 1 = runtime speed scheme with range set by number of points before and after Si Friendly trained point
                              // 
                              // Train2DMisc[14]; Reuse Rank 0 Vref
                              // 0 = Perform default read and write training
                              // 1 = Use Vref found from Rank 0 optimization for Rank 1 to improve runtime
   uint8_t  UseAltRxPath;     // Byte offset 0x0c, CSR Addr 0x58003, Direction=In
                              // Use alternate hardware to collect data on Rx Path
                              // UseAltRxPath[2:0] Select which data path to use in CA training
                              // 0x0 = Default, Use AsyncDbyteRxData
                              // 0x1 = Use Dtsm
                              // 0x2 = Use RxFifoContents
                              // Others, RFU
                              // UseAltRxPath[5:3] Select which data path to use in WrLvl training
                              // 0x0 = Use Dtsm and training Counters
                              // 0x1 = Use RxFifoContents
                              // Others, RFU
                              // UseAltRxPath[6] Select RX DRAM DCA sampling method (LP5X only)
                              // 0x0 = Default, use data collection, read DQ feedback
                              // 0x1 = Evaluate duty cycle using RxEnDly, sample RDQS only
   uint8_t  Misc;             // Byte offset 0x0d, CSR Addr 0x58003, Direction=In
                              // Lp4/5 specific options for training.
                              // 
                              // Bit fields:
                              // 
                              // Misc[0] Enable dfi_reset_n
                              // 0 : (Recommended) PHY internal registers control BP_MEMRESET_L pin until end of training. 
                              //   See PUB databook for requirement of dfi_reset_n control by MC before 1st dfi_init_start sequence.
                              // 1 : Enables dfi_reset_n to control BP_MEMRESET_L pin during training. 
                              //   To ensure that no glitches occur on BP_MEMRESET at the end of training, 
                              //   The MC must drive dfi_reset_n=1'b1 prior to starting training and keep its value until the end of training.
                              // Misc[1] use a shared reset between multiple PHYs and the DRAM devices.
                              // 0 : default
                              // 1 : Use Shared Reset mode
                              // Misc[2] unused
                              // Misc[3] Enable 4UI Si Friendly Scan
                              // 0: 4UI scan
                              // 1: 2UI scan
                              // Misc[4] PRBS Read training seeding
                              // 0: Use si friendly trained result
                              // 1: Use RxReplica Estimate
                              //  Misc[5] Pre Compute RxClk Coarse bit
                              //  0: compute RxClk coarse bit after generating both sets of eyes
                              //  1: estimate RxClk Coarse bit before RxClk training
                              //  Misc[6] Single RxClk scan in SI Friendly Read
                              //  0: Run both RxClkT and RxClkC scan
                              //  1: Run only RxClkT scan  
                              // Misc[7] RFU, must be zero
   int8_t   SIFriendlyDlyOffset; // Byte offset 0x0e, CSR Addr 0x58003, Direction=In
                              // SI Friendly Delay Offset
                              // SIFriendlyDlyOffset[7:1]
                              // This field can be used to modify the trained delay of an eye to be equal to an offset from the edge of that eye for the trained value of the voltage. This can be useful when performing SI friendly 2D training and encountering eye collapse in later training.
                              // SIFriendlyDlyOffset[7:1] = 0  Disable this mechanism
                              // SIFriendlyDlyOffset[7:1] > 0  Add offset to delay left edge of eye
                              // SIFriendlyDlyOffset[7:1] < 0 Subtract offset from delay right edge of eye
                              // 
                              // TruncV
                              // SIFriendlyDlyOffset[0]
                              //    0 = 2D Normal optimization. Treat any point outside of tested eye rectangle as failing.
                              //    1 = If eye is truncated at low voltages treat points at voltages lower than the minimum tested voltage as passing. The trained point will always be at a voltage above the minimum tested voltage.
   uint8_t  CsTestFail;       // Byte offset 0x0f, CSR Addr 0x58003, Direction=Out
                              // This field will be set if training fails on any rank.
                              //    0x0 = No failures
                              //    non-zero = one or more ranks failed training
   uint16_t SequenceCtrl;     // Byte offset 0x10, CSR Addr 0x58004, Direction=In
                              // Controls the training steps to be run. Each bit corresponds to a training step. 
                              // 
                              // If the bit is set to 1, the training step will run. 
                              // If the bit is set to 0, the training step will be skipped.
                              // 
                              // Training step to bit mapping:
                              //    SequenceCtrl[0] = Run DevInit - Device/phy initialization. Should always be set.
                              //    SequenceCtrl[1] = Run WrLvl - Write leveling
                              //    SequenceCtrl[2] = Run RxEn - Read gate training
                              //    SequenceCtrl[3] = Run RdDQS - read dqs training
                              //    SequenceCtrl[4] = Run WrDq - write dq training
                              //    SequenceCtrl[5] = RFU, must be zero
                              //    SequenceCtrl[6] = Run DRAM DCA - Dram duty cycle adjustment
                              //    SequenceCtrl[7] = Run PHY RdDCA - PHY read duty cycle adjustment
                              //    SequenceCtrl[8] = RFU, must be zero
                              //    SequenceCtrl[9] = Run MxRdLat - Max read latency training
                              //    SequenceCtrl[10] = Run TxDFE - DRAM Tx DFE
                              //    SequenceCtrl[11] = RFU, must be zero
                              //    SequenceCtrl[12] = Run LPCA - CA Training
                              //    SequenceCtrl[13] = RFU, must be zero
                              //    SequenceCtrl[14] = Run RxRcvr training
                              //    SequenceCtrl[15] = RFU, must be zero
   uint8_t  HdtCtrl;          // Byte offset 0x12, CSR Addr 0x58004, Direction=In
                              // To control the total number of debug messages, a verbosity subfield (HdtCtrl, Hardware Debug Trace Control) exists in the message block. Every message has a verbosity level associated with it, and as the HdtCtrl value is increased, less important s messages stop being sent through the mailboxes. The meanings of several major HdtCtrl thresholds are explained below:
                              // 
                              //    0x05 = Detailed debug messages (e.g. Eye delays)
                              //    0x0A = Coarse debug messages (e.g. rank information)
                              //    0xC8 = Stage completion
                              //    0xC9 = Assertion messages
                              //    0xFF = Firmware completion messages only
                              // 
                              // See Training App Note for more detailed information on what messages are included for each threshold.
                              // 
   uint8_t  Reserved13;       // Byte offset 0x13, CSR Addr 0x58004, Direction=In
                              // This field is reserved and must be programmed to 0x00.
   uint16_t InternalStatus;   // Byte offset 0x14, CSR Addr 0x58005, Direction=Out
                              // RFU
   uint8_t  DFIMRLMargin;     // Byte offset 0x16, CSR Addr 0x58005, Direction=In
                              // Margin added to smallest passing trained DFI Max Read Latency value, in units of DFI clocks. Recommended to be >= 1. See the Training App Note for more details on the training process and the use of this value.
                              // 
                              // This margin must include the maximum positive drift expected in tDQSCK over the target temperature and voltage range of the users system.
   uint8_t  TX2D_Delay_Weight; // Byte offset 0x17, CSR Addr 0x58005, Direction=In
                              // [0-4] 0 ... 31
                              // During TX 2D training with Largest Empty Circle when finding an eye center the delay and voltage components are weighed such that the combined margin is delay margin * TX_Delay_Weight2D + voltage margin * TX_Voltage_Weight2D. Either weight may be zero but if both are zero each weight is taken to have a value of one.
   uint8_t  TX2D_Voltage_Weight; // Byte offset 0x18, CSR Addr 0x58006, Direction=In
                              // [0-4] 0 ... 31
                              // During TX 2D training with Largest Empty Circle when finding an eye center the delay and voltage components are weighed such that the combined margin is delay margin * TX_Delay_Weight2D + voltage margin * TX_Voltage_Weight2D. Either weight may be zero but if both are zero each weight is taken to have a value of one.
   uint8_t  Quickboot;        // Byte offset 0x19, CSR Addr 0x58006, Direction=In
                              // Enable Quickboot.
   uint8_t  CaTrainAltUpdate; // Byte offset 0x1a, CSR Addr 0x58006, Direction=In
                              // Enable alternate update of delays in CA training.
   uint8_t  CATrainOpt;       // Byte offset 0x1b, CSR Addr 0x58006, Direction=In
                              // CA training option bit field
                              // [0] CA VREF Training
                              //        1 = Enable CA VREF Training
                              //        0 = Disable CA VREF Training
                              // [1] LP5 CS training
                              //        1 = Enable LP5 CS Training
                              //        0 = Disable LP5 CS Training
                              //      This bit is don't care for LP4 training
                              // [2] RFU must be zero
                              // [3] Delayed clock feature
                              //        0 = Use delayed clock
                              //        1 = Use normal clock
                              //  [4-7] Value by which ACTxDly is to be incremented during CA/CS training:
                              //       If bit 7 is set, delay is incremented by 8,
                              //       If bit 6 is set, delay is incremented by 4,
                              //       if bit 5 is set, delay is incremented by 2
                              //       else delay is incremented by 1
                              //       This helps in reducing test run time during simulations. For silicon, it is recommended to increment delay by steps of 1 only
   uint8_t  X8Mode;           // Byte offset 0x1c, CSR Addr 0x58007, Direction=In
                              // X8Mode is encoded as a bit field for channel and rank. 
                              // Bit = 0 means x16 devices are connected. 
                              // Bit = 1 means 2 x8 devices are connected. 
                              // This field should be treated as if you have a  2 channel system. Valid Settings are  0xf/0xa/0x0.
                              // X8Mode [0] - Channel A Rank 0
                              // X8Mode [1] - Channel A Rank 1
                              // X8Mode [2] - Channel B Rank 0
                              // X8Mode [3] - Channel B Rank 1
   uint8_t  RX2D_TrainOpt;    // Byte offset 0x1d, CSR Addr 0x58007, Direction=In
                              // RX2D_TrainOpt
                              // [0] EnableVrefDfeFiltering
                              //    0 = don't filter based on vref
                              //    1 = filter based on vref when DFE is enabled
   uint8_t  TX2D_TrainOpt;    // Byte offset 0x1e, CSR Addr 0x58007, Direction=In
                              // TX2D_TrainOpt
                              // [0] IncreasedHardwareWrScanRange,
                              // 0 = Use default hardware Write Training scan range
                              // 1 = Increase Write Training Hardware Scan range. If Hardware Scans are not enabled, this had no effect.
                              // [1] WriteEstimatePreScan
                              // 0 = Estimate software Write training range with DRAM WCK/DQS oscillator
                              // 1 = Run a coarse hardware Write training to estimate scan range for Software scans
   uint8_t  RxDFEOpt;         // Byte offset 0x1f, CSR Addr 0x58007, Direction=In
                              // RxDFE options
                              // [0]  Skip RxClkT eye gathering for brute force algorithm
                              // [1]  Perform negative tap scans for brute force algorithm
                              // [2]  Skip RxClkC eye gathering for brute force algorithm
                              // [3]  Run 1D RxClk Scan if SkipRxClkRetrain is not set
                              // [5:4] Selection criteria for brute force algorithm
                              //     0x0: use total eye area
                              //     0x1: use Vref margin at trained position
                              //     0X2: use eye height at trained delay value
                              // [6] RFU
                              // [7] Enable Brute Force DFE training algorithm
   uint8_t  RX2D_Delay_Weight; // Byte offset 0x20, CSR Addr 0x58008, Direction=In
                              // [0-4] 0 ... 31
                              // During RX 2D training with Largest Empty Circle when finding an eye center the delay and voltage components are weighed such that the combined margin is delay margin * RX_Delay_Weight2D + voltage margin * RX_Voltage_Weight2D. Either weight may be zero but if both are zero each weight is taken to have a value of one.
   uint8_t  RX2D_Voltage_Weight; // Byte offset 0x21, CSR Addr 0x58008, Direction=In
                              // [0-4] 0 ... 31
                              // During RX 2D training with Largest Empty Circle when finding an eye center the delay and voltage components are weighed such that the combined margin is delay margin * RX_Delay_Weight2D + voltage margin * RX_Voltage_Weight2D. Either weight may be zero but if both are zero each weight is taken to have a value of one.
   uint16_t PhyConfigOverride; // Byte offset 0x22, CSR Addr 0x58008, Direction=In
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  EnabledDQsChA;    // Byte offset 0x24, CSR Addr 0x58009, Direction=In
                              // Total number of DQ bits enabled in PHY Channel A
   uint8_t  CsPresentChA;     // Byte offset 0x25, CSR Addr 0x58009, Direction=In
                              // Indicates presence of DRAM at each chip select for PHY channel A.
                              // 
                              //  0x1 = CS0 is populated with DRAM
                              //  0x3 = CS0 and CS1 are populated with DRAM
                              // 
                              // All other encodings are illegal
                              //  
   int8_t   CDD_ChA_RR_1_0;   // Byte offset 0x26, CSR Addr 0x58009, Direction=Out
                              // This is a signed integer value.
                              // Read to read critical delay difference from cs 1 to cs 0 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_RR_0_1;   // Byte offset 0x27, CSR Addr 0x58009, Direction=Out
                              // This is a signed integer value.
                              // Read to read critical delay difference from cs 0 to cs 1 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_RW_1_1;   // Byte offset 0x28, CSR Addr 0x5800a, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs 1 to cs 1 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_RW_1_0;   // Byte offset 0x29, CSR Addr 0x5800a, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs 1 to cs 0 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_RW_0_1;   // Byte offset 0x2a, CSR Addr 0x5800a, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs 0 to cs 1 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_RW_0_0;   // Byte offset 0x2b, CSR Addr 0x5800a, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs0 to cs 0 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_WR_1_1;   // Byte offset 0x2c, CSR Addr 0x5800b, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 1 to cs 1 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_WR_1_0;   // Byte offset 0x2d, CSR Addr 0x5800b, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 1 to cs 0 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_WR_0_1;   // Byte offset 0x2e, CSR Addr 0x5800b, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 0 to cs 1 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_WR_0_0;   // Byte offset 0x2f, CSR Addr 0x5800b, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 0 to cs 0 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_WW_1_0;   // Byte offset 0x30, CSR Addr 0x5800c, Direction=Out
                              // This is a signed integer value.
                              // Write  to write critical delay difference from cs 1 to cs 0 on Channel A
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChA_WW_0_1;   // Byte offset 0x31, CSR Addr 0x5800c, Direction=Out
                              // This is a signed integer value.
                              // Write  to write critical delay difference from cs 0 to cs 1 on Channel A
                              // See PUB Databook for details on use of CDD values.
   uint8_t  CATerminatingRankChA; // Byte offset 0x32, CSR Addr 0x5800c, Direction=In
                              // Terminating Rank for CA bus on Channel A
                              //    0x0 = Rank 0 is terminating rank
                              //    0x1 = Rank 1 is terminating rank
   uint8_t  TrainedVREFCA_A0; // Byte offset 0x33, CSR Addr 0x5800c, Direction=Out
                              // Trained CA Vref setting for Ch A Rank 0
   uint8_t  TrainedVREFCA_A1; // Byte offset 0x34, CSR Addr 0x5800d, Direction=Out
                              // Trained CA Vref setting for Ch A Rank 1
   uint8_t  TrainedVREFDQ_A0; // Byte offset 0x35, CSR Addr 0x5800d, Direction=Out
                              // Trained DQ Vref setting for Ch A Rank 0
   uint8_t  TrainedVREFDQ_A1; // Byte offset 0x36, CSR Addr 0x5800d, Direction=Out
                              // Trained DQ Vref setting for Ch A Rank 1
   uint8_t  RxClkDly_Margin_A0; // Byte offset 0x37, CSR Addr 0x5800d, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  VrefDac_Margin_A0; // Byte offset 0x38, CSR Addr 0x5800e, Direction=Out
                              // Distance from the trained center to the closest failing region in phy DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  TxDqDly_Margin_A0; // Byte offset 0x39, CSR Addr 0x5800e, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DeviceVref_Margin_A0; // Byte offset 0x3a, CSR Addr 0x5800e, Direction=Out
                              // Distance from the trained center to the closest failing region in device DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  RxClkDly_Margin_A1; // Byte offset 0x3b, CSR Addr 0x5800e, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  VrefDac_Margin_A1; // Byte offset 0x3c, CSR Addr 0x5800f, Direction=Out
                              // Distance from the trained center to the closest failing region in phy DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  TxDqDly_Margin_A1; // Byte offset 0x3d, CSR Addr 0x5800f, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DeviceVref_Margin_A1; // Byte offset 0x3e, CSR Addr 0x5800f, Direction=Out
                              // Distance from the trained center to the closest failing region in device DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  EnabledDQsChB;    // Byte offset 0x3f, CSR Addr 0x5800f, Direction=In
                              // Total number of DQ bits enabled in PHY Channel B
   uint8_t  CsPresentChB;     // Byte offset 0x40, CSR Addr 0x58010, Direction=In
                              // Indicates presence of DRAM at each chip select for PHY channel B.
                              // 
                              //    0x0 = No chip selects are populated with DRAM
                              //    0x1 = CS0 is populated with DRAM
                              //    0x3 = CS0 and CS1 are populated with DRAM
                              // 
                              // All other encodings are illegal
                              //  
   int8_t   CDD_ChB_RR_1_0;   // Byte offset 0x41, CSR Addr 0x58010, Direction=Out
                              // This is a signed integer value.
                              // Read to read critical delay difference from cs 1 to cs 0 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_RR_0_1;   // Byte offset 0x42, CSR Addr 0x58010, Direction=Out
                              // This is a signed integer value.
                              // Read to read critical delay difference from cs 0 to cs 1 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_RW_1_1;   // Byte offset 0x43, CSR Addr 0x58010, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs 1 to cs 1 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_RW_1_0;   // Byte offset 0x44, CSR Addr 0x58011, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs 1 to cs 0 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_RW_0_1;   // Byte offset 0x45, CSR Addr 0x58011, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs 0 to cs 1 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_RW_0_0;   // Byte offset 0x46, CSR Addr 0x58011, Direction=Out
                              // This is a signed integer value.
                              // Read to write critical delay difference from cs01 to cs 0 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_WR_1_1;   // Byte offset 0x47, CSR Addr 0x58011, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 1 to cs 1 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_WR_1_0;   // Byte offset 0x48, CSR Addr 0x58012, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 1 to cs 0 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_WR_0_1;   // Byte offset 0x49, CSR Addr 0x58012, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 0 to cs 1 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_WR_0_0;   // Byte offset 0x4a, CSR Addr 0x58012, Direction=Out
                              // This is a signed integer value.
                              // Write  to read critical delay difference from cs 0 to cs 0 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_WW_1_0;   // Byte offset 0x4b, CSR Addr 0x58012, Direction=Out
                              // This is a signed integer value.
                              // Write  to write critical delay difference from cs 1 to cs 0 on Channel B
                              // See PUB Databook for details on use of CDD values.
   int8_t   CDD_ChB_WW_0_1;   // Byte offset 0x4c, CSR Addr 0x58013, Direction=Out
                              // This is a signed integer value.
                              // Write  to write critical delay difference from cs 0 to cs 1 on Channel B
                              // See PUB Databook for details on use of CDD values.
   uint8_t  CATerminatingRankChB; // Byte offset 0x4d, CSR Addr 0x58013, Direction=In
                              // Terminating Rank for CA bus on Channel B
                              //    0x0 = Rank 0 is terminating rank
                              //    0x1 = Rank 1 is terminating rank
   uint8_t  TrainedVREFCA_B0; // Byte offset 0x4e, CSR Addr 0x58013, Direction=Out
                              // Trained CA Vref setting for Ch B Rank 0
   uint8_t  TrainedVREFCA_B1; // Byte offset 0x4f, CSR Addr 0x58013, Direction=Out
                              // Trained CA Vref setting for Ch B Rank 1
   uint8_t  TrainedVREFDQ_B0; // Byte offset 0x50, CSR Addr 0x58014, Direction=Out
                              // Trained DQ Vref setting for Ch B Rank 0
   uint8_t  TrainedVREFDQ_B1; // Byte offset 0x51, CSR Addr 0x58014, Direction=Out
                              // Trained DQ Vref setting for Ch B Rank 1
   uint8_t  RxClkDly_Margin_B0; // Byte offset 0x52, CSR Addr 0x58014, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  VrefDac_Margin_B0; // Byte offset 0x53, CSR Addr 0x58014, Direction=Out
                              // Distance from the trained center to the closest failing region in phy DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  TxDqDly_Margin_B0; // Byte offset 0x54, CSR Addr 0x58015, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DeviceVref_Margin_B0; // Byte offset 0x55, CSR Addr 0x58015, Direction=Out
                              // Distance from the trained center to the closest failing region in device DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  RxClkDly_Margin_B1; // Byte offset 0x56, CSR Addr 0x58015, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  VrefDac_Margin_B1; // Byte offset 0x57, CSR Addr 0x58015, Direction=Out
                              // Distance from the trained center to the closest failing region in phy DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  TxDqDly_Margin_B1; // Byte offset 0x58, CSR Addr 0x58016, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DeviceVref_Margin_B1; // Byte offset 0x59, CSR Addr 0x58016, Direction=Out
                              // Distance from the trained center to the closest failing region in device DAC steps. This value is the minimum of all eyes in this timing group.
   uint8_t  MR1_A0;           // Byte offset 0x5a, CSR Addr 0x58016, Direction=in
                              // Value to be programmed in DRAM Mode Register 1 {Channel A, Rank 0}
   uint8_t  MR1_A1;           // Byte offset 0x5b, CSR Addr 0x58016, Direction=in
                              // Value to be programmed in DRAM Mode Register 1 {Channel A, Rank 1}
   uint8_t  MR1_B0;           // Byte offset 0x5c, CSR Addr 0x58017, Direction=in
                              // Value to be programmed in DRAM Mode Register 1 {Channel B, Rank 0}
   uint8_t  MR1_B1;           // Byte offset 0x5d, CSR Addr 0x58017, Direction=in
                              // Value to be programmed in DRAM Mode Register 1 {Channel B, Rank 1}
   uint8_t  MR2_A0;           // Byte offset 0x5e, CSR Addr 0x58017, Direction=in
                              // Value to be programmed in DRAM Mode Register 2 {Channel A, Rank 0}
   uint8_t  MR2_A1;           // Byte offset 0x5f, CSR Addr 0x58017, Direction=in
                              // Value to be programmed in DRAM Mode Register 2 {Channel A, Rank 1}
   uint8_t  MR2_B0;           // Byte offset 0x60, CSR Addr 0x58018, Direction=in
                              // Value to be programmed in DRAM Mode Register 2 {Channel B, Rank 0}
   uint8_t  MR2_B1;           // Byte offset 0x61, CSR Addr 0x58018, Direction=in
                              // Value to be programmed in DRAM Mode Register 2 {Channel B, Rank 1}
   uint8_t  MR3_A0;           // Byte offset 0x62, CSR Addr 0x58018, Direction=in
                              // Value to be programmed in DRAM Mode Register 3 {Channel A, Rank 0}
   uint8_t  MR3_A1;           // Byte offset 0x63, CSR Addr 0x58018, Direction=in
                              // Value to be programmed in DRAM Mode Register 3 {Channel A, Rank 1}
   uint8_t  MR3_B0;           // Byte offset 0x64, CSR Addr 0x58019, Direction=in
                              // Value to be programmed in DRAM Mode Register 3 {Channel B, Rank 0}
   uint8_t  MR3_B1;           // Byte offset 0x65, CSR Addr 0x58019, Direction=in
                              // Value to be programmed in DRAM Mode Register 3 {Channel B, Rank 1}
   uint8_t  MR10_A0;          // Byte offset 0x66, CSR Addr 0x58019, Direction=in
                              // Value to be programmed in DRAM Mode Register 10 {Channel A, Rank 0}
   uint8_t  MR10_A1;          // Byte offset 0x67, CSR Addr 0x58019, Direction=in
                              // Value to be programmed in DRAM Mode Register 10 {Channel A, Rank 1}
   uint8_t  MR10_B0;          // Byte offset 0x68, CSR Addr 0x5801a, Direction=in
                              // Value to be programmed in DRAM Mode Register 10 {Channel B, Rank 0}
   uint8_t  MR10_B1;          // Byte offset 0x69, CSR Addr 0x5801a, Direction=in
                              // Value to be programmed in DRAM Mode Register 10 {Channel B, Rank 1}
   uint8_t  MR11_A0;          // Byte offset 0x6a, CSR Addr 0x5801a, Direction=in
                              // Value to be programmed in DRAM Mode Register 11 {Channel A, Rank 0}
   uint8_t  MR11_A1;          // Byte offset 0x6b, CSR Addr 0x5801a, Direction=in
                              // Value to be programmed in DRAM Mode Register 11 {Channel A, Rank 1}
   uint8_t  MR11_B0;          // Byte offset 0x6c, CSR Addr 0x5801b, Direction=in
                              // Value to be programmed in DRAM Mode Register 11 {Channel B, Rank 0}
   uint8_t  MR11_B1;          // Byte offset 0x6d, CSR Addr 0x5801b, Direction=in
                              // Value to be programmed in DRAM Mode Register 11 {Channel B, Rank 1}
   uint8_t  MR12_A0;          // Byte offset 0x6e, CSR Addr 0x5801b, Direction=in
                              // Value to be programmed in DRAM Mode Register 12 {Channel A, Rank 0}
   uint8_t  MR12_A1;          // Byte offset 0x6f, CSR Addr 0x5801b, Direction=in
                              // Value to be programmed in DRAM Mode Register 12 {Channel A, Rank 1}
   uint8_t  MR12_B0;          // Byte offset 0x70, CSR Addr 0x5801c, Direction=in
                              // Value to be programmed in DRAM Mode Register 12 {Channel B, Rank 0}
   uint8_t  MR12_B1;          // Byte offset 0x71, CSR Addr 0x5801c, Direction=in
                              // Value to be programmed in DRAM Mode Register 12 {Channel B, Rank 1}
   uint8_t  MR13_A0;          // Byte offset 0x72, CSR Addr 0x5801c, Direction=in
                              // Value to be programmed in DRAM Mode Register 13 {Channel A, Rank 0}
   uint8_t  MR13_A1;          // Byte offset 0x73, CSR Addr 0x5801c, Direction=in
                              // Value to be programmed in DRAM Mode Register 13 {Channel A, Rank 1}
   uint8_t  MR13_B0;          // Byte offset 0x74, CSR Addr 0x5801d, Direction=in
                              // Value to be programmed in DRAM Mode Register 13 {Channel B, Rank 0}
   uint8_t  MR13_B1;          // Byte offset 0x75, CSR Addr 0x5801d, Direction=in
                              // Value to be programmed in DRAM Mode Register 13 {Channel B, Rank 1}
   uint8_t  MR14_A0;          // Byte offset 0x76, CSR Addr 0x5801d, Direction=in
                              // Value to be programmed in DRAM Mode Register 14 {Channel A, Rank 0}
   uint8_t  MR14_A1;          // Byte offset 0x77, CSR Addr 0x5801d, Direction=in
                              // Value to be programmed in DRAM Mode Register 14 {Channel A, Rank 1}
   uint8_t  MR14_B0;          // Byte offset 0x78, CSR Addr 0x5801e, Direction=in
                              // Value to be programmed in DRAM Mode Register 14 {Channel B, Rank 0}
   uint8_t  MR14_B1;          // Byte offset 0x79, CSR Addr 0x5801e, Direction=in
                              // Value to be programmed in DRAM Mode Register 14 {Channel B, Rank 1}
   uint8_t  MR15_A0;          // Byte offset 0x7a, CSR Addr 0x5801e, Direction=in
                              // Value to be programmed in DRAM Mode Register 15 {Channel A, Rank 0}
   uint8_t  MR15_A1;          // Byte offset 0x7b, CSR Addr 0x5801e, Direction=in
                              // Value to be programmed in DRAM Mode Register 15 {Channel A, Rank 1}
   uint8_t  MR15_B0;          // Byte offset 0x7c, CSR Addr 0x5801f, Direction=in
                              // Value to be programmed in DRAM Mode Register 15 {Channel B, Rank 0}
   uint8_t  MR15_B1;          // Byte offset 0x7d, CSR Addr 0x5801f, Direction=in
                              // Value to be programmed in DRAM Mode Register 15 {Channel B, Rank 1}
   uint8_t  MR16_A0;          // Byte offset 0x7e, CSR Addr 0x5801f, Direction=in
                              // Value to be programmed in DRAM Mode Register 16 {Channel A, Rank 0}
   uint8_t  MR16_A1;          // Byte offset 0x7f, CSR Addr 0x5801f, Direction=in
                              // Value to be programmed in DRAM Mode Register 16 {Channel A, Rank 1}
   uint8_t  MR16_B0;          // Byte offset 0x80, CSR Addr 0x58020, Direction=in
                              // Value to be programmed in DRAM Mode Register 16 {Channel B, Rank 0}
   uint8_t  MR16_B1;          // Byte offset 0x81, CSR Addr 0x58020, Direction=in
                              // Value to be programmed in DRAM Mode Register 16 {Channel B, Rank 1}
   uint8_t  MR17_A0;          // Byte offset 0x82, CSR Addr 0x58020, Direction=in
                              // Value to be programmed in DRAM Mode Register 17 {Channel A, Rank 0}
   uint8_t  MR17_A1;          // Byte offset 0x83, CSR Addr 0x58020, Direction=in
                              // Value to be programmed in DRAM Mode Register 17 {Channel A, Rank 1}
   uint8_t  MR17_B0;          // Byte offset 0x84, CSR Addr 0x58021, Direction=in
                              // Value to be programmed in DRAM Mode Register 17 {Channel B, Rank 0}
   uint8_t  MR17_B1;          // Byte offset 0x85, CSR Addr 0x58021, Direction=in
                              // Value to be programmed in DRAM Mode Register 17 {Channel B, Rank 1}
   uint8_t  MR18_A0;          // Byte offset 0x86, CSR Addr 0x58021, Direction=in
                              // Value to be programmed in DRAM Mode Register 18 {Channel A, Rank 0}
   uint8_t  MR18_A1;          // Byte offset 0x87, CSR Addr 0x58021, Direction=in
                              // Value to be programmed in DRAM Mode Register 18 {Channel A, Rank 1}
   uint8_t  MR18_B0;          // Byte offset 0x88, CSR Addr 0x58022, Direction=in
                              // Value to be programmed in DRAM Mode Register 18 {Channel B, Rank 0}
   uint8_t  MR18_B1;          // Byte offset 0x89, CSR Addr 0x58022, Direction=in
                              // Value to be programmed in DRAM Mode Register 18 {Channel B, Rank 1}
   uint8_t  MR19_A0;          // Byte offset 0x8a, CSR Addr 0x58022, Direction=in
                              // Value to be programmed in DRAM Mode Register 19 {Channel A, Rank 0}
   uint8_t  MR19_A1;          // Byte offset 0x8b, CSR Addr 0x58022, Direction=in
                              // Value to be programmed in DRAM Mode Register 19 {Channel A, Rank 1}
   uint8_t  MR19_B0;          // Byte offset 0x8c, CSR Addr 0x58023, Direction=in
                              // Value to be programmed in DRAM Mode Register 19 {Channel B, Rank 0}
   uint8_t  MR19_B1;          // Byte offset 0x8d, CSR Addr 0x58023, Direction=in
                              // Value to be programmed in DRAM Mode Register 19 {Channel B, Rank 1}
   uint8_t  MR20_A0;          // Byte offset 0x8e, CSR Addr 0x58023, Direction=in
                              // Value to be programmed in DRAM Mode Register 20 {Channel A, Rank 0}
   uint8_t  MR20_A1;          // Byte offset 0x8f, CSR Addr 0x58023, Direction=in
                              // Value to be programmed in DRAM Mode Register 20 {Channel A, Rank 1}
   uint8_t  MR20_B0;          // Byte offset 0x90, CSR Addr 0x58024, Direction=in
                              // Value to be programmed in DRAM Mode Register 20 {Channel B, Rank 0}
   uint8_t  MR20_B1;          // Byte offset 0x91, CSR Addr 0x58024, Direction=in
                              // Value to be programmed in DRAM Mode Register 20 {Channel B, Rank 1}
   uint8_t  MR21_A0;          // Byte offset 0x92, CSR Addr 0x58024, Direction=in
                              // Value to be programmed in DRAM Mode Register 21 {Channel A, Rank 0}
   uint8_t  MR21_A1;          // Byte offset 0x93, CSR Addr 0x58024, Direction=in
                              // Value to be programmed in DRAM Mode Register 21 {Channel A, Rank 1}
   uint8_t  MR21_B0;          // Byte offset 0x94, CSR Addr 0x58025, Direction=in
                              // Value to be programmed in DRAM Mode Register 21 {Channel B, Rank 0}
   uint8_t  MR21_B1;          // Byte offset 0x95, CSR Addr 0x58025, Direction=in
                              // Value to be programmed in DRAM Mode Register 21 {Channel B, Rank 1}
   uint8_t  MR22_A0;          // Byte offset 0x96, CSR Addr 0x58025, Direction=in
                              // Value to be programmed in DRAM Mode Register 22 {Channel A, Rank 0}
   uint8_t  MR22_A1;          // Byte offset 0x97, CSR Addr 0x58025, Direction=in
                              // Value to be programmed in DRAM Mode Register 22 {Channel A, Rank 1}
   uint8_t  MR22_B0;          // Byte offset 0x98, CSR Addr 0x58026, Direction=in
                              // Value to be programmed in DRAM Mode Register 22 {Channel B, Rank 0}
   uint8_t  MR22_B1;          // Byte offset 0x99, CSR Addr 0x58026, Direction=in
                              // Value to be programmed in DRAM Mode Register 22 {Channel B, Rank 1}
   uint8_t  MR24_A0;          // Byte offset 0x9a, CSR Addr 0x58026, Direction=in
                              // Value to be programmed in DRAM Mode Register 24 {Channel A, Rank 0}
   uint8_t  MR24_A1;          // Byte offset 0x9b, CSR Addr 0x58026, Direction=in
                              // Value to be programmed in DRAM Mode Register 24 {Channel A, Rank 1}
   uint8_t  MR24_B0;          // Byte offset 0x9c, CSR Addr 0x58027, Direction=in
                              // Value to be programmed in DRAM Mode Register 24 {Channel B, Rank 0}
   uint8_t  MR24_B1;          // Byte offset 0x9d, CSR Addr 0x58027, Direction=in
                              // Value to be programmed in DRAM Mode Register 24 {Channel B, Rank 1}
   uint8_t  MR25_A0;          // Byte offset 0x9e, CSR Addr 0x58027, Direction=in
                              // Value to be programmed in DRAM Mode Register 25 {Channel A, Rank 0}
   uint8_t  MR25_A1;          // Byte offset 0x9f, CSR Addr 0x58027, Direction=in
                              // Value to be programmed in DRAM Mode Register 25 {Channel A, Rank 1}
   uint8_t  MR25_B0;          // Byte offset 0xa0, CSR Addr 0x58028, Direction=in
                              // Value to be programmed in DRAM Mode Register 25 {Channel B, Rank 0}
   uint8_t  MR25_B1;          // Byte offset 0xa1, CSR Addr 0x58028, Direction=in
                              // Value to be programmed in DRAM Mode Register 25 {Channel B, Rank 1}
   uint8_t  MR26_A0;          // Byte offset 0xa2, CSR Addr 0x58028, Direction=in
                              // Value to be programmed in DRAM Mode Register 26 {Channel A, Rank 0}
   uint8_t  MR26_A1;          // Byte offset 0xa3, CSR Addr 0x58028, Direction=in
                              // Value to be programmed in DRAM Mode Register 26 {Channel A, Rank 1}
   uint8_t  MR26_B0;          // Byte offset 0xa4, CSR Addr 0x58029, Direction=in
                              // Value to be programmed in DRAM Mode Register 26 {Channel B, Rank 0}
   uint8_t  MR26_B1;          // Byte offset 0xa5, CSR Addr 0x58029, Direction=in
                              // Value to be programmed in DRAM Mode Register 26 {Channel B, Rank 1}
   uint8_t  MR27_A0;          // Byte offset 0xa6, CSR Addr 0x58029, Direction=in
                              // Value to be programmed in DRAM Mode Register 27 {Channel A, Rank 0}
   uint8_t  MR27_A1;          // Byte offset 0xa7, CSR Addr 0x58029, Direction=in
                              // Value to be programmed in DRAM Mode Register 27 {Channel A, Rank 1}
   uint8_t  MR27_B0;          // Byte offset 0xa8, CSR Addr 0x5802a, Direction=in
                              // Value to be programmed in DRAM Mode Register 27 {Channel B, Rank 0}
   uint8_t  MR27_B1;          // Byte offset 0xa9, CSR Addr 0x5802a, Direction=in
                              // Value to be programmed in DRAM Mode Register 27 {Channel B, Rank 1}
   uint8_t  MR28_A0;          // Byte offset 0xaa, CSR Addr 0x5802a, Direction=in
                              // Value to be programmed in DRAM Mode Register 28 {Channel A, Rank 0}
   uint8_t  MR28_A1;          // Byte offset 0xab, CSR Addr 0x5802a, Direction=in
                              // Value to be programmed in DRAM Mode Register 28 {Channel A, Rank 1}
   uint8_t  MR28_B0;          // Byte offset 0xac, CSR Addr 0x5802b, Direction=in
                              // Value to be programmed in DRAM Mode Register 28 {Channel B, Rank 0}
   uint8_t  MR28_B1;          // Byte offset 0xad, CSR Addr 0x5802b, Direction=in
                              // Value to be programmed in DRAM Mode Register 28 {Channel B, Rank 1}
   uint8_t  MR30_A0;          // Byte offset 0xae, CSR Addr 0x5802b, Direction=in
                              // Value to be programmed in DRAM Mode Register 30 {Channel A, Rank 0}
   uint8_t  MR30_A1;          // Byte offset 0xaf, CSR Addr 0x5802b, Direction=in
                              // Value to be programmed in DRAM Mode Register 30 {Channel A, Rank 1}
   uint8_t  MR30_B0;          // Byte offset 0xb0, CSR Addr 0x5802c, Direction=in
                              // Value to be programmed in DRAM Mode Register 30 {Channel B, Rank 0}
   uint8_t  MR30_B1;          // Byte offset 0xb1, CSR Addr 0x5802c, Direction=in
                              // Value to be programmed in DRAM Mode Register 30 {Channel B, Rank 1}
   uint8_t  MR31_A0;          // Byte offset 0xb2, CSR Addr 0x5802c, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR31_A1;          // Byte offset 0xb3, CSR Addr 0x5802c, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR31_B0;          // Byte offset 0xb4, CSR Addr 0x5802d, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR31_B1;          // Byte offset 0xb5, CSR Addr 0x5802d, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR32_A0;          // Byte offset 0xb6, CSR Addr 0x5802d, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR32_A1;          // Byte offset 0xb7, CSR Addr 0x5802d, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR32_B0;          // Byte offset 0xb8, CSR Addr 0x5802e, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR32_B1;          // Byte offset 0xb9, CSR Addr 0x5802e, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR33_A0;          // Byte offset 0xba, CSR Addr 0x5802e, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR33_A1;          // Byte offset 0xbb, CSR Addr 0x5802e, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR33_B0;          // Byte offset 0xbc, CSR Addr 0x5802f, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR33_B1;          // Byte offset 0xbd, CSR Addr 0x5802f, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR34_A0;          // Byte offset 0xbe, CSR Addr 0x5802f, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR34_A1;          // Byte offset 0xbf, CSR Addr 0x5802f, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR34_B0;          // Byte offset 0xc0, CSR Addr 0x58030, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR34_B1;          // Byte offset 0xc1, CSR Addr 0x58030, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR37_A0;          // Byte offset 0xc2, CSR Addr 0x58030, Direction=in
                              // Value to be programmed in DRAM Mode Register 37 {Channel A, Rank 0}
   uint8_t  MR37_A1;          // Byte offset 0xc3, CSR Addr 0x58030, Direction=in
                              // Value to be programmed in DRAM Mode Register 37 {Channel A, Rank 1}
   uint8_t  MR37_B0;          // Byte offset 0xc4, CSR Addr 0x58031, Direction=in
                              // Value to be programmed in DRAM Mode Register 37 {Channel B, Rank 0}
   uint8_t  MR37_B1;          // Byte offset 0xc5, CSR Addr 0x58031, Direction=in
                              // Value to be programmed in DRAM Mode Register 37 {Channel B, Rank 1}
   uint8_t  MR40_A0;          // Byte offset 0xc6, CSR Addr 0x58031, Direction=in
                              // Value to be programmed in DRAM Mode Register 40 {Channel A, Rank 0}
   uint8_t  MR40_A1;          // Byte offset 0xc7, CSR Addr 0x58031, Direction=in
                              // Value to be programmed in DRAM Mode Register 40 {Channel A, Rank 1}
   uint8_t  MR40_B0;          // Byte offset 0xc8, CSR Addr 0x58032, Direction=in
                              // Value to be programmed in DRAM Mode Register 40 {Channel B, Rank 0}
   uint8_t  MR40_B1;          // Byte offset 0xc9, CSR Addr 0x58032, Direction=in
                              // Value to be programmed in DRAM Mode Register 40 {Channel B, Rank 1}
   uint8_t  MR41_A0;          // Byte offset 0xca, CSR Addr 0x58032, Direction=in
                              // Value to be programmed in DRAM Mode Register 41 {Channel A, Rank 0}
   uint8_t  MR41_A1;          // Byte offset 0xcb, CSR Addr 0x58032, Direction=in
                              // Value to be programmed in DRAM Mode Register 41 {Channel A, Rank 1}
   uint8_t  MR41_B0;          // Byte offset 0xcc, CSR Addr 0x58033, Direction=in
                              // Value to be programmed in DRAM Mode Register 41 {Channel B, Rank 0}
   uint8_t  MR41_B1;          // Byte offset 0xcd, CSR Addr 0x58033, Direction=in
                              // Value to be programmed in DRAM Mode Register 41 {Channel B, Rank 1}
   uint8_t  MR57_A0;          // Byte offset 0xce, CSR Addr 0x58033, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR57_A1;          // Byte offset 0xcf, CSR Addr 0x58033, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR57_B0;          // Byte offset 0xd0, CSR Addr 0x58034, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR57_B1;          // Byte offset 0xd1, CSR Addr 0x58034, Direction=in
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  MR58_A0;          // Byte offset 0xd2, CSR Addr 0x58034, Direction=in
                              // Value to be programmed in DRAM Mode Register 58 {Channel A, Rank 0}
   uint8_t  MR58_A1;          // Byte offset 0xd3, CSR Addr 0x58034, Direction=in
                              // Value to be programmed in DRAM Mode Register 58 {Channel A, Rank 1}
   uint8_t  MR58_B0;          // Byte offset 0xd4, CSR Addr 0x58035, Direction=in
                              // Value to be programmed in DRAM Mode Register 58 {Channel B, Rank 0}
   uint8_t  MR58_B1;          // Byte offset 0xd5, CSR Addr 0x58035, Direction=in
                              // Value to be programmed in DRAM Mode Register 58 {Channel B, Rank 1}
   uint8_t  MR69_A0;          // Byte offset 0xd6, CSR Addr 0x58035, Direction=in
                              // Value to be programmed in DRAM Mode Register 69 {Channel A, Rank 0}
   uint8_t  MR69_A1;          // Byte offset 0xd7, CSR Addr 0x58035, Direction=in
                              // Value to be programmed in DRAM Mode Register 69 {Channel A, Rank 1}
   uint8_t  MR69_B0;          // Byte offset 0xd8, CSR Addr 0x58036, Direction=in
                              // Value to be programmed in DRAM Mode Register 69 {Channel B, Rank 0}
   uint8_t  MR69_B1;          // Byte offset 0xd9, CSR Addr 0x58036, Direction=in
                              // Value to be programmed in DRAM Mode Register 69 {Channel B, Rank 1}
   uint8_t  MR70_A0;          // Byte offset 0xda, CSR Addr 0x58036, Direction=in
                              // Value to be programmed in DRAM Mode Register 70 {Channel A, Rank 0}
   uint8_t  MR70_A1;          // Byte offset 0xdb, CSR Addr 0x58036, Direction=in
                              // Value to be programmed in DRAM Mode Register 70 {Channel A, Rank 1}
   uint8_t  MR70_B0;          // Byte offset 0xdc, CSR Addr 0x58037, Direction=in
                              // Value to be programmed in DRAM Mode Register 70 {Channel B, Rank 0}
   uint8_t  MR70_B1;          // Byte offset 0xdd, CSR Addr 0x58037, Direction=in
                              // Value to be programmed in DRAM Mode Register 70 {Channel B, Rank 1}
   uint8_t  MR71_A0;          // Byte offset 0xde, CSR Addr 0x58037, Direction=in
                              // Value to be programmed in DRAM Mode Register 71 {Channel A, Rank 0}
   uint8_t  MR71_A1;          // Byte offset 0xdf, CSR Addr 0x58037, Direction=in
                              // Value to be programmed in DRAM Mode Register 71 {Channel A, Rank 1}
   uint8_t  MR71_B0;          // Byte offset 0xe0, CSR Addr 0x58038, Direction=in
                              // Value to be programmed in DRAM Mode Register 71 {Channel B, Rank 0}
   uint8_t  MR71_B1;          // Byte offset 0xe1, CSR Addr 0x58038, Direction=in
                              // Value to be programmed in DRAM Mode Register 71 {Channel B, Rank 1}
   uint8_t  MR72_A0;          // Byte offset 0xe2, CSR Addr 0x58038, Direction=in
                              // Value to be programmed in DRAM Mode Register 72 {Channel A, Rank 0}
   uint8_t  MR72_A1;          // Byte offset 0xe3, CSR Addr 0x58038, Direction=in
                              // Value to be programmed in DRAM Mode Register 72 {Channel A, Rank 1}
   uint8_t  MR72_B0;          // Byte offset 0xe4, CSR Addr 0x58039, Direction=in
                              // Value to be programmed in DRAM Mode Register 72 {Channel B, Rank 0}
   uint8_t  MR72_B1;          // Byte offset 0xe5, CSR Addr 0x58039, Direction=in
                              // Value to be programmed in DRAM Mode Register 72 {Channel B, Rank 1}
   uint8_t  MR73_A0;          // Byte offset 0xe6, CSR Addr 0x58039, Direction=in
                              // Value to be programmed in DRAM Mode Register 73 {Channel A, Rank 0}
   uint8_t  MR73_A1;          // Byte offset 0xe7, CSR Addr 0x58039, Direction=in
                              // Value to be programmed in DRAM Mode Register 73 {Channel A, Rank 1}
   uint8_t  MR73_B0;          // Byte offset 0xe8, CSR Addr 0x5803a, Direction=in
                              // Value to be programmed in DRAM Mode Register 73 {Channel B, Rank 0}
   uint8_t  MR73_B1;          // Byte offset 0xe9, CSR Addr 0x5803a, Direction=in
                              // Value to be programmed in DRAM Mode Register 73 {Channel B, Rank 1}
   uint8_t  MR74_A0;          // Byte offset 0xea, CSR Addr 0x5803a, Direction=in
                              // Value to be programmed in DRAM Mode Register 74 {Channel A, Rank 0}
   uint8_t  MR74_A1;          // Byte offset 0xeb, CSR Addr 0x5803a, Direction=in
                              // Value to be programmed in DRAM Mode Register 74 {Channel A, Rank 1}
   uint8_t  MR74_B0;          // Byte offset 0xec, CSR Addr 0x5803b, Direction=in
                              // Value to be programmed in DRAM Mode Register 74 {Channel B, Rank 0}
   uint8_t  MR74_B1;          // Byte offset 0xed, CSR Addr 0x5803b, Direction=in
                              // Value to be programmed in DRAM Mode Register 74 {Channel B, Rank 1}
   uint8_t  Disable2D;        // Byte offset 0xee, CSR Addr 0x5803b, Direction=In
                              // Set to disable 2D training
   uint8_t  PPT2OffsetMargin; // Byte offset 0xef, CSR Addr 0x5803b, Direction=In
                              // When set to 0 disabled, non zero values add that much margin to left and right eye offsets to prevent underflow or overflow.
   uint8_t  TrainedVREFDQU_A0; // Byte offset 0xf0, CSR Addr 0x5803c, Direction=Out
                              // Trained CA DQ Upper setting for Ch A Rank 0
   uint8_t  TrainedDRAMDFE_A0; // Byte offset 0xf1, CSR Addr 0x5803c, Direction=Out
                              // Trained DRAM DFE setting for Ch A Rank 0 
                              //   Upper byte [6:4]
                              //   Lower byte  [2:0]
   uint8_t  TrainedDRAMDCA_A0; // Byte offset 0xf2, CSR Addr 0x5803c, Direction=Out
                              // Trained DRAM DCA 
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  forceRxReplica;   // Byte offset 0xf3, CSR Addr 0x5803c, Direction=In
                              // when set to 1 force rxReplica to calibrate and be used for training below 2667 Mbps
   uint8_t  HardwareScans;    // Byte offset 0xf4, CSR Addr 0x5803d, Direction=In
                              // Use hardware scan for specific training steps: 0 = Software delay scan, 1 = Hardware delay scan
                              //   HardwareScans[0]: read training (includes RxDfe)
                              //   HardwareScans[1]: write training
                              //   HardwareScans[2]: DCA
                              //   HardwareScans[3]: TxDfe
   uint8_t  TrainedVREFDQU_A1; // Byte offset 0xf5, CSR Addr 0x5803d, Direction=Out
                              // Trained CA DQ Upper setting for Ch A Rank 1
   uint8_t  TrainedDRAMDFE_A1; // Byte offset 0xf6, CSR Addr 0x5803d, Direction=Out
                              // Trained DRAM DFE setting for Ch A Rank 1
                              //   Upper byte [6:4]
                              //   Lower byte  [2:0]
   uint8_t  TrainedDRAMDCA_A1; // Byte offset 0xf7, CSR Addr 0x5803d, Direction=Out
                              // Trained DRAM DCA 
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  TxDFETrainOpt;    // Byte offset 0xf8, CSR Addr 0x5803e, Direction=in
                              // TxDFETrainOpt[0] If the DRAM supports per-pin DFE enable in MR41 OP[0] = 0x1
                              //    0: unsupported 
                              //    1: supported
   uint8_t  SDOpt;            // Byte offset 0xf9, CSR Addr 0x5803e, Direction=in
                              // RFU, must be zero
   uint8_t  TrainedVREFDQU_B0; // Byte offset 0xfa, CSR Addr 0x5803e, Direction=Out
                              // Trained CA DQ Upper setting for Ch B Rank 0
   uint8_t  TrainedDRAMDFE_B0; // Byte offset 0xfb, CSR Addr 0x5803e, Direction=Out
                              // Trained DRAM DFE setting for Ch B Rank 0
                              //   Upper byte [6:4]
                              //   Lower byte  [2:0]
   uint8_t  TrainedDRAMDCA_B0; // Byte offset 0xfc, CSR Addr 0x5803f, Direction=Out
                              // Trained DRAM DCA 
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  ReservedFD;       // Byte offset 0xfd, CSR Addr 0x5803f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  ReservedFE;       // Byte offset 0xfe, CSR Addr 0x5803f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  TrainedVREFDQU_B1; // Byte offset 0xff, CSR Addr 0x5803f, Direction=Out
                              // Trained CA DQ Upper setting for Ch B Rank 1
   uint8_t  TrainedDRAMDFE_B1; // Byte offset 0x100, CSR Addr 0x58040, Direction=Out
                              // Trained DRAM DFE setting for Ch B Rank 1
                              //   Upper byte [6:4]
                              //   Lower byte  [2:0]
   uint8_t  TrainedDRAMDCA_B1; // Byte offset 0x101, CSR Addr 0x58040, Direction=Out
                              // Trained DRAM DCA 
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  Reserved102;      // Byte offset 0x102, CSR Addr 0x58040, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved103;      // Byte offset 0x103, CSR Addr 0x58040, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  RdWrPatternA;     // Byte offset 0x104, CSR Addr 0x58041, Direction=In
                              // Lower-byte read pattern for training 
                              // Enabled with LdffMode[2]
   uint8_t  RdWrPatternB;     // Byte offset 0x105, CSR Addr 0x58041, Direction=In
                              // Upper-byte read pattern for training 
                              // Enabled with LdffMode[2]
   uint8_t  RdWrInvert;       // Byte offset 0x106, CSR Addr 0x58041, Direction=In
                              // Each bit in RdWrInvert represents a lane in the DBYTE which has its data inverted during read transactions during training.
                              // Eg, [0] = 1 inverts lane 0 , [3] = 1 inverts lane 3 . This field applies to all DBYTES
                              // Enabled with LdffMode[2]
   uint8_t  LdffMode;         // Byte offset 0x107, CSR Addr 0x58041, Direction=In
                              // In LDFF mode raw PATN/PRBS sequences driven on DBI & EDC  lanes. If this is set to 0 pattern follows MR settings
                              // [0] = 1 Force DBI like patterns on all lanes
                              // [1] = 1 Force non DBI patterns on all lanes
                              // [2] = 1 use custom patterns from RdWrPatternA, RdWrPatternB, and RdWrInvert
   uint16_t FCDfi0AcsmStart;  // Byte offset 0x108, CSR Addr 0x58042, Direction=In
                              // Start Address for MRW commands for DFI0
   uint16_t FCDfi1AcsmStart  ; // Byte offset 0x10a, CSR Addr 0x58042, Direction=In
                              // Start Address for MRW commands for DFI1
   uint16_t FCDfi0AcsmStartPSY; // Byte offset 0x10c, CSR Addr 0x58043, Direction=In
                              // Start Address for MRW commands for DFI0 for the previous PState
   uint16_t FCDfi1AcsmStartPSY; // Byte offset 0x10e, CSR Addr 0x58043, Direction=In
                              // Start Address for MRW commands for DFI1 for the previous PState
   uint16_t FCDMAStartMR;     // Byte offset 0x110, CSR Addr 0x58044, Direction=In
                              // Start DMA Address for FCDfi0AcsmStart
   uint16_t FCDMAStartCsr;    // Byte offset 0x112, CSR Addr 0x58044, Direction=In
                              // Start DMA Address for Starting CSR
   uint8_t  EnCustomSettings; // Byte offset 0x114, CSR Addr 0x58045, Direction=In
                              // Enable Custome TxSlew and TxImpedance Settings
                              // 
                              // When this field is set to 1, the following LS_ values shall be used in the corresponding AC CSRs during low speed operations.
                              // The values are programmed as it is in the CSRs by the firmware, so these should be set very carefully
                              // This feature is only valid at or above 1600 Mpbs
                              // 
   uint8_t  LSTxSlewCK;       // Byte offset 0x115, CSR Addr 0x58045, Direction=In
                              // Custom Low Speed AC TxSlew for CK
   uint8_t  LSTxSlewCS;       // Byte offset 0x116, CSR Addr 0x58045, Direction=In
                              // Custom Low Speed AC TxSlew for CS
   uint8_t  LSTxSlewCA;       // Byte offset 0x117, CSR Addr 0x58045, Direction=In
                              // Custom Low Speed AC TxSlew for CA
   uint8_t  LSTxImpedanceCK;  // Byte offset 0x118, CSR Addr 0x58046, Direction=In
                              // Custom Low Speed AC TxImpedance for CK
   uint8_t  LSTxImpedanceCS;  // Byte offset 0x119, CSR Addr 0x58046, Direction=In
                              // Custom Low Speed AC TxImpedance for CS
   uint8_t  LSTxImpedanceCA;  // Byte offset 0x11a, CSR Addr 0x58046, Direction=In
                              // Custom Low Speed AC TxImpedance for CA
   uint8_t  VrefFilterAboveVal; // Byte offset 0x11b, CSR Addr 0x58046, Direction=In
                              // number of steps above vref in Rx 2D training before filtering is applied (enable RX2D_TrainOpt[0] must be set) 
   uint8_t  VrefFilterBelowVal; // Byte offset 0x11c, CSR Addr 0x58047, Direction=In
                              // number of steps below vref in Rx 2D training before filtering is applied (enableRX2D_TrainOpt[0]  must be set) 
   uint8_t  EMOpt;            // Byte offset 0x11d, CSR Addr 0x58047, Direction=in
                              // RFU, must be zero
   uint8_t  Reserved11E;      // Byte offset 0x11e, CSR Addr 0x58047, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved11F;      // Byte offset 0x11f, CSR Addr 0x58047, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  VrefInc;          // Byte offset 0x120, CSR Addr 0x58048, Direction=In
                              // This field should be programmed to 1
                              // This controls the vrefIncrement size for 2D training
   uint8_t  UpperLowerByte;   // Byte offset 0x121, CSR Addr 0x58048, Direction=In
                              // UpperLowerByte[3:0] - A value of 0 means partner bytes are not swapped. A value of 1 means partner bytes are swapped.  
                              // [0] : Channel A Rank 0
                              // [1] : Channel A Rank 1
                              // [2] : Channel B Rank 0
                              // [3] : Channel B Rank1
   uint8_t  Reserved122;      // Byte offset 0x122, CSR Addr 0x58048, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  ALT_RL;           // Byte offset 0x123, CSR Addr 0x58048, Direction=In
                              // This is the alternate Read Latency for DBI off
   uint8_t  MAIN_RL;          // Byte offset 0x124, CSR Addr 0x58049, Direction=In
                              // This is the main RL calculated by phyinit
   uint8_t  CSBACKOFF;        // Byte offset 0x125, CSR Addr 0x58049, Direction=In
                              // Programmable CS delay adjustment
                              // CSBACKOFF = 1 : -0.125tCK
                              // CSBACKOFF = 2 : -0.25tCK
                              // CSBACKOFF = 3 : -0.375tCK
                              // CSBACKOFF = default: -0.5tCK
   uint8_t  WrLvlTrainOpt;    // Byte offset 0x126, CSR Addr 0x58049, Direction=In
                              // Write leveling training options
                              // [0] = When set, coarse wck2ck leveling training is skipped
   uint8_t  Reserved127;      // Byte offset 0x127, CSR Addr 0x58049, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint16_t FCDCCMStartCSR;   // Byte offset 0x128, CSR Addr 0x5804a, Direction=out
                              // Start Address in DCCM for CSRs to be copied to DMA
   uint16_t FCDCCMLenCSR;     // Byte offset 0x12a, CSR Addr 0x5804a, Direction=out
                              // number of entries written into DCCM for CSRs
   uint16_t FCDCCMStartMR;    // Byte offset 0x12c, CSR Addr 0x5804b, Direction=out
                              // Start Address in DCCM for Mrs to be copied to DMA
   uint16_t  FCDCCMLenMR;     // Byte offset 0x12e, CSR Addr 0x5804b, Direction=out
                              // number of entries written into DCCM for Mrs
   int8_t   MRLCalcAdj;       // Byte offset 0x130, CSR Addr 0x5804c, Direction=In
                              // This field is treated as an int_8 and is added to the intermediate MRL values used in training.
   uint8_t  LP5XMode;         // Byte offset 0x131, CSR Addr 0x5804c, Direction=In
                              // Must be Set if DRAM supports LP5X
   uint8_t  DfiMRL_Margin_A0; // Byte offset 0x132, CSR Addr 0x5804c, Direction=Out
                              // Distance from the trained value to the closest failing region in DFIClk steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DfiMRL_Margin_A1; // Byte offset 0x133, CSR Addr 0x5804c, Direction=Out
                              // Distance from the trained value to the closest failing region in DFIClk steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DfiMRL_Margin_B0; // Byte offset 0x134, CSR Addr 0x5804d, Direction=Out
                              // Distance from the trained value to the closest failing region in DFIClk steps. This value is the minimum of all eyes in this timing group.
   uint8_t  DfiMRL_Margin_B1; // Byte offset 0x135, CSR Addr 0x5804d, Direction=Out
                              // Distance from the trained value to the closest failing region in DFIClk steps. This value is the minimum of all eyes in this timing group.
   uint8_t  Reserved136;      // Byte offset 0x136, CSR Addr 0x5804d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved137;      // Byte offset 0x137, CSR Addr 0x5804d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint16_t RxVrefStartPat;   // Byte offset 0x138, CSR Addr 0x5804e, Direction=In
                              // Starting VREF Value for Rx Training for Pattern Mode
   uint16_t RxVrefStartPrbs;  // Byte offset 0x13a, CSR Addr 0x5804e, Direction=In
                              // Train2Dmisc[13]= 0, Starting VREF Value for Rx Training for Prbs Mode
                              // Train2Dmisc[13]= 1, number of points to scan before the si friendly trained vref
   uint16_t RxVrefEndPat;     // Byte offset 0x13c, CSR Addr 0x5804f, Direction=In
                              // Ending VREF Value for Rx Training for Pattern Mode
   uint16_t RxVrefEndPrbs;    // Byte offset 0x13e, CSR Addr 0x5804f, Direction=In
                              // Train2Dmisc[13]= 0,Ending VREF Value for Rx Training for Prbs Mode
                              // Train2Dmisc[13]= 1,Number of points to scan after the si friendly trained vref
   uint8_t  TxVrefStart;      // Byte offset 0x140, CSR Addr 0x58050, Direction=In
                              // Starting VREF Value for Tx Training for Prbs Mode
   uint8_t  TxVrefEnd;        // Byte offset 0x141, CSR Addr 0x58050, Direction=In
                              // Ending VREF Value for Tx Training for Prbs Mode
   uint16_t RxVrefStepPat;    // Byte offset 0x142, CSR Addr 0x58050, Direction=In
                              // VREF Step Value for Rx Training for Pattern Mode
   uint16_t RxVrefStepPrbs;   // Byte offset 0x144, CSR Addr 0x58051, Direction=In
                              // VREF Step Value for Rx Training for Prbs Mode
   uint8_t  TxVrefStep;       // Byte offset 0x146, CSR Addr 0x58051, Direction=In
                              // VREF Step Value for Tx Training for Prbs Mode
   uint8_t  RxDlyScanShiftRank0Byte0; // Byte offset 0x147, CSR Addr 0x58051, Direction=In
                              // Rx delay scan shift for Rank0 Dbyte0.  Examples:
                              //   0x1 - start scan 1 step earlier
                              //   0xf - start scan 15 steps earlier
                              //   0xff - start scan 1 step later
                              //   0xfe - start scan 2 steps later
   uint8_t  RxDlyScanShiftRank0Byte1; // Byte offset 0x148, CSR Addr 0x58052, Direction=In
                              // Rx delay scan shift for Rank0 Dbyte1
   uint8_t  RxDlyScanShiftRank0Byte2; // Byte offset 0x149, CSR Addr 0x58052, Direction=In
                              // Rx delay scan shift for Rank0 Dbyte2
   uint8_t  RxDlyScanShiftRank0Byte3; // Byte offset 0x14a, CSR Addr 0x58052, Direction=In
                              // Rx delay scan shift for Rank0 Dbyte3
   uint8_t  RxDlyScanShiftRank1Byte0; // Byte offset 0x14b, CSR Addr 0x58052, Direction=In
                              // Rx delay scan shift for Rank1 Dbyte0
   uint8_t  RxDlyScanShiftRank1Byte1; // Byte offset 0x14c, CSR Addr 0x58053, Direction=In
                              // Rx delay scan shift for Rank1 Dbyte1
   uint8_t  RxDlyScanShiftRank1Byte2; // Byte offset 0x14d, CSR Addr 0x58053, Direction=In
                              // Rx delay scan shift for Rank1 Dbyte2
   uint8_t  RxDlyScanShiftRank1Byte3; // Byte offset 0x14e, CSR Addr 0x58053, Direction=In
                              // Rx delay scan shift for Rank1 Dbyte3
   uint8_t  Reserved14F;      // Byte offset 0x14f, CSR Addr 0x58053, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint16_t FCDfi0AcsmStartPS0; // Byte offset 0x150, CSR Addr 0x58054, Direction=In
                              // Start Address for MRW commands for DFI0, for Pstate 0
   uint16_t FCDfi1AcsmStartPS0; // Byte offset 0x152, CSR Addr 0x58054, Direction=In
                              // Start Address for MRW commands for DFI1, for Pstate 0
   uint16_t FCDfi0AcsmStartPS1; // Byte offset 0x154, CSR Addr 0x58055, Direction=In
                              // Start Address for MRW commands for DFI0, for Pstate 1
   uint16_t FCDfi1AcsmStartPS1; // Byte offset 0x156, CSR Addr 0x58055, Direction=In
                              // Start Address for MRW commands for DFI1, for Pstate 1
   uint16_t FCDfi0AcsmStartPS2; // Byte offset 0x158, CSR Addr 0x58056, Direction=In
                              // Start Address for MRW commands for DFI0, for Pstate 2
   uint16_t FCDfi1AcsmStartPS2; // Byte offset 0x15a, CSR Addr 0x58056, Direction=In
                              // Start Address for MRW commands for DFI1, for Pstate 2
   uint16_t FCDfi0AcsmStartPS3; // Byte offset 0x15c, CSR Addr 0x58057, Direction=In
                              // Start Address for MRW commands for DFI0, for Pstate 3
   uint16_t FCDfi1AcsmStartPS3; // Byte offset 0x15e, CSR Addr 0x58057, Direction=In
                              // Start Address for MRW commands for DFI1, for Pstate 3
   uint8_t  RdDQSBitTimeControl; // Byte offset 0x160, CSR Addr 0x58058, Direction=In
                              // RdDQSBitTimeControl[0-2]:
                              // Input for the amount of data bits Read DQS does before deciding if any specific voltage and delay setting passes or fails. Every time this input increases by 1, the number of data comparisons is doubled. The run time will increase proportionally to the number of bit times requested per point.
                              // Basic amount is 128  bits.                         
                              // 0 = 2^0 times of basic amount                           
                              // 1 = 2^1 times of basic amount
                              // ...                
                              // 4 = 2^4 times of basic amount  (default behavior)    
                              //  . . .                    
                              // 7 = 2^7 times of basic amount
                              // 
                              // [3-7]: RFU, must be zero
   uint8_t  WrDqBitTimeControl; // Byte offset 0x161, CSR Addr 0x58058, Direction=In
                              // WrDqBitTimeControl[0-2]:
                              // Input for the amount of data bits Write DQ does before deciding if any specific voltage and delay setting passes or fails. Every time this input increases by 1, the number of data comparisons is doubled. The run time will increase proportionally to the number of bit times requested per point.
                              // Basic amount is 128  bits.                         
                              // 0 = 2^0 times of basic amount                           
                              // 1 = 2^1 times of basic amount
                              // ...                
                              // 4 = 2^4 times of basic amount  (default behavior)    
                              //  . . .                    
                              // 7 = 2^7 times of basic amount
                              // 
                              // [3-7]: RFU, must be zero
   uint8_t  VrefOffsetBitTimeControl; // Byte offset 0x162, CSR Addr 0x58058, Direction=In
                              // VrefOffsetBitTimeControl[0-2]:
                              // Input for the amount of data bits Vref Offset does before deciding if any specific voltage and delay setting passes or fails. Every time this input increases by 1, the number of data comparisons is doubled. The run time will increase proportionally to the number of bit times requested per point.
                              // Basic amount is 128  bits.                         
                              // 0 = 2^0 times of basic amount                           
                              // 1 = 2^1 times of basic amount
                              // ...                
                              // 4 = 2^4 times of basic amount  (default behavior)    
                              //  . . .                    
                              // 7 = 2^7 times of basic amount
                              // 
                              // [3-7]: RFU, must be zero
   uint8_t  PhyDCABitTimeControl; // Byte offset 0x163, CSR Addr 0x58058, Direction=In
                              // PhyDCABitTimeControl[0-2]:
                              // Input for the amount of data bits Phy DCA does before deciding if any specific voltage and delay setting passes or fails. Every time this input increases by 1, the number of data comparisons is doubled. The run time will increase proportionally to the number of bit times requested per point.
                              // Basic amount is 128  bits.                         
                              // 0 = 2^0 times of basic amount                           
                              // 1 = 2^1 times of basic amount
                              // ...                
                              // 4 = 2^4 times of basic amount  (default behavior)    
                              //  . . .                    
                              // 7 = 2^7 times of basic amount
                              // 
                              // [3-7]: RFU, must be zero
   uint8_t  RxDFEBitTimeControl; // Byte offset 0x164, CSR Addr 0x58059, Direction=In
                              // RxDFEBitTimeControl[0-2]:
                              // Input for the amount of data bits RxDFE does before deciding if any specific voltage and delay setting passes or fails. Every time this input increases by 1, the number of data comparisons is doubled. The run time will increase proportionally to the number of bit times requested per point.
                              // Basic amount is 128  bits.                         
                              // 0 = 2^0 times of basic amount                           
                              // 1 = 2^1 times of basic amount
                              // ...                
                              // 4 = 2^4 times of basic amount  (default behavior)    
                              //  . . .                    
                              // 7 = 2^7 times of basic amount
                              // 
                              // RxDFEBitTimeControl[3]:
                              // Generation 2 Training
                              // 0 = Default Algorithm
                              // 1 = Use Generation 2 Algorithm
                              // 
                              // RxDFEBitTimeControl[4]:
                              // DisableRxDFETraining
                              // 0 = Perform RxDFE training as part of RxRCVR training (default)
                              // 1 = Do not perform RxDFE training.
                              // 
                              // RxDFEBitTimeControl[5]:
                              // TrainRxDFEBiasSel
                              // 0 = Do not train RxDFEBiasSel. RxDFEBiasSel will be set to 3. (default)
                              // 1 = Train RxDFEBiasSel. This should only be set if the last trained pstate is the only pstate with RxDFE enabled.
                              // 
                              // RxDFEBitTimeControl[6]:
                              // SkipRxClkRetrain
                              // 0 = perform RxClk scan ( default )
                              // 1 = Do not perform RxClk scan
                              // 
                              // RxDFEBitTimeControl[7]:
                              // InvertDFETapTrainingFeedbackSense
                              // 0 = Do not invert feedback sense ( default )
                              // 1 = Invert feedback sense
                              // 
                              // 
   uint8_t  CATrnDly_Margin_A; // Byte offset 0x165, CSR Addr 0x58059, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this channel.
   uint8_t  CATrnDly_Margin_B; // Byte offset 0x166, CSR Addr 0x58059, Direction=Out
                              // Distance from the trained center to the closest failing region in DLL steps. This value is the minimum of all eyes in this channel.
   uint8_t  TrainedDRAMDQ0DFE_A0; // Byte offset 0x167, CSR Addr 0x58059, Direction=Out
                              // Trained DRAM DFE DQ setting for Ch A Rank 0 
                              //   DFE DQ0 [1:0]
                              //   DFE DQ1 [3:2]
                              //   DFE DQ2 [5:4]
                              //   DFE DQ3 [7:6]
   uint8_t  TrainedDRAMDQ1DFE_A0; // Byte offset 0x168, CSR Addr 0x5805a, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 0 
                              //   DFE DQ4 [1:0]
                              //   DFE DQ5 [3:2]
                              //   DFE DQ6 [5:4]
                              //   DFE DQ7 [7:6]
   uint8_t  TrainedDRAMDQ2DFE_A0; // Byte offset 0x169, CSR Addr 0x5805a, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 0 
                              //   DFE DQ8 [1:0]
                              //   DFE DQ9 [3:2]
                              //   DFE DQ10 [5:4]
                              //   DFE DQ11 [7:6]
   uint8_t  TrainedDRAMDQ3DFE_A0; // Byte offset 0x16a, CSR Addr 0x5805a, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 0 
                              //   DFE DQ12 [1:0]
                              //   DFE DQ12 [3:2]
                              //   DFE DQ14 [5:4]
                              //   DFE DQ15 [7:6]
   uint8_t  TrainedDRAMDQ4DFE_A0; // Byte offset 0x16b, CSR Addr 0x5805a, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 0 
                              //   DFE DMI0 [1:0]
                              //   DFE DMI1 [3:2]
                              //   DFE RDQS0 [5:4]
                              //   DFE RDQS1 [7:6]
   uint8_t  TrainedDRAMDQ0DFE_A1; // Byte offset 0x16c, CSR Addr 0x5805b, Direction=Out
                              // Trained DRAM DFE DQ setting for Ch A Rank 1 
                              //   DFE DQ0 [1:0]
                              //   DFE DQ1 [3:2]
                              //   DFE DQ2 [5:4]
                              //   DFE DQ3 [7:6]
   uint8_t  TrainedDRAMDQ1DFE_A1; // Byte offset 0x16d, CSR Addr 0x5805b, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 1 
                              //   DFE DQ4 [1:0]
                              //   DFE DQ5 [3:2]
                              //   DFE DQ6 [5:4]
                              //   DFE DQ7 [7:6]
   uint8_t  TrainedDRAMDQ2DFE_A1; // Byte offset 0x16e, CSR Addr 0x5805b, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 1 
                              //   DFE DQ8 [1:0]
                              //   DFE DQ9 [3:2]
                              //   DFE DQ10 [5:4]
                              //   DFE DQ11 [7:6]
   uint8_t  TrainedDRAMDQ3DFE_A1; // Byte offset 0x16f, CSR Addr 0x5805b, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 1 
                              //   DFE DQ12 [1:0]
                              //   DFE DQ12 [3:2]
                              //   DFE DQ14 [5:4]
                              //   DFE DQ15 [7:6]
   uint8_t  TrainedDRAMDQ4DFE_A1; // Byte offset 0x170, CSR Addr 0x5805c, Direction=In
                              // Trained DRAM DFE DQ setting for Ch A Rank 1 
                              //   DFE DMI0 [1:0]
                              //   DFE DMI1 [3:2]
                              //   DFE RDQS0 [5:4]
                              //   DFE RDQS1 [7:6]
   uint8_t  TrainedDRAMDQ0DFE_B0; // Byte offset 0x171, CSR Addr 0x5805c, Direction=Out
                              // Trained DRAM DFE DQ setting for Ch B Rank 0 
                              //   DFE DQ0 [1:0]
                              //   DFE DQ1 [3:2]
                              //   DFE DQ2 [5:4]
                              //   DFE DQ3 [7:6]
   uint8_t  TrainedDRAMDQ1DFE_B0; // Byte offset 0x172, CSR Addr 0x5805c, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 0 
                              //   DFE DQ4 [1:0]
                              //   DFE DQ5 [3:2]
                              //   DFE DQ6 [5:4]
                              //   DFE DQ7 [7:6]
   uint8_t  TrainedDRAMDQ2DFE_B0; // Byte offset 0x173, CSR Addr 0x5805c, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 0 
                              //   DFE DQ8 [1:0]
                              //   DFE DQ9 [3:2]
                              //   DFE DQ10 [5:4]
                              //   DFE DQ11 [7:6]
   uint8_t  TrainedDRAMDQ3DFE_B0; // Byte offset 0x174, CSR Addr 0x5805d, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 0 
                              //   DFE DQ12 [1:0]
                              //   DFE DQ12 [3:2]
                              //   DFE DQ14 [5:4]
                              //   DFE DQ15 [7:6]
   uint8_t  TrainedDRAMDQ4DFE_B0; // Byte offset 0x175, CSR Addr 0x5805d, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 0 
                              //   DFE DMI0 [1:0]
                              //   DFE DMI1 [3:2]
                              //   DFE RDQS0 [5:4]
                              //   DFE RDQS1 [7:6]
   uint8_t  TrainedDRAMDQ0DFE_B1; // Byte offset 0x176, CSR Addr 0x5805d, Direction=Out
                              // Trained DRAM DFE DQ setting for Ch B Rank 1 
                              //   DFE DQ0 [1:0]
                              //   DFE DQ1 [3:2]
                              //   DFE DQ2 [5:4]
                              //   DFE DQ3 [7:6]
   uint8_t  TrainedDRAMDQ1DFE_B1; // Byte offset 0x177, CSR Addr 0x5805d, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 1 
                              //   DFE DQ4 [1:0]
                              //   DFE DQ5 [3:2]
                              //   DFE DQ6 [5:4]
                              //   DFE DQ7 [7:6]
   uint8_t  TrainedDRAMDQ2DFE_B1; // Byte offset 0x178, CSR Addr 0x5805e, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 1
                              //   DFE DQ8 [1:0]
                              //   DFE DQ9 [3:2]
                              //   DFE DQ10 [5:4]
                              //   DFE DQ11 [7:6]
   uint8_t  TrainedDRAMDQ3DFE_B1; // Byte offset 0x179, CSR Addr 0x5805e, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 1
                              //   DFE DQ12 [1:0]
                              //   DFE DQ12 [3:2]
                              //   DFE DQ14 [5:4]
                              //   DFE DQ15 [7:6]
   uint8_t  TrainedDRAMDQ4DFE_B1; // Byte offset 0x17a, CSR Addr 0x5805e, Direction=In
                              // Trained DRAM DFE DQ setting for Ch B Rank 1
                              //   DFE DMI0 [1:0]
                              //   DFE DMI1 [3:2]
                              //   DFE RDQS0 [5:4]
                              //   DFE RDQS1 [7:6]
   uint8_t  DramSupport7StepDFE; // Byte offset 0x17b, CSR Addr 0x5805e, Direction=In
                              // If the DRAM supports 7 Steps for DRAM DCA training in MR24
                              //   0: unsupported 
                              //   1: supported 
   uint8_t  PhyEnhancedTxDCA; // Byte offset 0x17c, CSR Addr 0x5805f, Direction=In
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  TrainedRXDRAMDCA_A0; // Byte offset 0x17d, CSR Addr 0x5805f, Direction=In
                              // Trained RX DRAM DCA setting for Ch A Rank 0
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  TrainedRXDRAMDCA_A1; // Byte offset 0x17e, CSR Addr 0x5805f, Direction=In
                              // Trained RX DRAM DCA setting for Ch A Rank 1
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  TrainedRXDRAMDCA_B0; // Byte offset 0x17f, CSR Addr 0x5805f, Direction=In
                              // Trained RX DRAM DCA setting for Ch B Rank 0
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  TrainedRXDRAMDCA_B1; // Byte offset 0x180, CSR Addr 0x58060, Direction=In
                              // Trained RX DRAM DCA setting for Ch B Rank 1
                              //   Upper byte [7:4]
                              //   Lower byte [3:0]
   uint8_t  RdDQSSiMinEyeWidth; // Byte offset 0x181, CSR Addr 0x58060, Direction=In
                              // If any of the RdDQS SI friendly eyes are smaller than this width training will exit
   uint8_t  RdDQSPRBSMinEyeWidth; // Byte offset 0x182, CSR Addr 0x58060, Direction=In
                              // If any of the RdDQS PRBS eyes are smaller than this width training will exit
   uint8_t  TxDQMinEyeWidth;  // Byte offset 0x183, CSR Addr 0x58060, Direction=In
                              // If any of the TxDQ eyes are smaller than this width training will exit
   uint8_t  CATrnMinEyeWidth; // Byte offset 0x184, CSR Addr 0x58061, Direction=In
                              // If any of the CA Training eyes are smaller than this width training will exit
   uint8_t  SelfTest;         // Byte offset 0x185, CSR Addr 0x58061, Direction=In
                              // Phy Self Test 
                              // SelfTest[0]: Run PMU SRAM self test.
   uint8_t  Reserved186;      // Byte offset 0x186, CSR Addr 0x58061, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  RxClk1uiMinFine;  // Byte offset 0x187, CSR Addr 0x58061, Direction=In
                              // Non-zero values will override the minimum fine bits needed to switch coarse bits for RxReplica PPT support.
                              // This field is for coarse bit selection between Rx1UIThreshold and Rx2UIThreshold.
                              // Value should be specified in x/64ths of a UI. Default minimum fine bits are 16.
   uint16_t Rx2UIThreshold;   // Byte offset 0x188, CSR Addr 0x58062, Direction=in
                              // Set to the data rate to enable custom 2UI threshold for RxClk Training
                              // Below this value and above Rx2uiThreshold RxClkTraining uses  RxClk1uiMinFine
                              // Default data rate is 3200.
   uint16_t Rx1UIThreshold;   // Byte offset 0x18a, CSR Addr 0x58062, Direction=In
                              // Set to the data rate to enable custom 1UI threshold for RxClk Training
                              // Below this value training does not adjust fine bits in RxClk training
                              // Default data rate is 1600.
   uint16_t QBCPllUPllProg0;  // Byte offset 0x18c, CSR Addr 0x58063, Direction=In
                              // CSR CPLLIPProg0 value for normal mode, reserved for Quickboot firmware
   uint16_t QBCPllUPllProg1;  // Byte offset 0x18e, CSR Addr 0x58063, Direction=In
                              // CSR CPLLIPProg1 value for normal mode, reserved for Quickboot firmware
   uint16_t QBCPllUPllProg2;  // Byte offset 0x190, CSR Addr 0x58064, Direction=In
                              // CSR CPLLIPProg2 value for normal mode, reserved for Quickboot firmware
   uint16_t QBCPllUPllProg3;  // Byte offset 0x192, CSR Addr 0x58064, Direction=In
                              // CSR CPLLIPProg3 value for normal mode, reserved for Quickboot firmware
   uint16_t QBCPllCtrl1Px;    // Byte offset 0x194, CSR Addr 0x58065, Direction=In
                              // CSR CPllCtrl1Px value for normal mode, Px Last pstate where x is 0,1,2,3 and reserved for Quickboot firmware
   uint16_t QBCPllCtrl4Px;    // Byte offset 0x196, CSR Addr 0x58065, Direction=In
                              // CSR CPllCtrl4Px value for normal mode, Px Last pstate where x is 0,1,2,3 and reserved for Quickboot firmware
   uint16_t QBCPllCtrl5Px;    // Byte offset 0x198, CSR Addr 0x58066, Direction=In
                              // CSR CPllCtrl5Px value for normal mode, Px Last pstate where x is 0,1,2,3 and reserved for Quickboot firmware
   uint8_t  Lp5xTinit3Op1;    // Byte offset 0x19a, CSR Addr 0x58066, Direction=In
                              // This field is configured by phyinit.
   uint8_t  Lp5xTinit3Op2;    // Byte offset 0x19b, CSR Addr 0x58066, Direction=In
                              // This field is configured by phyinit.
   uint32_t TSTINSADDR;       // Byte offset 0x19c, CSR Addr 0x58067, Direction=out
                              // Reserved for Training Usage
   uint8_t  Reserved1A0;      // Byte offset 0x1a0, CSR Addr 0x58068, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A1;      // Byte offset 0x1a1, CSR Addr 0x58068, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A2;      // Byte offset 0x1a2, CSR Addr 0x58068, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A3;      // Byte offset 0x1a3, CSR Addr 0x58068, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A4;      // Byte offset 0x1a4, CSR Addr 0x58069, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A5;      // Byte offset 0x1a5, CSR Addr 0x58069, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A6;      // Byte offset 0x1a6, CSR Addr 0x58069, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A7;      // Byte offset 0x1a7, CSR Addr 0x58069, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A8;      // Byte offset 0x1a8, CSR Addr 0x5806a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1A9;      // Byte offset 0x1a9, CSR Addr 0x5806a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1AA;      // Byte offset 0x1aa, CSR Addr 0x5806a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1AB;      // Byte offset 0x1ab, CSR Addr 0x5806a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1AC;      // Byte offset 0x1ac, CSR Addr 0x5806b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1AD;      // Byte offset 0x1ad, CSR Addr 0x5806b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1AE;      // Byte offset 0x1ae, CSR Addr 0x5806b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1AF;      // Byte offset 0x1af, CSR Addr 0x5806b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B0;      // Byte offset 0x1b0, CSR Addr 0x5806c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B1;      // Byte offset 0x1b1, CSR Addr 0x5806c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B2;      // Byte offset 0x1b2, CSR Addr 0x5806c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B3;      // Byte offset 0x1b3, CSR Addr 0x5806c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B4;      // Byte offset 0x1b4, CSR Addr 0x5806d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B5;      // Byte offset 0x1b5, CSR Addr 0x5806d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B6;      // Byte offset 0x1b6, CSR Addr 0x5806d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B7;      // Byte offset 0x1b7, CSR Addr 0x5806d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B8;      // Byte offset 0x1b8, CSR Addr 0x5806e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1B9;      // Byte offset 0x1b9, CSR Addr 0x5806e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1BA;      // Byte offset 0x1ba, CSR Addr 0x5806e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1BB;      // Byte offset 0x1bb, CSR Addr 0x5806e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1BC;      // Byte offset 0x1bc, CSR Addr 0x5806f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1BD;      // Byte offset 0x1bd, CSR Addr 0x5806f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1BE;      // Byte offset 0x1be, CSR Addr 0x5806f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1BF;      // Byte offset 0x1bf, CSR Addr 0x5806f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C0;      // Byte offset 0x1c0, CSR Addr 0x58070, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C1;      // Byte offset 0x1c1, CSR Addr 0x58070, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C2;      // Byte offset 0x1c2, CSR Addr 0x58070, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C3;      // Byte offset 0x1c3, CSR Addr 0x58070, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C4;      // Byte offset 0x1c4, CSR Addr 0x58071, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C5;      // Byte offset 0x1c5, CSR Addr 0x58071, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C6;      // Byte offset 0x1c6, CSR Addr 0x58071, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C7;      // Byte offset 0x1c7, CSR Addr 0x58071, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C8;      // Byte offset 0x1c8, CSR Addr 0x58072, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1C9;      // Byte offset 0x1c9, CSR Addr 0x58072, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1CA;      // Byte offset 0x1ca, CSR Addr 0x58072, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1CB;      // Byte offset 0x1cb, CSR Addr 0x58072, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1CC;      // Byte offset 0x1cc, CSR Addr 0x58073, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1CD;      // Byte offset 0x1cd, CSR Addr 0x58073, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1CE;      // Byte offset 0x1ce, CSR Addr 0x58073, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1CF;      // Byte offset 0x1cf, CSR Addr 0x58073, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D0;      // Byte offset 0x1d0, CSR Addr 0x58074, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D1;      // Byte offset 0x1d1, CSR Addr 0x58074, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D2;      // Byte offset 0x1d2, CSR Addr 0x58074, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D3;      // Byte offset 0x1d3, CSR Addr 0x58074, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D4;      // Byte offset 0x1d4, CSR Addr 0x58075, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D5;      // Byte offset 0x1d5, CSR Addr 0x58075, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D6;      // Byte offset 0x1d6, CSR Addr 0x58075, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D7;      // Byte offset 0x1d7, CSR Addr 0x58075, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D8;      // Byte offset 0x1d8, CSR Addr 0x58076, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1D9;      // Byte offset 0x1d9, CSR Addr 0x58076, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1DA;      // Byte offset 0x1da, CSR Addr 0x58076, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1DB;      // Byte offset 0x1db, CSR Addr 0x58076, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1DC;      // Byte offset 0x1dc, CSR Addr 0x58077, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1DD;      // Byte offset 0x1dd, CSR Addr 0x58077, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1DE;      // Byte offset 0x1de, CSR Addr 0x58077, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1DF;      // Byte offset 0x1df, CSR Addr 0x58077, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E0;      // Byte offset 0x1e0, CSR Addr 0x58078, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E1;      // Byte offset 0x1e1, CSR Addr 0x58078, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E2;      // Byte offset 0x1e2, CSR Addr 0x58078, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E3;      // Byte offset 0x1e3, CSR Addr 0x58078, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E4;      // Byte offset 0x1e4, CSR Addr 0x58079, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E5;      // Byte offset 0x1e5, CSR Addr 0x58079, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E6;      // Byte offset 0x1e6, CSR Addr 0x58079, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E7;      // Byte offset 0x1e7, CSR Addr 0x58079, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E8;      // Byte offset 0x1e8, CSR Addr 0x5807a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1E9;      // Byte offset 0x1e9, CSR Addr 0x5807a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1EA;      // Byte offset 0x1ea, CSR Addr 0x5807a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1EB;      // Byte offset 0x1eb, CSR Addr 0x5807a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1EC;      // Byte offset 0x1ec, CSR Addr 0x5807b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1ED;      // Byte offset 0x1ed, CSR Addr 0x5807b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1EE;      // Byte offset 0x1ee, CSR Addr 0x5807b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1EF;      // Byte offset 0x1ef, CSR Addr 0x5807b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F0;      // Byte offset 0x1f0, CSR Addr 0x5807c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F1;      // Byte offset 0x1f1, CSR Addr 0x5807c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F2;      // Byte offset 0x1f2, CSR Addr 0x5807c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F3;      // Byte offset 0x1f3, CSR Addr 0x5807c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F4;      // Byte offset 0x1f4, CSR Addr 0x5807d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F5;      // Byte offset 0x1f5, CSR Addr 0x5807d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F6;      // Byte offset 0x1f6, CSR Addr 0x5807d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F7;      // Byte offset 0x1f7, CSR Addr 0x5807d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F8;      // Byte offset 0x1f8, CSR Addr 0x5807e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1F9;      // Byte offset 0x1f9, CSR Addr 0x5807e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1FA;      // Byte offset 0x1fa, CSR Addr 0x5807e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1FB;      // Byte offset 0x1fb, CSR Addr 0x5807e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1FC;      // Byte offset 0x1fc, CSR Addr 0x5807f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1FD;      // Byte offset 0x1fd, CSR Addr 0x5807f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1FE;      // Byte offset 0x1fe, CSR Addr 0x5807f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved1FF;      // Byte offset 0x1ff, CSR Addr 0x5807f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved200;      // Byte offset 0x200, CSR Addr 0x58080, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved201;      // Byte offset 0x201, CSR Addr 0x58080, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved202;      // Byte offset 0x202, CSR Addr 0x58080, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved203;      // Byte offset 0x203, CSR Addr 0x58080, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved204;      // Byte offset 0x204, CSR Addr 0x58081, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved205;      // Byte offset 0x205, CSR Addr 0x58081, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved206;      // Byte offset 0x206, CSR Addr 0x58081, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved207;      // Byte offset 0x207, CSR Addr 0x58081, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved208;      // Byte offset 0x208, CSR Addr 0x58082, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved209;      // Byte offset 0x209, CSR Addr 0x58082, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved20A;      // Byte offset 0x20a, CSR Addr 0x58082, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved20B;      // Byte offset 0x20b, CSR Addr 0x58082, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved20C;      // Byte offset 0x20c, CSR Addr 0x58083, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved20D;      // Byte offset 0x20d, CSR Addr 0x58083, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved20E;      // Byte offset 0x20e, CSR Addr 0x58083, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved20F;      // Byte offset 0x20f, CSR Addr 0x58083, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved210;      // Byte offset 0x210, CSR Addr 0x58084, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved211;      // Byte offset 0x211, CSR Addr 0x58084, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved212;      // Byte offset 0x212, CSR Addr 0x58084, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved213;      // Byte offset 0x213, CSR Addr 0x58084, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved214;      // Byte offset 0x214, CSR Addr 0x58085, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved215;      // Byte offset 0x215, CSR Addr 0x58085, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved216;      // Byte offset 0x216, CSR Addr 0x58085, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved217;      // Byte offset 0x217, CSR Addr 0x58085, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved218;      // Byte offset 0x218, CSR Addr 0x58086, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved219;      // Byte offset 0x219, CSR Addr 0x58086, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved21A;      // Byte offset 0x21a, CSR Addr 0x58086, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved21B;      // Byte offset 0x21b, CSR Addr 0x58086, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved21C;      // Byte offset 0x21c, CSR Addr 0x58087, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved21D;      // Byte offset 0x21d, CSR Addr 0x58087, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved21E;      // Byte offset 0x21e, CSR Addr 0x58087, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved21F;      // Byte offset 0x21f, CSR Addr 0x58087, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved220;      // Byte offset 0x220, CSR Addr 0x58088, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved221;      // Byte offset 0x221, CSR Addr 0x58088, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved222;      // Byte offset 0x222, CSR Addr 0x58088, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved223;      // Byte offset 0x223, CSR Addr 0x58088, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved224;      // Byte offset 0x224, CSR Addr 0x58089, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved225;      // Byte offset 0x225, CSR Addr 0x58089, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved226;      // Byte offset 0x226, CSR Addr 0x58089, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved227;      // Byte offset 0x227, CSR Addr 0x58089, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved228;      // Byte offset 0x228, CSR Addr 0x5808a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved229;      // Byte offset 0x229, CSR Addr 0x5808a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved22A;      // Byte offset 0x22a, CSR Addr 0x5808a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved22B;      // Byte offset 0x22b, CSR Addr 0x5808a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved22C;      // Byte offset 0x22c, CSR Addr 0x5808b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved22D;      // Byte offset 0x22d, CSR Addr 0x5808b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved22E;      // Byte offset 0x22e, CSR Addr 0x5808b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved22F;      // Byte offset 0x22f, CSR Addr 0x5808b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved230;      // Byte offset 0x230, CSR Addr 0x5808c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved231;      // Byte offset 0x231, CSR Addr 0x5808c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved232;      // Byte offset 0x232, CSR Addr 0x5808c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved233;      // Byte offset 0x233, CSR Addr 0x5808c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved234;      // Byte offset 0x234, CSR Addr 0x5808d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved235;      // Byte offset 0x235, CSR Addr 0x5808d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved236;      // Byte offset 0x236, CSR Addr 0x5808d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved237;      // Byte offset 0x237, CSR Addr 0x5808d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved238;      // Byte offset 0x238, CSR Addr 0x5808e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved239;      // Byte offset 0x239, CSR Addr 0x5808e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved23A;      // Byte offset 0x23a, CSR Addr 0x5808e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved23B;      // Byte offset 0x23b, CSR Addr 0x5808e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved23C;      // Byte offset 0x23c, CSR Addr 0x5808f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved23D;      // Byte offset 0x23d, CSR Addr 0x5808f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved23E;      // Byte offset 0x23e, CSR Addr 0x5808f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved23F;      // Byte offset 0x23f, CSR Addr 0x5808f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved240;      // Byte offset 0x240, CSR Addr 0x58090, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved241;      // Byte offset 0x241, CSR Addr 0x58090, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved242;      // Byte offset 0x242, CSR Addr 0x58090, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved243;      // Byte offset 0x243, CSR Addr 0x58090, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved244;      // Byte offset 0x244, CSR Addr 0x58091, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved245;      // Byte offset 0x245, CSR Addr 0x58091, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved246;      // Byte offset 0x246, CSR Addr 0x58091, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved247;      // Byte offset 0x247, CSR Addr 0x58091, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved248;      // Byte offset 0x248, CSR Addr 0x58092, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved249;      // Byte offset 0x249, CSR Addr 0x58092, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved24A;      // Byte offset 0x24a, CSR Addr 0x58092, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved24B;      // Byte offset 0x24b, CSR Addr 0x58092, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved24C;      // Byte offset 0x24c, CSR Addr 0x58093, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved24D;      // Byte offset 0x24d, CSR Addr 0x58093, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved24E;      // Byte offset 0x24e, CSR Addr 0x58093, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved24F;      // Byte offset 0x24f, CSR Addr 0x58093, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved250;      // Byte offset 0x250, CSR Addr 0x58094, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved251;      // Byte offset 0x251, CSR Addr 0x58094, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved252;      // Byte offset 0x252, CSR Addr 0x58094, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved253;      // Byte offset 0x253, CSR Addr 0x58094, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved254;      // Byte offset 0x254, CSR Addr 0x58095, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved255;      // Byte offset 0x255, CSR Addr 0x58095, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved256;      // Byte offset 0x256, CSR Addr 0x58095, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved257;      // Byte offset 0x257, CSR Addr 0x58095, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved258;      // Byte offset 0x258, CSR Addr 0x58096, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved259;      // Byte offset 0x259, CSR Addr 0x58096, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved25A;      // Byte offset 0x25a, CSR Addr 0x58096, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved25B;      // Byte offset 0x25b, CSR Addr 0x58096, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved25C;      // Byte offset 0x25c, CSR Addr 0x58097, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved25D;      // Byte offset 0x25d, CSR Addr 0x58097, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved25E;      // Byte offset 0x25e, CSR Addr 0x58097, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved25F;      // Byte offset 0x25f, CSR Addr 0x58097, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved260;      // Byte offset 0x260, CSR Addr 0x58098, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved261;      // Byte offset 0x261, CSR Addr 0x58098, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved262;      // Byte offset 0x262, CSR Addr 0x58098, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved263;      // Byte offset 0x263, CSR Addr 0x58098, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved264;      // Byte offset 0x264, CSR Addr 0x58099, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved265;      // Byte offset 0x265, CSR Addr 0x58099, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved266;      // Byte offset 0x266, CSR Addr 0x58099, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved267;      // Byte offset 0x267, CSR Addr 0x58099, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved268;      // Byte offset 0x268, CSR Addr 0x5809a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved269;      // Byte offset 0x269, CSR Addr 0x5809a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved26A;      // Byte offset 0x26a, CSR Addr 0x5809a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved26B;      // Byte offset 0x26b, CSR Addr 0x5809a, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved26C;      // Byte offset 0x26c, CSR Addr 0x5809b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved26D;      // Byte offset 0x26d, CSR Addr 0x5809b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved26E;      // Byte offset 0x26e, CSR Addr 0x5809b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved26F;      // Byte offset 0x26f, CSR Addr 0x5809b, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved270;      // Byte offset 0x270, CSR Addr 0x5809c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved271;      // Byte offset 0x271, CSR Addr 0x5809c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved272;      // Byte offset 0x272, CSR Addr 0x5809c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved273;      // Byte offset 0x273, CSR Addr 0x5809c, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved274;      // Byte offset 0x274, CSR Addr 0x5809d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved275;      // Byte offset 0x275, CSR Addr 0x5809d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved276;      // Byte offset 0x276, CSR Addr 0x5809d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved277;      // Byte offset 0x277, CSR Addr 0x5809d, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved278;      // Byte offset 0x278, CSR Addr 0x5809e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved279;      // Byte offset 0x279, CSR Addr 0x5809e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved27A;      // Byte offset 0x27a, CSR Addr 0x5809e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved27B;      // Byte offset 0x27b, CSR Addr 0x5809e, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved27C;      // Byte offset 0x27c, CSR Addr 0x5809f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved27D;      // Byte offset 0x27d, CSR Addr 0x5809f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved27E;      // Byte offset 0x27e, CSR Addr 0x5809f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved27F;      // Byte offset 0x27f, CSR Addr 0x5809f, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved280;      // Byte offset 0x280, CSR Addr 0x580a0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved281;      // Byte offset 0x281, CSR Addr 0x580a0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved282;      // Byte offset 0x282, CSR Addr 0x580a0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved283;      // Byte offset 0x283, CSR Addr 0x580a0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved284;      // Byte offset 0x284, CSR Addr 0x580a1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved285;      // Byte offset 0x285, CSR Addr 0x580a1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved286;      // Byte offset 0x286, CSR Addr 0x580a1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved287;      // Byte offset 0x287, CSR Addr 0x580a1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved288;      // Byte offset 0x288, CSR Addr 0x580a2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved289;      // Byte offset 0x289, CSR Addr 0x580a2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved28A;      // Byte offset 0x28a, CSR Addr 0x580a2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved28B;      // Byte offset 0x28b, CSR Addr 0x580a2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved28C;      // Byte offset 0x28c, CSR Addr 0x580a3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved28D;      // Byte offset 0x28d, CSR Addr 0x580a3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved28E;      // Byte offset 0x28e, CSR Addr 0x580a3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved28F;      // Byte offset 0x28f, CSR Addr 0x580a3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved290;      // Byte offset 0x290, CSR Addr 0x580a4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved291;      // Byte offset 0x291, CSR Addr 0x580a4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved292;      // Byte offset 0x292, CSR Addr 0x580a4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved293;      // Byte offset 0x293, CSR Addr 0x580a4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved294;      // Byte offset 0x294, CSR Addr 0x580a5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved295;      // Byte offset 0x295, CSR Addr 0x580a5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved296;      // Byte offset 0x296, CSR Addr 0x580a5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved297;      // Byte offset 0x297, CSR Addr 0x580a5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved298;      // Byte offset 0x298, CSR Addr 0x580a6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved299;      // Byte offset 0x299, CSR Addr 0x580a6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved29A;      // Byte offset 0x29a, CSR Addr 0x580a6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved29B;      // Byte offset 0x29b, CSR Addr 0x580a6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved29C;      // Byte offset 0x29c, CSR Addr 0x580a7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved29D;      // Byte offset 0x29d, CSR Addr 0x580a7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved29E;      // Byte offset 0x29e, CSR Addr 0x580a7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved29F;      // Byte offset 0x29f, CSR Addr 0x580a7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A0;      // Byte offset 0x2a0, CSR Addr 0x580a8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A1;      // Byte offset 0x2a1, CSR Addr 0x580a8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A2;      // Byte offset 0x2a2, CSR Addr 0x580a8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A3;      // Byte offset 0x2a3, CSR Addr 0x580a8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A4;      // Byte offset 0x2a4, CSR Addr 0x580a9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A5;      // Byte offset 0x2a5, CSR Addr 0x580a9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A6;      // Byte offset 0x2a6, CSR Addr 0x580a9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A7;      // Byte offset 0x2a7, CSR Addr 0x580a9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A8;      // Byte offset 0x2a8, CSR Addr 0x580aa, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2A9;      // Byte offset 0x2a9, CSR Addr 0x580aa, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2AA;      // Byte offset 0x2aa, CSR Addr 0x580aa, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2AB;      // Byte offset 0x2ab, CSR Addr 0x580aa, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2AC;      // Byte offset 0x2ac, CSR Addr 0x580ab, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2AD;      // Byte offset 0x2ad, CSR Addr 0x580ab, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2AE;      // Byte offset 0x2ae, CSR Addr 0x580ab, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2AF;      // Byte offset 0x2af, CSR Addr 0x580ab, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B0;      // Byte offset 0x2b0, CSR Addr 0x580ac, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B1;      // Byte offset 0x2b1, CSR Addr 0x580ac, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B2;      // Byte offset 0x2b2, CSR Addr 0x580ac, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B3;      // Byte offset 0x2b3, CSR Addr 0x580ac, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B4;      // Byte offset 0x2b4, CSR Addr 0x580ad, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B5;      // Byte offset 0x2b5, CSR Addr 0x580ad, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B6;      // Byte offset 0x2b6, CSR Addr 0x580ad, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B7;      // Byte offset 0x2b7, CSR Addr 0x580ad, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B8;      // Byte offset 0x2b8, CSR Addr 0x580ae, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2B9;      // Byte offset 0x2b9, CSR Addr 0x580ae, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2BA;      // Byte offset 0x2ba, CSR Addr 0x580ae, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2BB;      // Byte offset 0x2bb, CSR Addr 0x580ae, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2BC;      // Byte offset 0x2bc, CSR Addr 0x580af, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2BD;      // Byte offset 0x2bd, CSR Addr 0x580af, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2BE;      // Byte offset 0x2be, CSR Addr 0x580af, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2BF;      // Byte offset 0x2bf, CSR Addr 0x580af, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C0;      // Byte offset 0x2c0, CSR Addr 0x580b0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C1;      // Byte offset 0x2c1, CSR Addr 0x580b0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C2;      // Byte offset 0x2c2, CSR Addr 0x580b0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C3;      // Byte offset 0x2c3, CSR Addr 0x580b0, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C4;      // Byte offset 0x2c4, CSR Addr 0x580b1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C5;      // Byte offset 0x2c5, CSR Addr 0x580b1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C6;      // Byte offset 0x2c6, CSR Addr 0x580b1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C7;      // Byte offset 0x2c7, CSR Addr 0x580b1, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C8;      // Byte offset 0x2c8, CSR Addr 0x580b2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2C9;      // Byte offset 0x2c9, CSR Addr 0x580b2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2CA;      // Byte offset 0x2ca, CSR Addr 0x580b2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2CB;      // Byte offset 0x2cb, CSR Addr 0x580b2, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2CC;      // Byte offset 0x2cc, CSR Addr 0x580b3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2CD;      // Byte offset 0x2cd, CSR Addr 0x580b3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2CE;      // Byte offset 0x2ce, CSR Addr 0x580b3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2CF;      // Byte offset 0x2cf, CSR Addr 0x580b3, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D0;      // Byte offset 0x2d0, CSR Addr 0x580b4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D1;      // Byte offset 0x2d1, CSR Addr 0x580b4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D2;      // Byte offset 0x2d2, CSR Addr 0x580b4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D3;      // Byte offset 0x2d3, CSR Addr 0x580b4, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D4;      // Byte offset 0x2d4, CSR Addr 0x580b5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D5;      // Byte offset 0x2d5, CSR Addr 0x580b5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D6;      // Byte offset 0x2d6, CSR Addr 0x580b5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D7;      // Byte offset 0x2d7, CSR Addr 0x580b5, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D8;      // Byte offset 0x2d8, CSR Addr 0x580b6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2D9;      // Byte offset 0x2d9, CSR Addr 0x580b6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2DA;      // Byte offset 0x2da, CSR Addr 0x580b6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2DB;      // Byte offset 0x2db, CSR Addr 0x580b6, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2DC;      // Byte offset 0x2dc, CSR Addr 0x580b7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2DD;      // Byte offset 0x2dd, CSR Addr 0x580b7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2DE;      // Byte offset 0x2de, CSR Addr 0x580b7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2DF;      // Byte offset 0x2df, CSR Addr 0x580b7, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E0;      // Byte offset 0x2e0, CSR Addr 0x580b8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E1;      // Byte offset 0x2e1, CSR Addr 0x580b8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E2;      // Byte offset 0x2e2, CSR Addr 0x580b8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E3;      // Byte offset 0x2e3, CSR Addr 0x580b8, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E4;      // Byte offset 0x2e4, CSR Addr 0x580b9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E5;      // Byte offset 0x2e5, CSR Addr 0x580b9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E6;      // Byte offset 0x2e6, CSR Addr 0x580b9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E7;      // Byte offset 0x2e7, CSR Addr 0x580b9, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E8;      // Byte offset 0x2e8, CSR Addr 0x580ba, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2E9;      // Byte offset 0x2e9, CSR Addr 0x580ba, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2EA;      // Byte offset 0x2ea, CSR Addr 0x580ba, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2EB;      // Byte offset 0x2eb, CSR Addr 0x580ba, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2EC;      // Byte offset 0x2ec, CSR Addr 0x580bb, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2ED;      // Byte offset 0x2ed, CSR Addr 0x580bb, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2EE;      // Byte offset 0x2ee, CSR Addr 0x580bb, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2EF;      // Byte offset 0x2ef, CSR Addr 0x580bb, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F0;      // Byte offset 0x2f0, CSR Addr 0x580bc, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F1;      // Byte offset 0x2f1, CSR Addr 0x580bc, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F2;      // Byte offset 0x2f2, CSR Addr 0x580bc, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F3;      // Byte offset 0x2f3, CSR Addr 0x580bc, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F4;      // Byte offset 0x2f4, CSR Addr 0x580bd, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F5;      // Byte offset 0x2f5, CSR Addr 0x580bd, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F6;      // Byte offset 0x2f6, CSR Addr 0x580bd, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F7;      // Byte offset 0x2f7, CSR Addr 0x580bd, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F8;      // Byte offset 0x2f8, CSR Addr 0x580be, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2F9;      // Byte offset 0x2f9, CSR Addr 0x580be, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2FA;      // Byte offset 0x2fa, CSR Addr 0x580be, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2FB;      // Byte offset 0x2fb, CSR Addr 0x580be, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2FC;      // Byte offset 0x2fc, CSR Addr 0x580bf, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  Reserved2FD;      // Byte offset 0x2fd, CSR Addr 0x580bf, Direction=N/A
                              // This field is reserved and must be programmed to 0x00.
   uint8_t  VMRSControl;      // Byte offset 0x2fe, CSR Addr 0x580bf, Direction=In
                              // VMRS Control
                              // 
                              // VMRS Control[0] VMRS Enable
                              //     0x1 = VMRS writes enabled
                              //     0x0 = VMRS writes disabled
                              // 
                              // VMRS Control[1] Additional VMRS request
                              //    0x1 = Additional VMRS will be requested after current batch is written
                              //    0x0 = VMRS write phase is complete after current batch is written
   uint8_t  VMRSCount;        // Byte offset 0x2ff, CSR Addr 0x580bf, Direction=In
                              // VMRS Count[7:0]
                              // 
                              // The number of VMRS addr/data pairs populated in the message block.
                              // 
                              // Should not exceed the maximum number of addr/data pairs in the message block (128).
   uint8_t  VMRSAddr0;        // Byte offset 0x300, CSR Addr 0x580c0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData0
   uint8_t  VMRSAddr1;        // Byte offset 0x301, CSR Addr 0x580c0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData1
   uint8_t  VMRSAddr2;        // Byte offset 0x302, CSR Addr 0x580c0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData2
   uint8_t  VMRSAddr3;        // Byte offset 0x303, CSR Addr 0x580c0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData3
   uint8_t  VMRSAddr4;        // Byte offset 0x304, CSR Addr 0x580c1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData4
   uint8_t  VMRSAddr5;        // Byte offset 0x305, CSR Addr 0x580c1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData5
   uint8_t  VMRSAddr6;        // Byte offset 0x306, CSR Addr 0x580c1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData6
   uint8_t  VMRSAddr7;        // Byte offset 0x307, CSR Addr 0x580c1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData7
   uint8_t  VMRSAddr8;        // Byte offset 0x308, CSR Addr 0x580c2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData8
   uint8_t  VMRSAddr9;        // Byte offset 0x309, CSR Addr 0x580c2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData9
   uint8_t  VMRSAddr10;       // Byte offset 0x30a, CSR Addr 0x580c2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData10
   uint8_t  VMRSAddr11;       // Byte offset 0x30b, CSR Addr 0x580c2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData11
   uint8_t  VMRSAddr12;       // Byte offset 0x30c, CSR Addr 0x580c3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData12
   uint8_t  VMRSAddr13;       // Byte offset 0x30d, CSR Addr 0x580c3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData13
   uint8_t  VMRSAddr14;       // Byte offset 0x30e, CSR Addr 0x580c3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData14
   uint8_t  VMRSAddr15;       // Byte offset 0x30f, CSR Addr 0x580c3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData15
   uint8_t  VMRSAddr16;       // Byte offset 0x310, CSR Addr 0x580c4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData16
   uint8_t  VMRSAddr17;       // Byte offset 0x311, CSR Addr 0x580c4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData17
   uint8_t  VMRSAddr18;       // Byte offset 0x312, CSR Addr 0x580c4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData18
   uint8_t  VMRSAddr19;       // Byte offset 0x313, CSR Addr 0x580c4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData19
   uint8_t  VMRSAddr20;       // Byte offset 0x314, CSR Addr 0x580c5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData20
   uint8_t  VMRSAddr21;       // Byte offset 0x315, CSR Addr 0x580c5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData21
   uint8_t  VMRSAddr22;       // Byte offset 0x316, CSR Addr 0x580c5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData22
   uint8_t  VMRSAddr23;       // Byte offset 0x317, CSR Addr 0x580c5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData23
   uint8_t  VMRSAddr24;       // Byte offset 0x318, CSR Addr 0x580c6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData24
   uint8_t  VMRSAddr25;       // Byte offset 0x319, CSR Addr 0x580c6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData25
   uint8_t  VMRSAddr26;       // Byte offset 0x31a, CSR Addr 0x580c6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData26
   uint8_t  VMRSAddr27;       // Byte offset 0x31b, CSR Addr 0x580c6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData27
   uint8_t  VMRSAddr28;       // Byte offset 0x31c, CSR Addr 0x580c7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData28
   uint8_t  VMRSAddr29;       // Byte offset 0x31d, CSR Addr 0x580c7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData29
   uint8_t  VMRSAddr30;       // Byte offset 0x31e, CSR Addr 0x580c7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData30
   uint8_t  VMRSAddr31;       // Byte offset 0x31f, CSR Addr 0x580c7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData31
   uint8_t  VMRSAddr32;       // Byte offset 0x320, CSR Addr 0x580c8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData32
   uint8_t  VMRSAddr33;       // Byte offset 0x321, CSR Addr 0x580c8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData33
   uint8_t  VMRSAddr34;       // Byte offset 0x322, CSR Addr 0x580c8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData34
   uint8_t  VMRSAddr35;       // Byte offset 0x323, CSR Addr 0x580c8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData35
   uint8_t  VMRSAddr36;       // Byte offset 0x324, CSR Addr 0x580c9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData36
   uint8_t  VMRSAddr37;       // Byte offset 0x325, CSR Addr 0x580c9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData37
   uint8_t  VMRSAddr38;       // Byte offset 0x326, CSR Addr 0x580c9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData38
   uint8_t  VMRSAddr39;       // Byte offset 0x327, CSR Addr 0x580c9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData39
   uint8_t  VMRSAddr40;       // Byte offset 0x328, CSR Addr 0x580ca, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData40
   uint8_t  VMRSAddr41;       // Byte offset 0x329, CSR Addr 0x580ca, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData41
   uint8_t  VMRSAddr42;       // Byte offset 0x32a, CSR Addr 0x580ca, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData42
   uint8_t  VMRSAddr43;       // Byte offset 0x32b, CSR Addr 0x580ca, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData43
   uint8_t  VMRSAddr44;       // Byte offset 0x32c, CSR Addr 0x580cb, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData44
   uint8_t  VMRSAddr45;       // Byte offset 0x32d, CSR Addr 0x580cb, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData45
   uint8_t  VMRSAddr46;       // Byte offset 0x32e, CSR Addr 0x580cb, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData46
   uint8_t  VMRSAddr47;       // Byte offset 0x32f, CSR Addr 0x580cb, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData47
   uint8_t  VMRSAddr48;       // Byte offset 0x330, CSR Addr 0x580cc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData48
   uint8_t  VMRSAddr49;       // Byte offset 0x331, CSR Addr 0x580cc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData49
   uint8_t  VMRSAddr50;       // Byte offset 0x332, CSR Addr 0x580cc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData50
   uint8_t  VMRSAddr51;       // Byte offset 0x333, CSR Addr 0x580cc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData51
   uint8_t  VMRSAddr52;       // Byte offset 0x334, CSR Addr 0x580cd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData52
   uint8_t  VMRSAddr53;       // Byte offset 0x335, CSR Addr 0x580cd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData53
   uint8_t  VMRSAddr54;       // Byte offset 0x336, CSR Addr 0x580cd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData54
   uint8_t  VMRSAddr55;       // Byte offset 0x337, CSR Addr 0x580cd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData55
   uint8_t  VMRSAddr56;       // Byte offset 0x338, CSR Addr 0x580ce, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData56
   uint8_t  VMRSAddr57;       // Byte offset 0x339, CSR Addr 0x580ce, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData57
   uint8_t  VMRSAddr58;       // Byte offset 0x33a, CSR Addr 0x580ce, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData58
   uint8_t  VMRSAddr59;       // Byte offset 0x33b, CSR Addr 0x580ce, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData59
   uint8_t  VMRSAddr60;       // Byte offset 0x33c, CSR Addr 0x580cf, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData60
   uint8_t  VMRSAddr61;       // Byte offset 0x33d, CSR Addr 0x580cf, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData61
   uint8_t  VMRSAddr62;       // Byte offset 0x33e, CSR Addr 0x580cf, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData62
   uint8_t  VMRSAddr63;       // Byte offset 0x33f, CSR Addr 0x580cf, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData63
   uint8_t  VMRSAddr64;       // Byte offset 0x340, CSR Addr 0x580d0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData64
   uint8_t  VMRSAddr65;       // Byte offset 0x341, CSR Addr 0x580d0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData65
   uint8_t  VMRSAddr66;       // Byte offset 0x342, CSR Addr 0x580d0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData66
   uint8_t  VMRSAddr67;       // Byte offset 0x343, CSR Addr 0x580d0, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData67
   uint8_t  VMRSAddr68;       // Byte offset 0x344, CSR Addr 0x580d1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData68
   uint8_t  VMRSAddr69;       // Byte offset 0x345, CSR Addr 0x580d1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData69
   uint8_t  VMRSAddr70;       // Byte offset 0x346, CSR Addr 0x580d1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData70
   uint8_t  VMRSAddr71;       // Byte offset 0x347, CSR Addr 0x580d1, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData71
   uint8_t  VMRSAddr72;       // Byte offset 0x348, CSR Addr 0x580d2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData72
   uint8_t  VMRSAddr73;       // Byte offset 0x349, CSR Addr 0x580d2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData73
   uint8_t  VMRSAddr74;       // Byte offset 0x34a, CSR Addr 0x580d2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData74
   uint8_t  VMRSAddr75;       // Byte offset 0x34b, CSR Addr 0x580d2, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData75
   uint8_t  VMRSAddr76;       // Byte offset 0x34c, CSR Addr 0x580d3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData76
   uint8_t  VMRSAddr77;       // Byte offset 0x34d, CSR Addr 0x580d3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData77
   uint8_t  VMRSAddr78;       // Byte offset 0x34e, CSR Addr 0x580d3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData78
   uint8_t  VMRSAddr79;       // Byte offset 0x34f, CSR Addr 0x580d3, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData79
   uint8_t  VMRSAddr80;       // Byte offset 0x350, CSR Addr 0x580d4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData80
   uint8_t  VMRSAddr81;       // Byte offset 0x351, CSR Addr 0x580d4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData81
   uint8_t  VMRSAddr82;       // Byte offset 0x352, CSR Addr 0x580d4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData82
   uint8_t  VMRSAddr83;       // Byte offset 0x353, CSR Addr 0x580d4, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData83
   uint8_t  VMRSAddr84;       // Byte offset 0x354, CSR Addr 0x580d5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData84
   uint8_t  VMRSAddr85;       // Byte offset 0x355, CSR Addr 0x580d5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData85
   uint8_t  VMRSAddr86;       // Byte offset 0x356, CSR Addr 0x580d5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData86
   uint8_t  VMRSAddr87;       // Byte offset 0x357, CSR Addr 0x580d5, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData87
   uint8_t  VMRSAddr88;       // Byte offset 0x358, CSR Addr 0x580d6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData88
   uint8_t  VMRSAddr89;       // Byte offset 0x359, CSR Addr 0x580d6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData89
   uint8_t  VMRSAddr90;       // Byte offset 0x35a, CSR Addr 0x580d6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData90
   uint8_t  VMRSAddr91;       // Byte offset 0x35b, CSR Addr 0x580d6, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData91
   uint8_t  VMRSAddr92;       // Byte offset 0x35c, CSR Addr 0x580d7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData92
   uint8_t  VMRSAddr93;       // Byte offset 0x35d, CSR Addr 0x580d7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData93
   uint8_t  VMRSAddr94;       // Byte offset 0x35e, CSR Addr 0x580d7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData94
   uint8_t  VMRSAddr95;       // Byte offset 0x35f, CSR Addr 0x580d7, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData95
   uint8_t  VMRSAddr96;       // Byte offset 0x360, CSR Addr 0x580d8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData96
   uint8_t  VMRSAddr97;       // Byte offset 0x361, CSR Addr 0x580d8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData97
   uint8_t  VMRSAddr98;       // Byte offset 0x362, CSR Addr 0x580d8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData98
   uint8_t  VMRSAddr99;       // Byte offset 0x363, CSR Addr 0x580d8, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData99
   uint8_t  VMRSAddr100;      // Byte offset 0x364, CSR Addr 0x580d9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData100
   uint8_t  VMRSAddr101;      // Byte offset 0x365, CSR Addr 0x580d9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData101
   uint8_t  VMRSAddr102;      // Byte offset 0x366, CSR Addr 0x580d9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData102
   uint8_t  VMRSAddr103;      // Byte offset 0x367, CSR Addr 0x580d9, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData103
   uint8_t  VMRSAddr104;      // Byte offset 0x368, CSR Addr 0x580da, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData104
   uint8_t  VMRSAddr105;      // Byte offset 0x369, CSR Addr 0x580da, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData105
   uint8_t  VMRSAddr106;      // Byte offset 0x36a, CSR Addr 0x580da, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData106
   uint8_t  VMRSAddr107;      // Byte offset 0x36b, CSR Addr 0x580da, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData107
   uint8_t  VMRSAddr108;      // Byte offset 0x36c, CSR Addr 0x580db, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData108
   uint8_t  VMRSAddr109;      // Byte offset 0x36d, CSR Addr 0x580db, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData109
   uint8_t  VMRSAddr110;      // Byte offset 0x36e, CSR Addr 0x580db, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData110
   uint8_t  VMRSAddr111;      // Byte offset 0x36f, CSR Addr 0x580db, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData111
   uint8_t  VMRSAddr112;      // Byte offset 0x370, CSR Addr 0x580dc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData112
   uint8_t  VMRSAddr113;      // Byte offset 0x371, CSR Addr 0x580dc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData113
   uint8_t  VMRSAddr114;      // Byte offset 0x372, CSR Addr 0x580dc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData114
   uint8_t  VMRSAddr115;      // Byte offset 0x373, CSR Addr 0x580dc, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData115
   uint8_t  VMRSAddr116;      // Byte offset 0x374, CSR Addr 0x580dd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData116
   uint8_t  VMRSAddr117;      // Byte offset 0x375, CSR Addr 0x580dd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData117
   uint8_t  VMRSAddr118;      // Byte offset 0x376, CSR Addr 0x580dd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData118
   uint8_t  VMRSAddr119;      // Byte offset 0x377, CSR Addr 0x580dd, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData119
   uint8_t  VMRSAddr120;      // Byte offset 0x378, CSR Addr 0x580de, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData120
   uint8_t  VMRSAddr121;      // Byte offset 0x379, CSR Addr 0x580de, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData121
   uint8_t  VMRSAddr122;      // Byte offset 0x37a, CSR Addr 0x580de, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData122
   uint8_t  VMRSAddr123;      // Byte offset 0x37b, CSR Addr 0x580de, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData123
   uint8_t  VMRSAddr124;      // Byte offset 0x37c, CSR Addr 0x580df, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData124
   uint8_t  VMRSAddr125;      // Byte offset 0x37d, CSR Addr 0x580df, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData125
   uint8_t  VMRSAddr126;      // Byte offset 0x37e, CSR Addr 0x580df, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData126
   uint8_t  VMRSAddr127;      // Byte offset 0x37f, CSR Addr 0x580df, Direction=In
                              // VMRS Address to be written, corresponds to VMRSData127
   uint8_t  VMRSData0;        // Byte offset 0x380, CSR Addr 0x580e0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr0
   uint8_t  VMRSData1;        // Byte offset 0x381, CSR Addr 0x580e0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr1
   uint8_t  VMRSData2;        // Byte offset 0x382, CSR Addr 0x580e0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr2
   uint8_t  VMRSData3;        // Byte offset 0x383, CSR Addr 0x580e0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr3
   uint8_t  VMRSData4;        // Byte offset 0x384, CSR Addr 0x580e1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr4
   uint8_t  VMRSData5;        // Byte offset 0x385, CSR Addr 0x580e1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr5
   uint8_t  VMRSData6;        // Byte offset 0x386, CSR Addr 0x580e1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr6
   uint8_t  VMRSData7;        // Byte offset 0x387, CSR Addr 0x580e1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr7
   uint8_t  VMRSData8;        // Byte offset 0x388, CSR Addr 0x580e2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr8
   uint8_t  VMRSData9;        // Byte offset 0x389, CSR Addr 0x580e2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr9
   uint8_t  VMRSData10;       // Byte offset 0x38a, CSR Addr 0x580e2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr10
   uint8_t  VMRSData11;       // Byte offset 0x38b, CSR Addr 0x580e2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr11
   uint8_t  VMRSData12;       // Byte offset 0x38c, CSR Addr 0x580e3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr12
   uint8_t  VMRSData13;       // Byte offset 0x38d, CSR Addr 0x580e3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr13
   uint8_t  VMRSData14;       // Byte offset 0x38e, CSR Addr 0x580e3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr14
   uint8_t  VMRSData15;       // Byte offset 0x38f, CSR Addr 0x580e3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr15
   uint8_t  VMRSData16;       // Byte offset 0x390, CSR Addr 0x580e4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr16
   uint8_t  VMRSData17;       // Byte offset 0x391, CSR Addr 0x580e4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr17
   uint8_t  VMRSData18;       // Byte offset 0x392, CSR Addr 0x580e4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr18
   uint8_t  VMRSData19;       // Byte offset 0x393, CSR Addr 0x580e4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr19
   uint8_t  VMRSData20;       // Byte offset 0x394, CSR Addr 0x580e5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr20
   uint8_t  VMRSData21;       // Byte offset 0x395, CSR Addr 0x580e5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr21
   uint8_t  VMRSData22;       // Byte offset 0x396, CSR Addr 0x580e5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr22
   uint8_t  VMRSData23;       // Byte offset 0x397, CSR Addr 0x580e5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr23
   uint8_t  VMRSData24;       // Byte offset 0x398, CSR Addr 0x580e6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr24
   uint8_t  VMRSData25;       // Byte offset 0x399, CSR Addr 0x580e6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr25
   uint8_t  VMRSData26;       // Byte offset 0x39a, CSR Addr 0x580e6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr26
   uint8_t  VMRSData27;       // Byte offset 0x39b, CSR Addr 0x580e6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr27
   uint8_t  VMRSData28;       // Byte offset 0x39c, CSR Addr 0x580e7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr28
   uint8_t  VMRSData29;       // Byte offset 0x39d, CSR Addr 0x580e7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr29
   uint8_t  VMRSData30;       // Byte offset 0x39e, CSR Addr 0x580e7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr30
   uint8_t  VMRSData31;       // Byte offset 0x39f, CSR Addr 0x580e7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr31
   uint8_t  VMRSData32;       // Byte offset 0x3a0, CSR Addr 0x580e8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr32
   uint8_t  VMRSData33;       // Byte offset 0x3a1, CSR Addr 0x580e8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr33
   uint8_t  VMRSData34;       // Byte offset 0x3a2, CSR Addr 0x580e8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr34
   uint8_t  VMRSData35;       // Byte offset 0x3a3, CSR Addr 0x580e8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr35
   uint8_t  VMRSData36;       // Byte offset 0x3a4, CSR Addr 0x580e9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr36
   uint8_t  VMRSData37;       // Byte offset 0x3a5, CSR Addr 0x580e9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr37
   uint8_t  VMRSData38;       // Byte offset 0x3a6, CSR Addr 0x580e9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr38
   uint8_t  VMRSData39;       // Byte offset 0x3a7, CSR Addr 0x580e9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr39
   uint8_t  VMRSData40;       // Byte offset 0x3a8, CSR Addr 0x580ea, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr40
   uint8_t  VMRSData41;       // Byte offset 0x3a9, CSR Addr 0x580ea, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr41
   uint8_t  VMRSData42;       // Byte offset 0x3aa, CSR Addr 0x580ea, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr42
   uint8_t  VMRSData43;       // Byte offset 0x3ab, CSR Addr 0x580ea, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr43
   uint8_t  VMRSData44;       // Byte offset 0x3ac, CSR Addr 0x580eb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr44
   uint8_t  VMRSData45;       // Byte offset 0x3ad, CSR Addr 0x580eb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr45
   uint8_t  VMRSData46;       // Byte offset 0x3ae, CSR Addr 0x580eb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr46
   uint8_t  VMRSData47;       // Byte offset 0x3af, CSR Addr 0x580eb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr47
   uint8_t  VMRSData48;       // Byte offset 0x3b0, CSR Addr 0x580ec, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr48
   uint8_t  VMRSData49;       // Byte offset 0x3b1, CSR Addr 0x580ec, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr49
   uint8_t  VMRSData50;       // Byte offset 0x3b2, CSR Addr 0x580ec, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr50
   uint8_t  VMRSData51;       // Byte offset 0x3b3, CSR Addr 0x580ec, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr51
   uint8_t  VMRSData52;       // Byte offset 0x3b4, CSR Addr 0x580ed, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr52
   uint8_t  VMRSData53;       // Byte offset 0x3b5, CSR Addr 0x580ed, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr53
   uint8_t  VMRSData54;       // Byte offset 0x3b6, CSR Addr 0x580ed, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr54
   uint8_t  VMRSData55;       // Byte offset 0x3b7, CSR Addr 0x580ed, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr55
   uint8_t  VMRSData56;       // Byte offset 0x3b8, CSR Addr 0x580ee, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr56
   uint8_t  VMRSData57;       // Byte offset 0x3b9, CSR Addr 0x580ee, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr57
   uint8_t  VMRSData58;       // Byte offset 0x3ba, CSR Addr 0x580ee, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr58
   uint8_t  VMRSData59;       // Byte offset 0x3bb, CSR Addr 0x580ee, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr59
   uint8_t  VMRSData60;       // Byte offset 0x3bc, CSR Addr 0x580ef, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr60
   uint8_t  VMRSData61;       // Byte offset 0x3bd, CSR Addr 0x580ef, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr61
   uint8_t  VMRSData62;       // Byte offset 0x3be, CSR Addr 0x580ef, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr62
   uint8_t  VMRSData63;       // Byte offset 0x3bf, CSR Addr 0x580ef, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr63
   uint8_t  VMRSData64;       // Byte offset 0x3c0, CSR Addr 0x580f0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr64
   uint8_t  VMRSData65;       // Byte offset 0x3c1, CSR Addr 0x580f0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr65
   uint8_t  VMRSData66;       // Byte offset 0x3c2, CSR Addr 0x580f0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr66
   uint8_t  VMRSData67;       // Byte offset 0x3c3, CSR Addr 0x580f0, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr67
   uint8_t  VMRSData68;       // Byte offset 0x3c4, CSR Addr 0x580f1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr68
   uint8_t  VMRSData69;       // Byte offset 0x3c5, CSR Addr 0x580f1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr69
   uint8_t  VMRSData70;       // Byte offset 0x3c6, CSR Addr 0x580f1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr70
   uint8_t  VMRSData71;       // Byte offset 0x3c7, CSR Addr 0x580f1, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr71
   uint8_t  VMRSData72;       // Byte offset 0x3c8, CSR Addr 0x580f2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr72
   uint8_t  VMRSData73;       // Byte offset 0x3c9, CSR Addr 0x580f2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr73
   uint8_t  VMRSData74;       // Byte offset 0x3ca, CSR Addr 0x580f2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr74
   uint8_t  VMRSData75;       // Byte offset 0x3cb, CSR Addr 0x580f2, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr75
   uint8_t  VMRSData76;       // Byte offset 0x3cc, CSR Addr 0x580f3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr76
   uint8_t  VMRSData77;       // Byte offset 0x3cd, CSR Addr 0x580f3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr77
   uint8_t  VMRSData78;       // Byte offset 0x3ce, CSR Addr 0x580f3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr78
   uint8_t  VMRSData79;       // Byte offset 0x3cf, CSR Addr 0x580f3, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr79
   uint8_t  VMRSData80;       // Byte offset 0x3d0, CSR Addr 0x580f4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr80
   uint8_t  VMRSData81;       // Byte offset 0x3d1, CSR Addr 0x580f4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr81
   uint8_t  VMRSData82;       // Byte offset 0x3d2, CSR Addr 0x580f4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr82
   uint8_t  VMRSData83;       // Byte offset 0x3d3, CSR Addr 0x580f4, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr83
   uint8_t  VMRSData84;       // Byte offset 0x3d4, CSR Addr 0x580f5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr84
   uint8_t  VMRSData85;       // Byte offset 0x3d5, CSR Addr 0x580f5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr85
   uint8_t  VMRSData86;       // Byte offset 0x3d6, CSR Addr 0x580f5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr86
   uint8_t  VMRSData87;       // Byte offset 0x3d7, CSR Addr 0x580f5, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr87
   uint8_t  VMRSData88;       // Byte offset 0x3d8, CSR Addr 0x580f6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr88
   uint8_t  VMRSData89;       // Byte offset 0x3d9, CSR Addr 0x580f6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr89
   uint8_t  VMRSData90;       // Byte offset 0x3da, CSR Addr 0x580f6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr90
   uint8_t  VMRSData91;       // Byte offset 0x3db, CSR Addr 0x580f6, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr91
   uint8_t  VMRSData92;       // Byte offset 0x3dc, CSR Addr 0x580f7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr92
   uint8_t  VMRSData93;       // Byte offset 0x3dd, CSR Addr 0x580f7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr93
   uint8_t  VMRSData94;       // Byte offset 0x3de, CSR Addr 0x580f7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr94
   uint8_t  VMRSData95;       // Byte offset 0x3df, CSR Addr 0x580f7, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr95
   uint8_t  VMRSData96;       // Byte offset 0x3e0, CSR Addr 0x580f8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr96
   uint8_t  VMRSData97;       // Byte offset 0x3e1, CSR Addr 0x580f8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr97
   uint8_t  VMRSData98;       // Byte offset 0x3e2, CSR Addr 0x580f8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr98
   uint8_t  VMRSData99;       // Byte offset 0x3e3, CSR Addr 0x580f8, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr99
   uint8_t  VMRSData100;      // Byte offset 0x3e4, CSR Addr 0x580f9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr100
   uint8_t  VMRSData101;      // Byte offset 0x3e5, CSR Addr 0x580f9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr101
   uint8_t  VMRSData102;      // Byte offset 0x3e6, CSR Addr 0x580f9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr102
   uint8_t  VMRSData103;      // Byte offset 0x3e7, CSR Addr 0x580f9, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr103
   uint8_t  VMRSData104;      // Byte offset 0x3e8, CSR Addr 0x580fa, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr104
   uint8_t  VMRSData105;      // Byte offset 0x3e9, CSR Addr 0x580fa, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr105
   uint8_t  VMRSData106;      // Byte offset 0x3ea, CSR Addr 0x580fa, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr106
   uint8_t  VMRSData107;      // Byte offset 0x3eb, CSR Addr 0x580fa, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr107
   uint8_t  VMRSData108;      // Byte offset 0x3ec, CSR Addr 0x580fb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr108
   uint8_t  VMRSData109;      // Byte offset 0x3ed, CSR Addr 0x580fb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr109
   uint8_t  VMRSData110;      // Byte offset 0x3ee, CSR Addr 0x580fb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr110
   uint8_t  VMRSData111;      // Byte offset 0x3ef, CSR Addr 0x580fb, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr111
   uint8_t  VMRSData112;      // Byte offset 0x3f0, CSR Addr 0x580fc, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr112
   uint8_t  VMRSData113;      // Byte offset 0x3f1, CSR Addr 0x580fc, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr113
   uint8_t  VMRSData114;      // Byte offset 0x3f2, CSR Addr 0x580fc, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr114
   uint8_t  VMRSData115;      // Byte offset 0x3f3, CSR Addr 0x580fc, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr115
   uint8_t  VMRSData116;      // Byte offset 0x3f4, CSR Addr 0x580fd, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr116
   uint8_t  VMRSData117;      // Byte offset 0x3f5, CSR Addr 0x580fd, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr117
   uint8_t  VMRSData118;      // Byte offset 0x3f6, CSR Addr 0x580fd, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr118
   uint8_t  VMRSData119;      // Byte offset 0x3f7, CSR Addr 0x580fd, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr119
   uint8_t  VMRSData120;      // Byte offset 0x3f8, CSR Addr 0x580fe, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr120
   uint8_t  VMRSData121;      // Byte offset 0x3f9, CSR Addr 0x580fe, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr121
   uint8_t  VMRSData122;      // Byte offset 0x3fa, CSR Addr 0x580fe, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr122
   uint8_t  VMRSData123;      // Byte offset 0x3fb, CSR Addr 0x580fe, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr123
   uint8_t  VMRSData124;      // Byte offset 0x3fc, CSR Addr 0x580ff, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr124
   uint8_t  VMRSData125;      // Byte offset 0x3fd, CSR Addr 0x580ff, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr125
   uint8_t  VMRSData126;      // Byte offset 0x3fe, CSR Addr 0x580ff, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr126
   uint8_t  VMRSData127;      // Byte offset 0x3ff, CSR Addr 0x580ff, Direction=In
                              // VMRS Data to be written, corresponds to VMRSAddr127
} __attribute__ ((packed)) PMU_SMB_LPDDR5X_1D_t;
