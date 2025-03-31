 const phy_init_data_t phy_init_skiptrain_details[string][] = '{
                  
//[dwc_ddrphy_phyinit_userCustom_A_bringupPower] Start of dwc_ddrphy_phyinit_userCustom_A_bringupPower()
//[dwc_ddrphy_phyinit_userCustom_A_bringupPower] End of dwc_ddrphy_phyinit_userCustom_A_bringupPower()
 
                  
//[dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy] Start of dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy()
//[dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy] End of dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy()
 
   "C" : '{                 
//[phyinit_C_initPhyConfig] Start of dwc_ddrphy_phyinit_C_initPhyConfig()
                          '{ step_type : REG_WRITE, reg_addr : 32'h30022, value : 32'h2}, //[dwc_ddrphy_phyinit_programMemResetL] Programming MemResetL AC0 to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h31022, value : 32'h2}, //[dwc_ddrphy_phyinit_programMemResetL] Programming MemResetL AC1 to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=0, Programming HMAC 4  TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h5070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=0, Programming HMAC 5  TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'hb070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=0, Programming HMAC 11 TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'hc070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=0, Programming HMAC 12 TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h104070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=1, Programming HMAC 4  TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h105070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=1, Programming HMAC 5  TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=1, Programming HMAC 11 TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=1, Programming HMAC 12 TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h204070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=2, Programming HMAC 4  TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h205070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=2, Programming HMAC 5  TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h20b070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=2, Programming HMAC 11 TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h20c070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=2, Programming HMAC 12 TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h304070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=3, Programming HMAC 4  TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h305070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=3, Programming HMAC 5  TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h30b070, value : 32'hff}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=3, Programming HMAC 11 TxImpedanceAC::CS to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h30c070, value : 32'h77}, //[dwc_ddrphy_phyinit_PowerUp] Pstate=3, Programming HMAC 12 TxImpedanceAC::CK to 0x77
                          '{ step_type : REG_WRITE, reg_addr : 32'h5, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC0 Instance0 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC1 Instance1 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC2 Instance2 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC3 Instance3 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h4005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC4 Instance4 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h5005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC5 Instance5 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h7005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC0 Instance7 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h8005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC1 Instance8 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h9005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC2 Instance9 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'ha005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC3 Instance10 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'hb005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC4 Instance11 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC5 Instance12 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'ha0308, value : 32'h2}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMZCAL TxPowerDownZCAL to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'ha0002, value : 32'h1}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMZCAL ZcalPowerCtl.RxPowerDown to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he0046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he0047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he0048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he0049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he1046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he1047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he1048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he1049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he104a, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn4 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he004b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he104b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he2046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he2047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he2048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he2049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he3046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he3047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he3048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he3049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he304a, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn4 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he204b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he304b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he4046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he4047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he4048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he4049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he5046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he5047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he5048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he5049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he504a, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn4 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he404b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he504b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he6046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he6047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he6048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he6049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he7046, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn0 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he7047, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn1 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he7048, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn2 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he7049, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn3 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he704a, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn4 TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he604b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'he704b, value : 32'h6}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownDQS TxPowerDown to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h30020, value : 32'h1}, //[dwc_ddrphy_phyinit_PowerUp] Programming PorControl::PwrOkDlyCtrl to 1'b1
                          '{ step_type : REG_WRITE, reg_addr : 32'h31020, value : 32'h1},
                          '{ step_type : WAIT_DFI, reg_addr : 0, value : 16},
//Calling  [dwc_ddrphy_phyinit_userCustom_wait] to wait 16 DfiClks;
                          '{ step_type : REG_WRITE, reg_addr : 32'h5, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC0 Instance0 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC1 Instance1 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC2 Instance2 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC3 Instance3 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h4005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC4 Instance4 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h5005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX0 HMAC5 Instance5 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h7005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC0 Instance7 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h8005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC1 Instance8 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h9005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC2 Instance9 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'ha005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC3 Instance10 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'hb005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC4 Instance11 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc005, value : 32'h3}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming ACX1 HMAC5 Instance12 RxPowerDownAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'ha0308, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMZCAL TxPowerDownZCAL to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'ha0002, value : 32'h1}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMZCAL ZcalPowerCtl.RxPowerDown to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he0046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he0047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he0048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he0049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he1046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he1047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he1048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he1049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he104a, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownLn4 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he004b, value : 32'h2}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX0 DxRxPowerDownDQS TxPowerDown to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'he104b, value : 32'h4}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE0 DX1 DxRxPowerDownDQS TxPowerDown to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he2046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he2047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he2048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he2049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he3046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he3047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he3048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he3049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he304a, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownLn4 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he204b, value : 32'h2}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX0 DxRxPowerDownDQS TxPowerDown to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'he304b, value : 32'h4}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE1 DX1 DxRxPowerDownDQS TxPowerDown to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he4046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he4047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he4048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he4049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he5046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he5047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he5048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he5049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he504a, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownLn4 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he404b, value : 32'h2}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX0 DxRxPowerDownDQS TxPowerDown to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'he504b, value : 32'h4}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE2 DX1 DxRxPowerDownDQS TxPowerDown to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he6046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he6047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he6048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he6049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he7046, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn0 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he7047, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn1 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he7048, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn2 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he7049, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn3 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he704a, value : 32'h0}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownLn4 TxPowerDown to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he604b, value : 32'h2}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX0 DxRxPowerDownDQS TxPowerDown to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'he704b, value : 32'h4}, //[dwc_ddrphy_phyinit_setTxRxPowerDown] Programming HMDBYTE3 DX1 DxRxPowerDownDQS TxPowerDown to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h200a5, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming LP5Mode to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h10097, value : 32'h7ff}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE0 DxOdtEn to 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h11097, value : 32'h7ff}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE1 DxOdtEn to 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h12097, value : 32'h7ff}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE2 DxOdtEn to 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h13097, value : 32'h7ff}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE3 DxOdtEn to 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE0. TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE0. TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE1. TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE1. TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE2. TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE2. TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE3. TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming DBYTE3. TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb0303, value : 32'h9}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ZCalRate::ZCalOnce to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'ha0302, value : 32'h26}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ZCalCompVref::ZCalDACRangeSel to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb0301, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ZCalBaseCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb030f, value : 32'h1d}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ZCalAnaSettlingTime to 0x1d
                          '{ step_type : REG_WRITE, reg_addr : 32'h300ae, value : 32'h1880}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming AC0.AcLnDisable to 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h300ad, value : 32'h1880}, //phyinit_io_write: 0x300ae, 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h300ac, value : 32'h1880}, //phyinit_io_write: 0x300ad, 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h310ae, value : 32'h1880}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming AC1.AcLnDisable to 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h310ad, value : 32'h1880}, //phyinit_io_write: 0x310ae, 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h310ac, value : 32'h1880}, //phyinit_io_write: 0x310ad, 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h100a3, value : 32'h833}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming PptCtlStatic to 0x833
                          '{ step_type : REG_WRITE, reg_addr : 32'h110a3, value : 32'h83f}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming PptCtlStatic to 0x83f
                          '{ step_type : REG_WRITE, reg_addr : 32'h120a3, value : 32'h833}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming PptCtlStatic to 0x833
                          '{ step_type : REG_WRITE, reg_addr : 32'h130a3, value : 32'h83f}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming PptCtlStatic to 0x83f
                          '{ step_type : REG_WRITE, reg_addr : 32'hc00f0, value : 32'h1111}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat[3]=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h90730, value : 32'h688}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[3]=3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc00f1, value : 32'h2222}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat[7]=2
                          '{ step_type : REG_WRITE, reg_addr : 32'h90731, value : 32'h688}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[7]=3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc00f2, value : 32'h7777}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat[11]=7
                          '{ step_type : REG_WRITE, reg_addr : 32'h90732, value : 32'h688}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[11]=3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc00f3, value : 32'h34}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat[15]=0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90733, value : 32'h2d}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[15]=0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc00f4, value : 32'h5555}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat[19]=5
                          '{ step_type : REG_WRITE, reg_addr : 32'h90734, value : 32'h688}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[19]=3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc00f7, value : 32'hf000}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat[31]=15
                          '{ step_type : REG_WRITE, reg_addr : 32'h90737, value : 32'ha00}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[31]=5
                          '{ step_type : REG_WRITE, reg_addr : 32'h9071f, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming xlat_dp[63]=0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90829, value : 32'hf}, //phyinit_io_write: 0x9071f, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h20007, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming MASTER.PubDbyteDisable to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he007a, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 0 DX4 RxModeX8Sel to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he107a, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 0 DX5 RxModeX8Sel to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he207a, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 1 DX4 RxModeX8Sel to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he307a, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 1 DX5 RxModeX8Sel to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he407a, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 2 DX4 RxModeX8Sel to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he507a, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 2 DX5 RxModeX8Sel to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he607a, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 3 DX4 RxModeX8Sel to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he707a, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE 3 DX5 RxModeX8Sel to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h61e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC0 Instance0 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h161e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC1 Instance1 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h261e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC2 Instance2 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h361e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC3 Instance3 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h461e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC4 Instance4 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h561e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC5 Instance5 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h761e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC0 Instance7 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h861e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC1 Instance8 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h961e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC2 Instance9 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'ha61e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC3 Instance10 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb61e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC4 Instance11 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc61e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC5 Instance12 PclkDCAClkGaterEnAC/DB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10e1f, value : 32'h0}, //phyinit_io_write: 0xc61e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11e1f, value : 32'h0}, //phyinit_io_write: 0x10e1f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12e1f, value : 32'h0}, //phyinit_io_write: 0x11e1f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13e1f, value : 32'h0}, //phyinit_io_write: 0x12e1f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30807, value : 32'hee66}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming PclkDCANextFineOnCoarseAC/DB Full Search to 0xee66
                          '{ step_type : REG_WRITE, reg_addr : 32'h31807, value : 32'hee66}, //phyinit_io_write: 0x30807, 0xee66
                          '{ step_type : REG_WRITE, reg_addr : 32'h10807, value : 32'hee66}, //phyinit_io_write: 0x31807, 0xee66
                          '{ step_type : REG_WRITE, reg_addr : 32'h11807, value : 32'hee66}, //phyinit_io_write: 0x10807, 0xee66
                          '{ step_type : REG_WRITE, reg_addr : 32'h12807, value : 32'hee66}, //phyinit_io_write: 0x11807, 0xee66
                          '{ step_type : REG_WRITE, reg_addr : 32'h13807, value : 32'hee66}, //phyinit_io_write: 0x12807, 0xee66
                          '{ step_type : REG_WRITE, reg_addr : 32'h300a0, value : 32'h3fff}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming AC0.AsyncAcTxMode to 0x3fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h310a0, value : 32'h3fff}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming AC1.AsyncAcTxMode to 0x3fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h10089, value : 32'h1fff}, //phyinit_io_write: 0x310a0, 0x3fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h1008a, value : 32'h7ff}, //phyinit_io_write: 0x10089, 0x1fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h11089, value : 32'h1fff}, //phyinit_io_write: 0x1008a, 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h1108a, value : 32'h7ff}, //phyinit_io_write: 0x11089, 0x1fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h12089, value : 32'h1fff}, //phyinit_io_write: 0x1108a, 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h1208a, value : 32'h7ff}, //phyinit_io_write: 0x12089, 0x1fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h13089, value : 32'h1fff}, //phyinit_io_write: 0x1208a, 0x7ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h1308a, value : 32'h7ff}, //phyinit_io_write: 0x13089, 0x1fff
                          '{ step_type : REG_WRITE, reg_addr : 32'h20006, value : 32'hf}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming LpDqPhaseDisable to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h2000c, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming PipeNetDis to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he000d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE0 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he100d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE1 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he200d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE2 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he300d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE3 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he400d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE4 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he500d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE5 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he600d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE6 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he700d, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming HMDBYTE7 RxGainCtrl to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h30027, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACDlyScaleGatingDisable AC0 to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC0 Instance0 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h103f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC1 Instance1 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h203f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC2 Instance2 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h303f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC3 Instance3 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h403f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC4 Instance4 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h503f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX0 HMAC5 Instance5 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h31027, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACDlyScaleGatingDisable AC1 to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h703f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC0 Instance7 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h803f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC1 Instance8 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h903f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC2 Instance9 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'ha03f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC3 Instance10 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'hb03f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC4 Instance11 to NeverGateACDlyScaleValClk 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'hc03f, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfig] Programming ACX1 HMAC5 Instance12 to NeverGateACDlyScaleValClk 0x1
//[dwc_ddrphy_phyinit_programDfiMode] Skip DfiMode Programming: Keeping the reset value of 0x3
//[phyinit_C_initPhyConfig] End of dwc_ddrphy_phyinit_C_initPhyConfig()
// [dwc_ddrphy_phyinit_getPsExecOrder] pRuntimeConfig->psExecOrder[3] = 0x0
//Start of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), PState=1, tck_ps=1666ps
                          '{ step_type : REG_WRITE, reg_addr : 32'h2008b, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, programming PState = 1
                          '{ step_type : REG_WRITE, reg_addr : 32'h190801, value : 32'hc0a2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming Seq0BGPR1 to 0xc0a2
                          '{ step_type : REG_WRITE, reg_addr : 32'h190802, value : 32'h0}, //phyinit_io_write: 0x190801, 0xc0a2
                          '{ step_type : REG_WRITE, reg_addr : 32'h190806, value : 32'h1}, //phyinit_io_write: 0x190802, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1a03ff, value : 32'h4101}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming OdtSeg120 to 0x4101
                          '{ step_type : REG_WRITE, reg_addr : 32'h1a030b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming ZCalCompCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h160008, value : 32'ha9a}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_C_initPhyConfigPsLoop] Pstate=1,  Memclk=600MHz, Programming CpllCtrl5 to 0xa9a.
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e0, value : 32'h4b}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY0 to 0x4b (0.5us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e1, value : 32'he1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY1 to 0xe1 (tZQCal PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e2, value : 32'h5dc}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY2 to 0x5dc (10.us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e3, value : 32'h58}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY3 to 0x58 (dllLock PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e4, value : 32'hf}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY4 to 0xf (0.1us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e5, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY5 to 0x0 (RxReplicaCalWait delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e6, value : 32'h43}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY6 to 0x43 (Oscillator PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e7, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY7 to 0x0 (tXDSM_XP PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908ea, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY10 to 0x3 (tPDXCSODTON 20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908eb, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY11 to 0x3 (20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908ec, value : 32'h8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY12 to 0x8 (50ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908ed, value : 32'h3b}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming Seq0BDLY13 to 0x3b (tXSR PIE delay, tRFCab delay is 380ns)
                          '{ step_type : REG_WRITE, reg_addr : 32'h120002, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming PclkPtrInitVal to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h160040, value : 32'h3}, //phyinit_io_write: 0x120002, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h120000, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DfiFreqRatio to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h1100fb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming RxDigStrbEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1110fb, value : 32'h0}, //phyinit_io_write: 0x1100fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1120fb, value : 32'h0}, //phyinit_io_write: 0x1110fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1130fb, value : 32'h0}, //phyinit_io_write: 0x1120fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e000b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DxDigStrobeMode HMDBYTE to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e100b, value : 32'h0}, //phyinit_io_write: 0x1e000b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e200b, value : 32'h0}, //phyinit_io_write: 0x1e100b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e300b, value : 32'h0}, //phyinit_io_write: 0x1e200b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e400b, value : 32'h0}, //phyinit_io_write: 0x1e300b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e500b, value : 32'h0}, //phyinit_io_write: 0x1e400b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e600b, value : 32'h0}, //phyinit_io_write: 0x1e500b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e700b, value : 32'h0}, //phyinit_io_write: 0x1e600b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h110024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE0.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h111024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE1.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE2.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h113024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE3.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h110025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE0.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h111025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE1.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h112025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE2.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h113025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE3.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h110004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE0.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h110003, value : 32'h0}, //phyinit_io_write: 0x110004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h111004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE1.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h111003, value : 32'h0}, //phyinit_io_write: 0x111004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE2.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112003, value : 32'h0}, //phyinit_io_write: 0x112004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h113004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE3.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h113003, value : 32'h0}, //phyinit_io_write: 0x113004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1b0004, value : 32'h258}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ZCalClkInfo::ZCalDfiClkTicksPer1uS to 0x258
                          '{ step_type : REG_WRITE, reg_addr : 32'h1a030c, value : 32'h0},
                          '{ step_type : REG_WRITE, reg_addr : 32'h11003e, value : 32'h5}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE RxGainCurrAdjRxReplica to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h11103e, value : 32'h5}, //phyinit_io_write: 0x11003e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h11203e, value : 32'h5}, //phyinit_io_write: 0x11103e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h11303e, value : 32'h5}, //phyinit_io_write: 0x11203e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h120003, value : 32'h1}, //phyinit_io_write: 0x11303e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h12000b, value : 32'h1111}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming CPclkDivRatio to 0x1111
                          '{ step_type : REG_WRITE, reg_addr : 32'h110108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE0.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h111108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE1.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE2.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h113108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming DBYTE3.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70005, value : 32'h0}, //[phyinit_C_initPhyConfig] Programming EnPhyUpdZQCalUpdate to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h7000f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming DisableZQupdateOnSnoop to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11000e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h11100e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h11200e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h11300e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h120019, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming EnRxDqsTracking::DqsSampNegRxEnSense to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e002c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e102c, value : 32'h33}, //phyinit_io_write: 0x1e002c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e002d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e102d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e202c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e302c, value : 32'h33}, //phyinit_io_write: 0x1e202c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e202d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e302d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e402c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e502c, value : 32'h33}, //phyinit_io_write: 0x1e402c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e402d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e502d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e602c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e702c, value : 32'h33}, //phyinit_io_write: 0x1e602c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e602d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e702d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h100070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC0 Instance0 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h101070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC1 Instance1 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h102070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC2 Instance2 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h103070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC3 Instance3 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h104070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming AC0 HMAC4 Instance4 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h105070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC5 Instance5 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h107070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC0 Instance7 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h108070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC1 Instance8 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h109070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC2 Instance9 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC3 Instance10 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming AC1 HMAC4 Instance11 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC5 Instance12 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e002e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e102e, value : 32'h30}, //phyinit_io_write: 0x1e002e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e002f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e102f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e202e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e302e, value : 32'h30}, //phyinit_io_write: 0x1e202e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e202f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e302f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e402e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e502e, value : 32'h30}, //phyinit_io_write: 0x1e402e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e402f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e502f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e602e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e702e, value : 32'h30}, //phyinit_io_write: 0x1e602e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e602f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e702f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h100079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC0 Instance0 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h101079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC1 Instance1 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h102079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC2 Instance2 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h103079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC3 Instance3 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h104079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC4 Instance4 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h105079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC5 DIFF5 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h107079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC0 Instance7 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h108079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC1 Instance8 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h109079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC2 Instance9 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC3 Instance10 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC4 Instance11 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC5 DIFF12 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e001c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 0 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e101c, value : 32'h3}, //phyinit_io_write: 0x1e001c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e201c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 1 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e301c, value : 32'h3}, //phyinit_io_write: 0x1e201c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e401c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 2 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e501c, value : 32'h3}, //phyinit_io_write: 0x1e401c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e601c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming HMDBYTE 3 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e701c, value : 32'h3}, //phyinit_io_write: 0x1e601c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h10006d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC0 Instance0 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10106d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC1 Instance1 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10206d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC2 Instance2 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10306d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC3 Instance3 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10406d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC4 Instance4 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h10506d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX0 HMAC5 Instance5 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10706d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC0 Instance7 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10806d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC1 Instance8 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10906d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC2 Instance9 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC3 Instance10 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b06d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC4 Instance11 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACX1 HMAC5 Instance12 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e003e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming HMDBYTE RxDQSCtrl::RxDQSDiffSeVrefDACEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e103e, value : 32'h0}, //phyinit_io_write: 0x1e003e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e203e, value : 32'h0}, //phyinit_io_write: 0x1e103e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e303e, value : 32'h0}, //phyinit_io_write: 0x1e203e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e403e, value : 32'h0}, //phyinit_io_write: 0x1e303e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e503e, value : 32'h0}, //phyinit_io_write: 0x1e403e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e603e, value : 32'h0}, //phyinit_io_write: 0x1e503e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e703e, value : 32'h0}, //phyinit_io_write: 0x1e603e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h110001, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming WriteLinkEcc to 0
                          '{ step_type : REG_WRITE, reg_addr : 32'h111001, value : 32'h0}, //phyinit_io_write: 0x110001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112001, value : 32'h0}, //phyinit_io_write: 0x111001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h113001, value : 32'h0}, //phyinit_io_write: 0x112001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h170040, value : 32'h5a}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming PPTTrainSetup::PhyMstrMaxReqToAck to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h170041, value : 32'hf}, //phyinit_io_write: 0x170040, 0x5a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1100a5, value : 32'h1}, //phyinit_io_write: 0x170041, 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h1110a5, value : 32'h1}, //phyinit_io_write: 0x1100a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1120a5, value : 32'h1}, //phyinit_io_write: 0x1110a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1130a5, value : 32'h1}, //phyinit_io_write: 0x1120a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h110209, value : 32'h3232}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming RxReplicaRangeVal 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h111209, value : 32'h3232}, //phyinit_io_write: 0x110209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h112209, value : 32'h3232}, //phyinit_io_write: 0x111209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h113209, value : 32'h3232}, //phyinit_io_write: 0x112209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h11020f, value : 32'h6}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming RxReplicaCtl04 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h11120f, value : 32'h6}, //phyinit_io_write: 0x11020f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h11220f, value : 32'h6}, //phyinit_io_write: 0x11120f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h11320f, value : 32'h6}, //phyinit_io_write: 0x11220f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h120005, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, DfiFreq=600MHz, Programming PipeCtl[AcInPipeEn]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h110008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, DfiFreq=600MHz, Programming DBYTE0.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h111008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, DfiFreq=600MHz, Programming DBYTE1.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h112008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, DfiFreq=600MHz, Programming DBYTE2.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h113008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, DfiFreq=600MHz, Programming DBYTE3.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h17006b, value : 32'h222}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, DfiFreq=600MHz, Programming DfiHandshakeDelays[PhyUpdReqDelay]=0x2 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h170066, value : 32'h20}, //phyinit_io_write: 0x17006b, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h1700eb, value : 32'h222}, //phyinit_io_write: 0x170066, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h1700e6, value : 32'h20}, //phyinit_io_write: 0x1700eb, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h170135, value : 32'hc08}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth to 0x19, ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleDelay to 0x18
                          '{ step_type : REG_WRITE, reg_addr : 32'h170136, value : 32'hc08}, //phyinit_io_write: 0x170135, 0xc08
                          '{ step_type : REG_WRITE, reg_addr : 32'h170137, value : 32'h414}, //phyinit_io_write: 0x170136, 0xc08
                          '{ step_type : REG_WRITE, reg_addr : 32'h170138, value : 32'h1918}, //phyinit_io_write: 0x170137, 0x414
                          '{ step_type : REG_WRITE, reg_addr : 32'h170139, value : 32'hc10}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleWidth to 0x29, ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleDelay to 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h17013a, value : 32'hc10}, //phyinit_io_write: 0x170139, 0xc10
                          '{ step_type : REG_WRITE, reg_addr : 32'h17013b, value : 32'h41c}, //phyinit_io_write: 0x17013a, 0xc10
                          '{ step_type : REG_WRITE, reg_addr : 32'h17013c, value : 32'h2920}, //phyinit_io_write: 0x17013b, 0x41c
                          '{ step_type : REG_WRITE, reg_addr : 32'h17013d, value : 32'hc04}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleWidth to 0x11, ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleDelay to 0x14
                          '{ step_type : REG_WRITE, reg_addr : 32'h17013e, value : 32'hc04}, //phyinit_io_write: 0x17013d, 0xc04
                          '{ step_type : REG_WRITE, reg_addr : 32'h17013f, value : 32'h410}, //phyinit_io_write: 0x17013e, 0xc04
                          '{ step_type : REG_WRITE, reg_addr : 32'h170140, value : 32'h1114}, //phyinit_io_write: 0x17013f, 0x410
                          '{ step_type : REG_WRITE, reg_addr : 32'h17012c, value : 32'h827}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMRxValPulse::ACSMRxValDelay to 0x27, ACSMRxValPulse::ACSMRxValWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h17012d, value : 32'h827}, //phyinit_io_write: 0x17012c, 0x827
                          '{ step_type : REG_WRITE, reg_addr : 32'h170130, value : 32'h827}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMRdcsPulse::ACSMRdcsDelay to 0x27, ACSMRdcsPulse::ACSMRdcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h17012e, value : 32'h817}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMTxEnPulse::ACSMTxEnDelay to 0x17, ACSMTxEnPulse::ACSMTxEnWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h17012f, value : 32'h817}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming ACSMWrcsPulse::ACSMWrcsDelay to 0x17, ACSMWrcsPulse::ACSMWrcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h130008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming AcPipeEn AC0 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h131008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, Programming AcPipeEn AC1 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1013, value : 32'h0}, //phyinit_io_write: 0x1e0013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3013, value : 32'h0}, //phyinit_io_write: 0x1e2013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5013, value : 32'h0}, //phyinit_io_write: 0x1e4013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7013, value : 32'h0}, //phyinit_io_write: 0x1e6013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1005e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC0 Instance0 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1015e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC1 Instance1 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1025e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC2 Instance2 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1035e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC3 Instance3 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1045e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC4 Instance4 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1055e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC5 Instance5 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1075e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC0 Instance7 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1085e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC1 Instance8 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1095e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC2 Instance9 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC3 Instance10 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC4 Instance11 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC5 Instance12 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e05e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE0 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e15e3, value : 32'h4}, //phyinit_io_write: 0x1e05e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e25e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE1 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e35e3, value : 32'h4}, //phyinit_io_write: 0x1e25e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e45e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE2 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e55e3, value : 32'h4}, //phyinit_io_write: 0x1e45e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e65e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE3 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e75e3, value : 32'h4}, //phyinit_io_write: 0x1e65e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h10050a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC0 Instance0 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10150a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC1 Instance1 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10250a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC2 Instance2 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10350a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC3 Instance3 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10450a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC4 Instance4 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10550a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC5 Instance5 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10750a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC0 Instance7 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10850a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC1 Instance8 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10950a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC2 Instance9 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC3 Instance10 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC4 Instance11 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC5 Instance12 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11080b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE0 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11180b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE1 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11280b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE2 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11380b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE3 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h130803, value : 32'h105a}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming PclkDCAStaticCtr0AC to 0x105a
                          '{ step_type : REG_WRITE, reg_addr : 32'h131803, value : 32'h105a}, //phyinit_io_write: 0x130803, 0x105a
                          '{ step_type : REG_WRITE, reg_addr : 32'h110803, value : 32'h105a}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming PclkDCAStaticCtr0DB to 0x105a
                          '{ step_type : REG_WRITE, reg_addr : 32'h111803, value : 32'h105a}, //phyinit_io_write: 0x110803, 0x105a
                          '{ step_type : REG_WRITE, reg_addr : 32'h112803, value : 32'h105a}, //phyinit_io_write: 0x111803, 0x105a
                          '{ step_type : REG_WRITE, reg_addr : 32'h113803, value : 32'h105a}, //phyinit_io_write: 0x112803, 0x105a
                          '{ step_type : REG_WRITE, reg_addr : 32'h100503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC0 Instance0 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h101503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC1 Instance1 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h102503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC2 Instance2 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h103503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC3 Instance3 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h104503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC4 Instance4 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h105503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC5 Instance5 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h107503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC0 Instance7 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h108503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC1 Instance8 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h109503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC2 Instance9 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC3 Instance10 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC4 Instance11 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c503, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC5 Instance12 PclkDCAStaticCtrl1AC to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h110c03, value : 32'h1b}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming PclkDCAStaticCtrl1DB to 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h111c03, value : 32'h1b}, //phyinit_io_write: 0x110c03, 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h112c03, value : 32'h1b}, //phyinit_io_write: 0x111c03, 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h113c03, value : 32'h1b}, //phyinit_io_write: 0x112c03, 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h100110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC0 Instance0 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h101110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC1 Instance1 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h102110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC2 Instance2 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h103110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC3 Instance3 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h104110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC4 Instance4 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h105110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX0 HMAC5 Instance5 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h107110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC0 Instance7 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h108110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC1 Instance8 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h109110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC2 Instance9 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC3 Instance10 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC4 Instance11 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming ACX1 HMAC5 Instance12 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE0 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1110, value : 32'h1f}, //phyinit_io_write: 0x1e0110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE1 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3110, value : 32'h1f}, //phyinit_io_write: 0x1e2110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE2 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5110, value : 32'h1f}, //phyinit_io_write: 0x1e4110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming HMDBYTE3 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7110, value : 32'h1f}, //phyinit_io_write: 0x1e6110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e8, value : 32'h11}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=1, Programming Seq0BDLY9 to 57
                          '{ step_type : REG_WRITE, reg_addr : 32'h1908e9, value : 32'h39}, //phyinit_io_write: 0x1908e8, 0x11
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0002, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Programming HMDBYTE RxDFECtrlDq to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1002, value : 32'h0}, //phyinit_io_write: 0x1e0002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2002, value : 32'h0}, //phyinit_io_write: 0x1e1002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3002, value : 32'h0}, //phyinit_io_write: 0x1e2002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4002, value : 32'h0}, //phyinit_io_write: 0x1e3002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5002, value : 32'h0}, //phyinit_io_write: 0x1e4002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6002, value : 32'h0}, //phyinit_io_write: 0x1e5002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7002, value : 32'h0}, //phyinit_io_write: 0x1e6002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11010b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=1, Memclk=600MHz, freqThreshold=200MHz, NoRDQS=0 Programming InhibitTxRdPtrInit::DisableRxEnDlyLoad to 0x0, InhibitTxRdPtrInit::DisableTxDqDly to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11110b, value : 32'h0}, //phyinit_io_write: 0x11010b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11210b, value : 32'h0}, //phyinit_io_write: 0x11110b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11310b, value : 32'h0}, //phyinit_io_write: 0x11210b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h100063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h101063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h102063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h103063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h104063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h105063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h107063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h108063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h109063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c063, value : 32'h8a}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0x8a HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080a, value : 32'h28a}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR10 to HMTxLcdlSeed Full search value = 0x28a
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080b, value : 32'h8a}, //phyinit_io_write: 0x19080a, 0x28a
                          '{ step_type : REG_WRITE, reg_addr : 32'h190815, value : 32'h28a}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR21 to ACHMTxLcdlSeed Full search value = 0x28a
                          '{ step_type : REG_WRITE, reg_addr : 32'h190816, value : 32'h8a}, //phyinit_io_write: 0x190815, 0x28a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0063, value : 32'h8a}, //phyinit_io_write: 0x190816, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0064, value : 32'h8a}, //phyinit_io_write: 0x1e0063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0087, value : 32'h8a}, //phyinit_io_write: 0x1e0064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1063, value : 32'h8a}, //phyinit_io_write: 0x1e0087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1064, value : 32'h8a}, //phyinit_io_write: 0x1e1063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1087, value : 32'h8a}, //phyinit_io_write: 0x1e1064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2063, value : 32'h8a}, //phyinit_io_write: 0x1e1087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2064, value : 32'h8a}, //phyinit_io_write: 0x1e2063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2087, value : 32'h8a}, //phyinit_io_write: 0x1e2064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3063, value : 32'h8a}, //phyinit_io_write: 0x1e2087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3064, value : 32'h8a}, //phyinit_io_write: 0x1e3063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3087, value : 32'h8a}, //phyinit_io_write: 0x1e3064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4063, value : 32'h8a}, //phyinit_io_write: 0x1e3087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4064, value : 32'h8a}, //phyinit_io_write: 0x1e4063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4087, value : 32'h8a}, //phyinit_io_write: 0x1e4064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5063, value : 32'h8a}, //phyinit_io_write: 0x1e4087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5064, value : 32'h8a}, //phyinit_io_write: 0x1e5063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5087, value : 32'h8a}, //phyinit_io_write: 0x1e5064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6063, value : 32'h8a}, //phyinit_io_write: 0x1e5087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6064, value : 32'h8a}, //phyinit_io_write: 0x1e6063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6087, value : 32'h8a}, //phyinit_io_write: 0x1e6064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7063, value : 32'h8a}, //phyinit_io_write: 0x1e6087, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7064, value : 32'h8a}, //phyinit_io_write: 0x1e7063, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7087, value : 32'h8a}, //phyinit_io_write: 0x1e7064, 0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'hc0080, value : 32'h7}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming UcclkHclkEnables to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e003c, value : 32'h80}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming RxDQSSeVrefDAC0 to 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e103c, value : 32'h80}, //phyinit_io_write: 0x1e003c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e203c, value : 32'h80}, //phyinit_io_write: 0x1e103c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e303c, value : 32'h80}, //phyinit_io_write: 0x1e203c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e403c, value : 32'h80}, //phyinit_io_write: 0x1e303c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e503c, value : 32'h80}, //phyinit_io_write: 0x1e403c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e603c, value : 32'h80}, //phyinit_io_write: 0x1e503c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e703c, value : 32'h80}, //phyinit_io_write: 0x1e603c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h190817, value : 32'h3e}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 1 Seq0BGPR23 to 0x3e, NumMemClk_tRFCab=246.0, NumMemClk_7p5ns=4.5, NumMemClk_tXSR=250.5
                          '{ step_type : REG_WRITE, reg_addr : 32'h190818, value : 32'h0}, //phyinit_io_write: 0x190817, 0x3e
                          '{ step_type : REG_WRITE, reg_addr : 32'h190819, value : 32'h0}, //phyinit_io_write: 0x190818, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1300eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 1 AC0 AcLcdlUpdInterval to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1310eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 1 AC1 AcLcdlUpdInterval to 0x0
//[dwc_ddrphy_phyinit_programDfiMode] Skip DfiMode Programming: Keeping the reset value of 0x3
//End of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), Pstate=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h60006, value : 32'h3f0}, //[dwc_ddrphy_phyinit_progCsrSkipTrain] Programming CPllCtrl3 to 0x3f0
                          '{ step_type : REG_WRITE, reg_addr : 32'h100d9, value : 32'h9c}, //[dwc_ddrphy_phyinit_progCsrSkipTrain] RxReplica Programming RxReplicaUICalWait to 0x9c
                          '{ step_type : REG_WRITE, reg_addr : 32'h110d9, value : 32'h9c}, //phyinit_io_write: 0x100d9, 0x9c
                          '{ step_type : REG_WRITE, reg_addr : 32'h120d9, value : 32'h9c}, //phyinit_io_write: 0x110d9, 0x9c
                          '{ step_type : REG_WRITE, reg_addr : 32'h130d9, value : 32'h9c}, //phyinit_io_write: 0x120d9, 0x9c
                          '{ step_type : REG_WRITE, reg_addr : 32'h10027, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrain] Programming RxClkCntl1 to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h11027, value : 32'h1}, //phyinit_io_write: 0x10027, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h12027, value : 32'h1}, //phyinit_io_write: 0x11027, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h13027, value : 32'h1}, //phyinit_io_write: 0x12027, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h30022, value : 32'h3}, // [dwc_ddrphy_phyinit_programMemResetL] Programming MemResetL AC 0to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h31022, value : 32'h3}, // [dwc_ddrphy_phyinit_programMemResetL] Programming MemResetL AC 1to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1300d9, value : 32'h40}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming CKXTxDly to 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1300d8, value : 32'h40}, //phyinit_io_write: 0x1300d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1301d8, value : 32'h40}, //phyinit_io_write: 0x1300d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1302d8, value : 32'h40}, //phyinit_io_write: 0x1301d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303d8, value : 32'h40}, //phyinit_io_write: 0x1302d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1304d8, value : 32'h40}, //phyinit_io_write: 0x1303d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1305d8, value : 32'h40}, //phyinit_io_write: 0x1304d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1306d8, value : 32'h40}, //phyinit_io_write: 0x1305d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1308d8, value : 32'h40}, //phyinit_io_write: 0x1306d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1309d8, value : 32'h40}, //phyinit_io_write: 0x1308d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1310d9, value : 32'h40}, //phyinit_io_write: 0x1309d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1310d8, value : 32'h40}, //phyinit_io_write: 0x1310d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1311d8, value : 32'h40}, //phyinit_io_write: 0x1310d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1312d8, value : 32'h40}, //phyinit_io_write: 0x1311d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1313d8, value : 32'h40}, //phyinit_io_write: 0x1312d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1314d8, value : 32'h40}, //phyinit_io_write: 0x1313d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1315d8, value : 32'h40}, //phyinit_io_write: 0x1314d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1316d8, value : 32'h40}, //phyinit_io_write: 0x1315d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1318d8, value : 32'h40}, //phyinit_io_write: 0x1316d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h1319d8, value : 32'h40}, //phyinit_io_write: 0x1318d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h110000, value : 32'h7}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming HwtMRL to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h111000, value : 32'h7}, //phyinit_io_write: 0x110000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h112000, value : 32'h7}, //phyinit_io_write: 0x111000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h113000, value : 32'h7}, //phyinit_io_write: 0x112000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h17000d, value : 32'h7}, //phyinit_io_write: 0x113000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h11002a, value : 32'h200}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming TxWckDlyTg0/Tg1 to 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11002b, value : 32'h200}, //phyinit_io_write: 0x11002a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11102a, value : 32'h200}, //phyinit_io_write: 0x11002b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11102b, value : 32'h200}, //phyinit_io_write: 0x11102a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11202a, value : 32'h200}, //phyinit_io_write: 0x11102b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11202b, value : 32'h200}, //phyinit_io_write: 0x11202a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11302a, value : 32'h200}, //phyinit_io_write: 0x11202b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h11302b, value : 32'h200}, //phyinit_io_write: 0x11302a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h110028, value : 32'hba}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming TxDqsDlyTg0/Tg1 to 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h110029, value : 32'hba}, //phyinit_io_write: 0x110028, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h111028, value : 32'hba}, //phyinit_io_write: 0x110029, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h111029, value : 32'hba}, //phyinit_io_write: 0x111028, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h112028, value : 32'hba}, //phyinit_io_write: 0x111029, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h112029, value : 32'hba}, //phyinit_io_write: 0x112028, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h113028, value : 32'hba}, //phyinit_io_write: 0x112029, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h113029, value : 32'hba}, //phyinit_io_write: 0x113028, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11007a, value : 32'hba}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming TxDqDlyTg0/Tg1 to 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11007b, value : 32'hba}, //phyinit_io_write: 0x11007a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11017a, value : 32'hba}, //phyinit_io_write: 0x11007b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11017b, value : 32'hba}, //phyinit_io_write: 0x11017a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11027a, value : 32'hba}, //phyinit_io_write: 0x11017b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11027b, value : 32'hba}, //phyinit_io_write: 0x11027a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11037a, value : 32'hba}, //phyinit_io_write: 0x11027b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11037b, value : 32'hba}, //phyinit_io_write: 0x11037a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11047a, value : 32'hba}, //phyinit_io_write: 0x11037b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11047b, value : 32'hba}, //phyinit_io_write: 0x11047a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11057a, value : 32'hba}, //phyinit_io_write: 0x11047b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11057b, value : 32'hba}, //phyinit_io_write: 0x11057a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11067a, value : 32'hba}, //phyinit_io_write: 0x11057b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11067b, value : 32'hba}, //phyinit_io_write: 0x11067a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11077a, value : 32'hba}, //phyinit_io_write: 0x11067b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11077b, value : 32'hba}, //phyinit_io_write: 0x11077a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11087a, value : 32'hba}, //phyinit_io_write: 0x11077b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11087b, value : 32'hba}, //phyinit_io_write: 0x11087a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11107a, value : 32'hba}, //phyinit_io_write: 0x11087b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11107b, value : 32'hba}, //phyinit_io_write: 0x11107a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11117a, value : 32'hba}, //phyinit_io_write: 0x11107b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11117b, value : 32'hba}, //phyinit_io_write: 0x11117a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11127a, value : 32'hba}, //phyinit_io_write: 0x11117b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11127b, value : 32'hba}, //phyinit_io_write: 0x11127a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11137a, value : 32'hba}, //phyinit_io_write: 0x11127b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11137b, value : 32'hba}, //phyinit_io_write: 0x11137a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11147a, value : 32'hba}, //phyinit_io_write: 0x11137b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11147b, value : 32'hba}, //phyinit_io_write: 0x11147a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11157a, value : 32'hba}, //phyinit_io_write: 0x11147b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11157b, value : 32'hba}, //phyinit_io_write: 0x11157a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11167a, value : 32'hba}, //phyinit_io_write: 0x11157b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11167b, value : 32'hba}, //phyinit_io_write: 0x11167a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11177a, value : 32'hba}, //phyinit_io_write: 0x11167b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11177b, value : 32'hba}, //phyinit_io_write: 0x11177a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11187a, value : 32'hba}, //phyinit_io_write: 0x11177b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11187b, value : 32'hba}, //phyinit_io_write: 0x11187a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11207a, value : 32'hba}, //phyinit_io_write: 0x11187b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11207b, value : 32'hba}, //phyinit_io_write: 0x11207a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11217a, value : 32'hba}, //phyinit_io_write: 0x11207b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11217b, value : 32'hba}, //phyinit_io_write: 0x11217a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11227a, value : 32'hba}, //phyinit_io_write: 0x11217b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11227b, value : 32'hba}, //phyinit_io_write: 0x11227a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11237a, value : 32'hba}, //phyinit_io_write: 0x11227b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11237b, value : 32'hba}, //phyinit_io_write: 0x11237a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11247a, value : 32'hba}, //phyinit_io_write: 0x11237b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11247b, value : 32'hba}, //phyinit_io_write: 0x11247a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11257a, value : 32'hba}, //phyinit_io_write: 0x11247b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11257b, value : 32'hba}, //phyinit_io_write: 0x11257a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11267a, value : 32'hba}, //phyinit_io_write: 0x11257b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11267b, value : 32'hba}, //phyinit_io_write: 0x11267a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11277a, value : 32'hba}, //phyinit_io_write: 0x11267b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11277b, value : 32'hba}, //phyinit_io_write: 0x11277a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11287a, value : 32'hba}, //phyinit_io_write: 0x11277b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11287b, value : 32'hba}, //phyinit_io_write: 0x11287a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11307a, value : 32'hba}, //phyinit_io_write: 0x11287b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11307b, value : 32'hba}, //phyinit_io_write: 0x11307a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11317a, value : 32'hba}, //phyinit_io_write: 0x11307b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11317b, value : 32'hba}, //phyinit_io_write: 0x11317a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11327a, value : 32'hba}, //phyinit_io_write: 0x11317b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11327b, value : 32'hba}, //phyinit_io_write: 0x11327a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11337a, value : 32'hba}, //phyinit_io_write: 0x11327b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11337b, value : 32'hba}, //phyinit_io_write: 0x11337a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11347a, value : 32'hba}, //phyinit_io_write: 0x11337b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11347b, value : 32'hba}, //phyinit_io_write: 0x11347a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11357a, value : 32'hba}, //phyinit_io_write: 0x11347b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11357b, value : 32'hba}, //phyinit_io_write: 0x11357a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11367a, value : 32'hba}, //phyinit_io_write: 0x11357b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11367b, value : 32'hba}, //phyinit_io_write: 0x11367a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11377a, value : 32'hba}, //phyinit_io_write: 0x11367b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11377b, value : 32'hba}, //phyinit_io_write: 0x11377a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11387a, value : 32'hba}, //phyinit_io_write: 0x11377b, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h11387b, value : 32'hba}, //phyinit_io_write: 0x11387a, 0xba
                          '{ step_type : REG_WRITE, reg_addr : 32'h110078, value : 32'h352}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming RxDigStrbDlyTg0/Tg1 to 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110079, value : 32'h352}, //phyinit_io_write: 0x110078, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110178, value : 32'h352}, //phyinit_io_write: 0x110079, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110179, value : 32'h352}, //phyinit_io_write: 0x110178, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110278, value : 32'h352}, //phyinit_io_write: 0x110179, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110279, value : 32'h352}, //phyinit_io_write: 0x110278, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110378, value : 32'h352}, //phyinit_io_write: 0x110279, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110379, value : 32'h352}, //phyinit_io_write: 0x110378, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110478, value : 32'h352}, //phyinit_io_write: 0x110379, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110479, value : 32'h352}, //phyinit_io_write: 0x110478, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110578, value : 32'h352}, //phyinit_io_write: 0x110479, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110579, value : 32'h352}, //phyinit_io_write: 0x110578, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110678, value : 32'h352}, //phyinit_io_write: 0x110579, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110679, value : 32'h352}, //phyinit_io_write: 0x110678, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110778, value : 32'h352}, //phyinit_io_write: 0x110679, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110779, value : 32'h352}, //phyinit_io_write: 0x110778, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110878, value : 32'h352}, //phyinit_io_write: 0x110779, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110879, value : 32'h352}, //phyinit_io_write: 0x110878, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111078, value : 32'h352}, //phyinit_io_write: 0x110879, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111079, value : 32'h352}, //phyinit_io_write: 0x111078, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111178, value : 32'h352}, //phyinit_io_write: 0x111079, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111179, value : 32'h352}, //phyinit_io_write: 0x111178, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111278, value : 32'h352}, //phyinit_io_write: 0x111179, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111279, value : 32'h352}, //phyinit_io_write: 0x111278, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111378, value : 32'h352}, //phyinit_io_write: 0x111279, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111379, value : 32'h352}, //phyinit_io_write: 0x111378, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111478, value : 32'h352}, //phyinit_io_write: 0x111379, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111479, value : 32'h352}, //phyinit_io_write: 0x111478, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111578, value : 32'h352}, //phyinit_io_write: 0x111479, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111579, value : 32'h352}, //phyinit_io_write: 0x111578, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111678, value : 32'h352}, //phyinit_io_write: 0x111579, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111679, value : 32'h352}, //phyinit_io_write: 0x111678, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111778, value : 32'h352}, //phyinit_io_write: 0x111679, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111779, value : 32'h352}, //phyinit_io_write: 0x111778, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111878, value : 32'h352}, //phyinit_io_write: 0x111779, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h111879, value : 32'h352}, //phyinit_io_write: 0x111878, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112078, value : 32'h352}, //phyinit_io_write: 0x111879, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112079, value : 32'h352}, //phyinit_io_write: 0x112078, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112178, value : 32'h352}, //phyinit_io_write: 0x112079, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112179, value : 32'h352}, //phyinit_io_write: 0x112178, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112278, value : 32'h352}, //phyinit_io_write: 0x112179, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112279, value : 32'h352}, //phyinit_io_write: 0x112278, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112378, value : 32'h352}, //phyinit_io_write: 0x112279, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112379, value : 32'h352}, //phyinit_io_write: 0x112378, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112478, value : 32'h352}, //phyinit_io_write: 0x112379, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112479, value : 32'h352}, //phyinit_io_write: 0x112478, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112578, value : 32'h352}, //phyinit_io_write: 0x112479, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112579, value : 32'h352}, //phyinit_io_write: 0x112578, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112678, value : 32'h352}, //phyinit_io_write: 0x112579, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112679, value : 32'h352}, //phyinit_io_write: 0x112678, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112778, value : 32'h352}, //phyinit_io_write: 0x112679, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112779, value : 32'h352}, //phyinit_io_write: 0x112778, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112878, value : 32'h352}, //phyinit_io_write: 0x112779, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h112879, value : 32'h352}, //phyinit_io_write: 0x112878, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113078, value : 32'h352}, //phyinit_io_write: 0x112879, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113079, value : 32'h352}, //phyinit_io_write: 0x113078, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113178, value : 32'h352}, //phyinit_io_write: 0x113079, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113179, value : 32'h352}, //phyinit_io_write: 0x113178, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113278, value : 32'h352}, //phyinit_io_write: 0x113179, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113279, value : 32'h352}, //phyinit_io_write: 0x113278, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113378, value : 32'h352}, //phyinit_io_write: 0x113279, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113379, value : 32'h352}, //phyinit_io_write: 0x113378, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113478, value : 32'h352}, //phyinit_io_write: 0x113379, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113479, value : 32'h352}, //phyinit_io_write: 0x113478, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113578, value : 32'h352}, //phyinit_io_write: 0x113479, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113579, value : 32'h352}, //phyinit_io_write: 0x113578, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113678, value : 32'h352}, //phyinit_io_write: 0x113579, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113679, value : 32'h352}, //phyinit_io_write: 0x113678, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113778, value : 32'h352}, //phyinit_io_write: 0x113679, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113779, value : 32'h352}, //phyinit_io_write: 0x113778, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113878, value : 32'h352}, //phyinit_io_write: 0x113779, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h113879, value : 32'h352}, //phyinit_io_write: 0x113878, 0x352
                          '{ step_type : REG_WRITE, reg_addr : 32'h110020, value : 32'h2b3}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming RxEnDlyTg0/Tg1 to 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h110021, value : 32'h2b3}, //phyinit_io_write: 0x110020, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h111020, value : 32'h2b3}, //phyinit_io_write: 0x110021, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h111021, value : 32'h2b3}, //phyinit_io_write: 0x111020, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h112020, value : 32'h2b3}, //phyinit_io_write: 0x111021, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h112021, value : 32'h2b3}, //phyinit_io_write: 0x112020, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h113020, value : 32'h2b3}, //phyinit_io_write: 0x112021, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h113021, value : 32'h2b3}, //phyinit_io_write: 0x113020, 0x2b3
                          '{ step_type : REG_WRITE, reg_addr : 32'h110010, value : 32'h188}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming RxClkT2UIDlyTg0/Tg1 and RxClkC2UIDlyTg0/Tg1 to 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110011, value : 32'h188}, //phyinit_io_write: 0x110010, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110012, value : 32'h188}, //phyinit_io_write: 0x110011, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110013, value : 32'h188}, //phyinit_io_write: 0x110012, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110110, value : 32'h188}, //phyinit_io_write: 0x110013, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110111, value : 32'h188}, //phyinit_io_write: 0x110110, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110112, value : 32'h188}, //phyinit_io_write: 0x110111, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110113, value : 32'h188}, //phyinit_io_write: 0x110112, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110210, value : 32'h188}, //phyinit_io_write: 0x110113, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110211, value : 32'h188}, //phyinit_io_write: 0x110210, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110212, value : 32'h188}, //phyinit_io_write: 0x110211, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110213, value : 32'h188}, //phyinit_io_write: 0x110212, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110310, value : 32'h188}, //phyinit_io_write: 0x110213, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110311, value : 32'h188}, //phyinit_io_write: 0x110310, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110312, value : 32'h188}, //phyinit_io_write: 0x110311, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110313, value : 32'h188}, //phyinit_io_write: 0x110312, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110410, value : 32'h188}, //phyinit_io_write: 0x110313, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110411, value : 32'h188}, //phyinit_io_write: 0x110410, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110412, value : 32'h188}, //phyinit_io_write: 0x110411, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110413, value : 32'h188}, //phyinit_io_write: 0x110412, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110510, value : 32'h188}, //phyinit_io_write: 0x110413, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110511, value : 32'h188}, //phyinit_io_write: 0x110510, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110512, value : 32'h188}, //phyinit_io_write: 0x110511, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110513, value : 32'h188}, //phyinit_io_write: 0x110512, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110610, value : 32'h188}, //phyinit_io_write: 0x110513, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110611, value : 32'h188}, //phyinit_io_write: 0x110610, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110612, value : 32'h188}, //phyinit_io_write: 0x110611, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110613, value : 32'h188}, //phyinit_io_write: 0x110612, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110710, value : 32'h188}, //phyinit_io_write: 0x110613, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110711, value : 32'h188}, //phyinit_io_write: 0x110710, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110712, value : 32'h188}, //phyinit_io_write: 0x110711, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110713, value : 32'h188}, //phyinit_io_write: 0x110712, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110810, value : 32'h188}, //phyinit_io_write: 0x110713, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110811, value : 32'h188}, //phyinit_io_write: 0x110810, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110812, value : 32'h188}, //phyinit_io_write: 0x110811, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h110813, value : 32'h188}, //phyinit_io_write: 0x110812, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111010, value : 32'h188}, //phyinit_io_write: 0x110813, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111011, value : 32'h188}, //phyinit_io_write: 0x111010, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111012, value : 32'h188}, //phyinit_io_write: 0x111011, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111013, value : 32'h188}, //phyinit_io_write: 0x111012, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111110, value : 32'h188}, //phyinit_io_write: 0x111013, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111111, value : 32'h188}, //phyinit_io_write: 0x111110, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111112, value : 32'h188}, //phyinit_io_write: 0x111111, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111113, value : 32'h188}, //phyinit_io_write: 0x111112, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111210, value : 32'h188}, //phyinit_io_write: 0x111113, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111211, value : 32'h188}, //phyinit_io_write: 0x111210, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111212, value : 32'h188}, //phyinit_io_write: 0x111211, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111213, value : 32'h188}, //phyinit_io_write: 0x111212, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111310, value : 32'h188}, //phyinit_io_write: 0x111213, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111311, value : 32'h188}, //phyinit_io_write: 0x111310, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111312, value : 32'h188}, //phyinit_io_write: 0x111311, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111313, value : 32'h188}, //phyinit_io_write: 0x111312, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111410, value : 32'h188}, //phyinit_io_write: 0x111313, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111411, value : 32'h188}, //phyinit_io_write: 0x111410, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111412, value : 32'h188}, //phyinit_io_write: 0x111411, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111413, value : 32'h188}, //phyinit_io_write: 0x111412, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111510, value : 32'h188}, //phyinit_io_write: 0x111413, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111511, value : 32'h188}, //phyinit_io_write: 0x111510, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111512, value : 32'h188}, //phyinit_io_write: 0x111511, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111513, value : 32'h188}, //phyinit_io_write: 0x111512, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111610, value : 32'h188}, //phyinit_io_write: 0x111513, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111611, value : 32'h188}, //phyinit_io_write: 0x111610, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111612, value : 32'h188}, //phyinit_io_write: 0x111611, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111613, value : 32'h188}, //phyinit_io_write: 0x111612, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111710, value : 32'h188}, //phyinit_io_write: 0x111613, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111711, value : 32'h188}, //phyinit_io_write: 0x111710, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111712, value : 32'h188}, //phyinit_io_write: 0x111711, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111713, value : 32'h188}, //phyinit_io_write: 0x111712, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111810, value : 32'h188}, //phyinit_io_write: 0x111713, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111811, value : 32'h188}, //phyinit_io_write: 0x111810, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111812, value : 32'h188}, //phyinit_io_write: 0x111811, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h111813, value : 32'h188}, //phyinit_io_write: 0x111812, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112010, value : 32'h188}, //phyinit_io_write: 0x111813, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112011, value : 32'h188}, //phyinit_io_write: 0x112010, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112012, value : 32'h188}, //phyinit_io_write: 0x112011, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112013, value : 32'h188}, //phyinit_io_write: 0x112012, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112110, value : 32'h188}, //phyinit_io_write: 0x112013, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112111, value : 32'h188}, //phyinit_io_write: 0x112110, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112112, value : 32'h188}, //phyinit_io_write: 0x112111, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112113, value : 32'h188}, //phyinit_io_write: 0x112112, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112210, value : 32'h188}, //phyinit_io_write: 0x112113, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112211, value : 32'h188}, //phyinit_io_write: 0x112210, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112212, value : 32'h188}, //phyinit_io_write: 0x112211, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112213, value : 32'h188}, //phyinit_io_write: 0x112212, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112310, value : 32'h188}, //phyinit_io_write: 0x112213, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112311, value : 32'h188}, //phyinit_io_write: 0x112310, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112312, value : 32'h188}, //phyinit_io_write: 0x112311, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112313, value : 32'h188}, //phyinit_io_write: 0x112312, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112410, value : 32'h188}, //phyinit_io_write: 0x112313, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112411, value : 32'h188}, //phyinit_io_write: 0x112410, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112412, value : 32'h188}, //phyinit_io_write: 0x112411, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112413, value : 32'h188}, //phyinit_io_write: 0x112412, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112510, value : 32'h188}, //phyinit_io_write: 0x112413, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112511, value : 32'h188}, //phyinit_io_write: 0x112510, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112512, value : 32'h188}, //phyinit_io_write: 0x112511, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112513, value : 32'h188}, //phyinit_io_write: 0x112512, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112610, value : 32'h188}, //phyinit_io_write: 0x112513, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112611, value : 32'h188}, //phyinit_io_write: 0x112610, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112612, value : 32'h188}, //phyinit_io_write: 0x112611, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112613, value : 32'h188}, //phyinit_io_write: 0x112612, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112710, value : 32'h188}, //phyinit_io_write: 0x112613, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112711, value : 32'h188}, //phyinit_io_write: 0x112710, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112712, value : 32'h188}, //phyinit_io_write: 0x112711, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112713, value : 32'h188}, //phyinit_io_write: 0x112712, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112810, value : 32'h188}, //phyinit_io_write: 0x112713, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112811, value : 32'h188}, //phyinit_io_write: 0x112810, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112812, value : 32'h188}, //phyinit_io_write: 0x112811, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h112813, value : 32'h188}, //phyinit_io_write: 0x112812, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113010, value : 32'h188}, //phyinit_io_write: 0x112813, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113011, value : 32'h188}, //phyinit_io_write: 0x113010, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113012, value : 32'h188}, //phyinit_io_write: 0x113011, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113013, value : 32'h188}, //phyinit_io_write: 0x113012, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113110, value : 32'h188}, //phyinit_io_write: 0x113013, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113111, value : 32'h188}, //phyinit_io_write: 0x113110, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113112, value : 32'h188}, //phyinit_io_write: 0x113111, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113113, value : 32'h188}, //phyinit_io_write: 0x113112, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113210, value : 32'h188}, //phyinit_io_write: 0x113113, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113211, value : 32'h188}, //phyinit_io_write: 0x113210, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113212, value : 32'h188}, //phyinit_io_write: 0x113211, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113213, value : 32'h188}, //phyinit_io_write: 0x113212, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113310, value : 32'h188}, //phyinit_io_write: 0x113213, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113311, value : 32'h188}, //phyinit_io_write: 0x113310, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113312, value : 32'h188}, //phyinit_io_write: 0x113311, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113313, value : 32'h188}, //phyinit_io_write: 0x113312, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113410, value : 32'h188}, //phyinit_io_write: 0x113313, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113411, value : 32'h188}, //phyinit_io_write: 0x113410, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113412, value : 32'h188}, //phyinit_io_write: 0x113411, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113413, value : 32'h188}, //phyinit_io_write: 0x113412, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113510, value : 32'h188}, //phyinit_io_write: 0x113413, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113511, value : 32'h188}, //phyinit_io_write: 0x113510, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113512, value : 32'h188}, //phyinit_io_write: 0x113511, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113513, value : 32'h188}, //phyinit_io_write: 0x113512, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113610, value : 32'h188}, //phyinit_io_write: 0x113513, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113611, value : 32'h188}, //phyinit_io_write: 0x113610, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113612, value : 32'h188}, //phyinit_io_write: 0x113611, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113613, value : 32'h188}, //phyinit_io_write: 0x113612, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113710, value : 32'h188}, //phyinit_io_write: 0x113613, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113711, value : 32'h188}, //phyinit_io_write: 0x113710, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113712, value : 32'h188}, //phyinit_io_write: 0x113711, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113713, value : 32'h188}, //phyinit_io_write: 0x113712, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113810, value : 32'h188}, //phyinit_io_write: 0x113713, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113811, value : 32'h188}, //phyinit_io_write: 0x113810, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113812, value : 32'h188}, //phyinit_io_write: 0x113811, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h113813, value : 32'h188}, //phyinit_io_write: 0x113812, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h11000c, value : 32'h9a}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming PptWck2DqoCntInvTrn1 to 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11000d, value : 32'h9a}, //phyinit_io_write: 0x11000c, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h110014, value : 32'h133}, //phyinit_io_write: 0x11000d, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h110015, value : 32'h133}, //phyinit_io_write: 0x110014, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11100c, value : 32'h9a}, //phyinit_io_write: 0x110015, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11100d, value : 32'h9a}, //phyinit_io_write: 0x11100c, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h111014, value : 32'h133}, //phyinit_io_write: 0x11100d, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h111015, value : 32'h133}, //phyinit_io_write: 0x111014, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11200c, value : 32'h9a}, //phyinit_io_write: 0x111015, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11200d, value : 32'h9a}, //phyinit_io_write: 0x11200c, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h112014, value : 32'h133}, //phyinit_io_write: 0x11200d, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h112015, value : 32'h133}, //phyinit_io_write: 0x112014, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11300c, value : 32'h9a}, //phyinit_io_write: 0x112015, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h11300d, value : 32'h9a}, //phyinit_io_write: 0x11300c, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h113014, value : 32'h133}, //phyinit_io_write: 0x11300d, 0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h113015, value : 32'h133}, //phyinit_io_write: 0x113014, 0x133
                          '{ step_type : REG_WRITE, reg_addr : 32'h70077, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming HwtCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h120071, value : 32'h55}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming HMRxReplicaLcdlSeed HMRxSeed to 0x83 HMRxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h100063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h101063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h102063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h103063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h104063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h105063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h107063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h108063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h109063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h10a063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h10b063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c063, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=1, Memclk=600MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0x83 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0063, value : 32'h83}, //phyinit_io_write: 0x10c063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0064, value : 32'h83}, //phyinit_io_write: 0x1e0063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e0087, value : 32'h83}, //phyinit_io_write: 0x1e0064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1063, value : 32'h83}, //phyinit_io_write: 0x1e0087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1064, value : 32'h83}, //phyinit_io_write: 0x1e1063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e1087, value : 32'h83}, //phyinit_io_write: 0x1e1064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2063, value : 32'h83}, //phyinit_io_write: 0x1e1087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2064, value : 32'h83}, //phyinit_io_write: 0x1e2063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e2087, value : 32'h83}, //phyinit_io_write: 0x1e2064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3063, value : 32'h83}, //phyinit_io_write: 0x1e2087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3064, value : 32'h83}, //phyinit_io_write: 0x1e3063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e3087, value : 32'h83}, //phyinit_io_write: 0x1e3064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4063, value : 32'h83}, //phyinit_io_write: 0x1e3087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4064, value : 32'h83}, //phyinit_io_write: 0x1e4063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e4087, value : 32'h83}, //phyinit_io_write: 0x1e4064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5063, value : 32'h83}, //phyinit_io_write: 0x1e4087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5064, value : 32'h83}, //phyinit_io_write: 0x1e5063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e5087, value : 32'h83}, //phyinit_io_write: 0x1e5064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6063, value : 32'h83}, //phyinit_io_write: 0x1e5087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6064, value : 32'h83}, //phyinit_io_write: 0x1e6063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e6087, value : 32'h83}, //phyinit_io_write: 0x1e6064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7063, value : 32'h83}, //phyinit_io_write: 0x1e6087, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7064, value : 32'h83}, //phyinit_io_write: 0x1e7063, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e7087, value : 32'h83}, //phyinit_io_write: 0x1e7064, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080a, value : 32'h283}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=1 Programming Seq0bGPR10 to mission mode HMTxLcdlSeed value 0x283
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080b, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=1 Programming Seq0bGPR11 to mission mode HMTxLcdlSeed value 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h190815, value : 32'h283}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=1 Programming Seq0bGPR21 to mission mode HMTxLcdlSeed value 0x283
                          '{ step_type : REG_WRITE, reg_addr : 32'h190816, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=1 Programming Seq0bGPR22 to mission mode HMTxLcdlSeed value 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h11015f, value : 32'h83}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=1, Memclk=600MHz, Programming RDqRDqsCntrl to 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h11115f, value : 32'h83}, //phyinit_io_write: 0x11015f, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h11215f, value : 32'h83}, //phyinit_io_write: 0x11115f, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h11315f, value : 32'h83}, //phyinit_io_write: 0x11215f, 0x83
                          '{ step_type : REG_WRITE, reg_addr : 32'h160009, value : 32'h10}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Memclk=600MHz, Programming CPllDacValIn to 0x10
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102a2, value : 32'h2c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaPathPhase2 to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102a3, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaPathPhase3 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102a4, value : 32'hb7}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaPathPhase4 to 0xb7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112a2, value : 32'h2c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaPathPhase2 to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112a3, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaPathPhase3 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112a4, value : 32'hb7}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaPathPhase4 to 0xb7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122a2, value : 32'h2c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaPathPhase2 to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122a3, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaPathPhase3 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122a4, value : 32'hb7}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaPathPhase4 to 0xb7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132a2, value : 32'h2c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaPathPhase2 to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132a3, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaPathPhase3 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132a4, value : 32'hb7}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaPathPhase4 to 0xb7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102af, value : 32'h28}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE0.RxReplicaCtl03 to 0x28
                          '{ step_type : REG_WRITE, reg_addr : 32'h1112af, value : 32'h28}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE1.RxReplicaCtl03 to 0x28
                          '{ step_type : REG_WRITE, reg_addr : 32'h1122af, value : 32'h28}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE2.RxReplicaCtl03 to 0x28
                          '{ step_type : REG_WRITE, reg_addr : 32'h1132af, value : 32'h28}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming DBYTE3.RxReplicaCtl03 to 0x28
                          '{ step_type : REG_WRITE, reg_addr : 32'h190807, value : 32'h9701}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming Seq0BGPR7 to save ZQCalCodeOvrValPU=0x12e and ZQCalCodeOvrEnPU=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h190808, value : 32'hb681}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=1, Programming Seq0BGPR8 to save ZQCalCodeOvrValPD=0x16d and ZQCalCodeOvrEnPD=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h0} //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
//[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] End of dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(), PState=1
   },
   "I" : '{                 
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Start of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h160008, value : 32'h956}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_I_loadPIEImagePsLoop] Pstate=1,  Memclk=600MHz, Programming CpllCtrl5 to 0x956.
                          '{ step_type : REG_WRITE, reg_addr : 32'h60006, value : 32'h3f0}, //End of dwc_ddrphy_phyinit_programPLL(), PState=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h130015, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h131015, value : 32'h0}, //phyinit_io_write: 0x130015, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11007c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11107c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11207c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11307c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h170141, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming ACSMWckFreeRunMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming GPR12 with Zcalkclkdiv to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h110027, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming RxClkCntl1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h111027, value : 32'h0}, //phyinit_io_write: 0x110027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112027, value : 32'h0}, //phyinit_io_write: 0x111027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h113027, value : 32'h0}, //phyinit_io_write: 0x112027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11020f, value : 32'h8}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=1, Programming RxReplicaCtl04 to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h11120f, value : 32'h8}, //phyinit_io_write: 0x11020f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h11220f, value : 32'h8}, //phyinit_io_write: 0x11120f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h11320f, value : 32'h8}, //phyinit_io_write: 0x11220f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e003f, value : 32'h0}, //phyinit_io_write: 0x11320f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e008d, value : 32'h0}, //phyinit_io_write: 0x1e003f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e103f, value : 32'h0}, //phyinit_io_write: 0x1e008d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e108d, value : 32'h0}, //phyinit_io_write: 0x1e103f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e203f, value : 32'h0}, //phyinit_io_write: 0x1e108d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e208d, value : 32'h0}, //phyinit_io_write: 0x1e203f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e303f, value : 32'h0}, //phyinit_io_write: 0x1e208d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e308d, value : 32'h0}, //phyinit_io_write: 0x1e303f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e403f, value : 32'h0}, //phyinit_io_write: 0x1e308d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e408d, value : 32'h0}, //phyinit_io_write: 0x1e403f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e503f, value : 32'h0}, //phyinit_io_write: 0x1e408d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e508d, value : 32'h0}, //phyinit_io_write: 0x1e503f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e603f, value : 32'h0}, //phyinit_io_write: 0x1e508d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e608d, value : 32'h0}, //phyinit_io_write: 0x1e603f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e703f, value : 32'h0}, //phyinit_io_write: 0x1e608d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1e708d, value : 32'h0}, //phyinit_io_write: 0x1e703f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h190903, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] PState=1, Programming RtrnMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70072, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnA to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080e, value : 32'h3}, //phyinit_io_write: 0x70072, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70073, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnB to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h19080f, value : 32'h3}, //phyinit_io_write: 0x70073, 0x3
//phyinit_io_write: 0x19080f, 0x3
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] End of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=1
//[dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop] End of dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop(), PState=1
//Start of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), PState=2, tck_ps=2500ps
                          '{ step_type : REG_WRITE, reg_addr : 32'h2008b, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, programming PState = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h290801, value : 32'ha692}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming Seq0BGPR1 to 0xa692
                          '{ step_type : REG_WRITE, reg_addr : 32'h290802, value : 32'h0}, //phyinit_io_write: 0x290801, 0xa692
                          '{ step_type : REG_WRITE, reg_addr : 32'h290806, value : 32'h1}, //phyinit_io_write: 0x290802, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2a03ff, value : 32'h4101}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming OdtSeg120 to 0x4101
                          '{ step_type : REG_WRITE, reg_addr : 32'h2a030b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming ZCalCompCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h260008, value : 32'h4a96}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_C_initPhyConfigPsLoop] Pstate=2,  Memclk=400MHz, Programming CpllCtrl5 to 0x4a96.
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e0, value : 32'h32}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY0 to 0x32 (0.5us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e1, value : 32'h96}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY1 to 0x96 (tZQCal PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e2, value : 32'h3e8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY2 to 0x3e8 (10.us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e3, value : 32'h58}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY3 to 0x58 (dllLock PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e4, value : 32'ha}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY4 to 0xa (0.1us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e5, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY5 to 0x0 (RxReplicaCalWait delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e6, value : 32'h43}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY6 to 0x43 (Oscillator PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908e7, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY7 to 0x0 (tXDSM_XP PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908ea, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY10 to 0x2 (tPDXCSODTON 20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908eb, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY11 to 0x2 (20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908ec, value : 32'h5}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY12 to 0x5 (50ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h2908ed, value : 32'h27}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming Seq0BDLY13 to 0x27 (tXSR PIE delay, tRFCab delay is 380ns)
                          '{ step_type : REG_WRITE, reg_addr : 32'h220002, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming PclkPtrInitVal to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h260040, value : 32'h3}, //phyinit_io_write: 0x220002, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h220000, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DfiFreqRatio to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2100fb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming RxDigStrbEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2110fb, value : 32'h0}, //phyinit_io_write: 0x2100fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2120fb, value : 32'h0}, //phyinit_io_write: 0x2110fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2130fb, value : 32'h0}, //phyinit_io_write: 0x2120fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e000b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DxDigStrobeMode HMDBYTE to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e100b, value : 32'h0}, //phyinit_io_write: 0x2e000b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e200b, value : 32'h0}, //phyinit_io_write: 0x2e100b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e300b, value : 32'h0}, //phyinit_io_write: 0x2e200b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e400b, value : 32'h0}, //phyinit_io_write: 0x2e300b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e500b, value : 32'h0}, //phyinit_io_write: 0x2e400b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e600b, value : 32'h0}, //phyinit_io_write: 0x2e500b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e700b, value : 32'h0}, //phyinit_io_write: 0x2e600b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h210024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE0.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h211024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE1.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h212024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE2.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h213024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE3.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h210025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE0.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h211025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE1.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h212025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE2.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h213025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE3.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h210004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE0.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h210003, value : 32'h0}, //phyinit_io_write: 0x210004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h211004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE1.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h211003, value : 32'h0}, //phyinit_io_write: 0x211004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h212004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE2.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h212003, value : 32'h0}, //phyinit_io_write: 0x212004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h213004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE3.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h213003, value : 32'h0}, //phyinit_io_write: 0x213004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2b0004, value : 32'h190}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ZCalClkInfo::ZCalDfiClkTicksPer1uS to 0x190
                          '{ step_type : REG_WRITE, reg_addr : 32'h2a030c, value : 32'h0},
                          '{ step_type : REG_WRITE, reg_addr : 32'h21003e, value : 32'h5}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE RxGainCurrAdjRxReplica to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21103e, value : 32'h5}, //phyinit_io_write: 0x21003e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21203e, value : 32'h5}, //phyinit_io_write: 0x21103e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21303e, value : 32'h5}, //phyinit_io_write: 0x21203e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h220003, value : 32'h1}, //phyinit_io_write: 0x21303e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h22000b, value : 32'h1111}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming CPclkDivRatio to 0x1111
                          '{ step_type : REG_WRITE, reg_addr : 32'h210108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE0.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h211108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE1.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h212108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE2.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h213108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming DBYTE3.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70005, value : 32'h0}, //[phyinit_C_initPhyConfig] Programming EnPhyUpdZQCalUpdate to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h7000f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming DisableZQupdateOnSnoop to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21000e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h21100e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h21200e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h21300e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h220019, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming EnRxDqsTracking::DqsSampNegRxEnSense to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e002c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e102c, value : 32'h33}, //phyinit_io_write: 0x2e002c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e002d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e102d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e202c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e302c, value : 32'h33}, //phyinit_io_write: 0x2e202c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e202d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e302d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e402c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e502c, value : 32'h33}, //phyinit_io_write: 0x2e402c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e402d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e502d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e602c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e702c, value : 32'h33}, //phyinit_io_write: 0x2e602c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e602d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e702d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h200070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC0 Instance0 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h201070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC1 Instance1 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h202070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC2 Instance2 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h203070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC3 Instance3 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h204070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming AC0 HMAC4 Instance4 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h205070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC5 Instance5 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h207070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC0 Instance7 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h208070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC1 Instance8 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h209070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC2 Instance9 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h20a070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC3 Instance10 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h20b070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming AC1 HMAC4 Instance11 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h20c070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC5 Instance12 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e002e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e102e, value : 32'h30}, //phyinit_io_write: 0x2e002e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e002f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e102f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e202e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e302e, value : 32'h30}, //phyinit_io_write: 0x2e202e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e202f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e302f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e402e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e502e, value : 32'h30}, //phyinit_io_write: 0x2e402e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e402f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e502f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e602e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e702e, value : 32'h30}, //phyinit_io_write: 0x2e602e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e602f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e702f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h200079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC0 Instance0 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h201079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC1 Instance1 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h202079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC2 Instance2 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h203079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC3 Instance3 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h204079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC4 Instance4 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h205079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC5 DIFF5 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h207079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC0 Instance7 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h208079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC1 Instance8 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h209079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC2 Instance9 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h20a079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC3 Instance10 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h20b079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC4 Instance11 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h20c079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC5 DIFF12 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e001c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 0 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e101c, value : 32'h3}, //phyinit_io_write: 0x2e001c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e201c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 1 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e301c, value : 32'h3}, //phyinit_io_write: 0x2e201c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e401c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 2 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e501c, value : 32'h3}, //phyinit_io_write: 0x2e401c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e601c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming HMDBYTE 3 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e701c, value : 32'h3}, //phyinit_io_write: 0x2e601c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h20006d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC0 Instance0 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20106d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC1 Instance1 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20206d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC2 Instance2 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20306d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC3 Instance3 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20406d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC4 Instance4 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h20506d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX0 HMAC5 Instance5 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20706d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC0 Instance7 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20806d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC1 Instance8 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20906d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC2 Instance9 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20a06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC3 Instance10 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20b06d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC4 Instance11 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h20c06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACX1 HMAC5 Instance12 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e003e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming HMDBYTE RxDQSCtrl::RxDQSDiffSeVrefDACEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e103e, value : 32'h0}, //phyinit_io_write: 0x2e003e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e203e, value : 32'h0}, //phyinit_io_write: 0x2e103e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e303e, value : 32'h0}, //phyinit_io_write: 0x2e203e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e403e, value : 32'h0}, //phyinit_io_write: 0x2e303e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e503e, value : 32'h0}, //phyinit_io_write: 0x2e403e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e603e, value : 32'h0}, //phyinit_io_write: 0x2e503e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e703e, value : 32'h0}, //phyinit_io_write: 0x2e603e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h210001, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming WriteLinkEcc to 0
                          '{ step_type : REG_WRITE, reg_addr : 32'h211001, value : 32'h0}, //phyinit_io_write: 0x210001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h212001, value : 32'h0}, //phyinit_io_write: 0x211001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h213001, value : 32'h0}, //phyinit_io_write: 0x212001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h270040, value : 32'h5a}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming PPTTrainSetup::PhyMstrMaxReqToAck to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h270041, value : 32'hf}, //phyinit_io_write: 0x270040, 0x5a
                          '{ step_type : REG_WRITE, reg_addr : 32'h2100a5, value : 32'h1}, //phyinit_io_write: 0x270041, 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h2110a5, value : 32'h1}, //phyinit_io_write: 0x2100a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h2120a5, value : 32'h1}, //phyinit_io_write: 0x2110a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h2130a5, value : 32'h1}, //phyinit_io_write: 0x2120a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h210209, value : 32'h3232}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming RxReplicaRangeVal 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h211209, value : 32'h3232}, //phyinit_io_write: 0x210209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h212209, value : 32'h3232}, //phyinit_io_write: 0x211209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h213209, value : 32'h3232}, //phyinit_io_write: 0x212209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h21020f, value : 32'h6}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming RxReplicaCtl04 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h21120f, value : 32'h6}, //phyinit_io_write: 0x21020f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h21220f, value : 32'h6}, //phyinit_io_write: 0x21120f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h21320f, value : 32'h6}, //phyinit_io_write: 0x21220f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h220005, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, DfiFreq=400MHz, Programming PipeCtl[AcInPipeEn]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h210008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, DfiFreq=400MHz, Programming DBYTE0.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h211008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, DfiFreq=400MHz, Programming DBYTE1.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h212008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, DfiFreq=400MHz, Programming DBYTE2.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h213008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, DfiFreq=400MHz, Programming DBYTE3.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h27006b, value : 32'h222}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, DfiFreq=400MHz, Programming DfiHandshakeDelays[PhyUpdReqDelay]=0x2 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h270066, value : 32'h20}, //phyinit_io_write: 0x27006b, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h2700eb, value : 32'h222}, //phyinit_io_write: 0x270066, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h2700e6, value : 32'h20}, //phyinit_io_write: 0x2700eb, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h270135, value : 32'h804}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth to 0x19, ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleDelay to 0x10
                          '{ step_type : REG_WRITE, reg_addr : 32'h270136, value : 32'h804}, //phyinit_io_write: 0x270135, 0x804
                          '{ step_type : REG_WRITE, reg_addr : 32'h270137, value : 32'h40c}, //phyinit_io_write: 0x270136, 0x804
                          '{ step_type : REG_WRITE, reg_addr : 32'h270138, value : 32'h1910}, //phyinit_io_write: 0x270137, 0x40c
                          '{ step_type : REG_WRITE, reg_addr : 32'h270139, value : 32'h808}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleWidth to 0x25, ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleDelay to 0x14
                          '{ step_type : REG_WRITE, reg_addr : 32'h27013a, value : 32'h808}, //phyinit_io_write: 0x270139, 0x808
                          '{ step_type : REG_WRITE, reg_addr : 32'h27013b, value : 32'h410}, //phyinit_io_write: 0x27013a, 0x808
                          '{ step_type : REG_WRITE, reg_addr : 32'h27013c, value : 32'h2514}, //phyinit_io_write: 0x27013b, 0x410
                          '{ step_type : REG_WRITE, reg_addr : 32'h27013d, value : 32'h800}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleWidth to 0x11, ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleDelay to 0xc
                          '{ step_type : REG_WRITE, reg_addr : 32'h27013e, value : 32'h800}, //phyinit_io_write: 0x27013d, 0x800
                          '{ step_type : REG_WRITE, reg_addr : 32'h27013f, value : 32'h408}, //phyinit_io_write: 0x27013e, 0x800
                          '{ step_type : REG_WRITE, reg_addr : 32'h270140, value : 32'h110c}, //phyinit_io_write: 0x27013f, 0x408
                          '{ step_type : REG_WRITE, reg_addr : 32'h27012c, value : 32'h81f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMRxValPulse::ACSMRxValDelay to 0x1f, ACSMRxValPulse::ACSMRxValWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h27012d, value : 32'h81f}, //phyinit_io_write: 0x27012c, 0x81f
                          '{ step_type : REG_WRITE, reg_addr : 32'h270130, value : 32'h81f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMRdcsPulse::ACSMRdcsDelay to 0x1f, ACSMRdcsPulse::ACSMRdcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h27012e, value : 32'h80f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMTxEnPulse::ACSMTxEnDelay to 0xf, ACSMTxEnPulse::ACSMTxEnWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h27012f, value : 32'h80f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming ACSMWrcsPulse::ACSMWrcsDelay to 0xf, ACSMWrcsPulse::ACSMWrcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h230008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming AcPipeEn AC0 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h231008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, Programming AcPipeEn AC1 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1013, value : 32'h0}, //phyinit_io_write: 0x2e0013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3013, value : 32'h0}, //phyinit_io_write: 0x2e2013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5013, value : 32'h0}, //phyinit_io_write: 0x2e4013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7013, value : 32'h0}, //phyinit_io_write: 0x2e6013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0002, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Programming HMDBYTE RxDFECtrlDq to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1002, value : 32'h0}, //phyinit_io_write: 0x2e0002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2002, value : 32'h0}, //phyinit_io_write: 0x2e1002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3002, value : 32'h0}, //phyinit_io_write: 0x2e2002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4002, value : 32'h0}, //phyinit_io_write: 0x2e3002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5002, value : 32'h0}, //phyinit_io_write: 0x2e4002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6002, value : 32'h0}, //phyinit_io_write: 0x2e5002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7002, value : 32'h0}, //phyinit_io_write: 0x2e6002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21010b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=2, Memclk=400MHz, freqThreshold=200MHz, NoRDQS=0 Programming InhibitTxRdPtrInit::DisableRxEnDlyLoad to 0x0, InhibitTxRdPtrInit::DisableTxDqDly to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21110b, value : 32'h0}, //phyinit_io_write: 0x21010b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21210b, value : 32'h0}, //phyinit_io_write: 0x21110b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21310b, value : 32'h0}, //phyinit_io_write: 0x21210b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h200063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h201063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h202063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h203063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h204063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h205063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h207063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h208063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h209063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h20a063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h20b063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h20c063, value : 32'hd0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080a, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR10 to HMTxLcdlSeed Full search value = 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080b, value : 32'hd0}, //phyinit_io_write: 0x29080a, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h290815, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR21 to ACHMTxLcdlSeed Full search value = 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h290816, value : 32'hd0}, //phyinit_io_write: 0x290815, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0063, value : 32'hd0}, //phyinit_io_write: 0x290816, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0064, value : 32'hd0}, //phyinit_io_write: 0x2e0063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0087, value : 32'hd0}, //phyinit_io_write: 0x2e0064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1063, value : 32'hd0}, //phyinit_io_write: 0x2e0087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1064, value : 32'hd0}, //phyinit_io_write: 0x2e1063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1087, value : 32'hd0}, //phyinit_io_write: 0x2e1064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2063, value : 32'hd0}, //phyinit_io_write: 0x2e1087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2064, value : 32'hd0}, //phyinit_io_write: 0x2e2063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2087, value : 32'hd0}, //phyinit_io_write: 0x2e2064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3063, value : 32'hd0}, //phyinit_io_write: 0x2e2087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3064, value : 32'hd0}, //phyinit_io_write: 0x2e3063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3087, value : 32'hd0}, //phyinit_io_write: 0x2e3064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4063, value : 32'hd0}, //phyinit_io_write: 0x2e3087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4064, value : 32'hd0}, //phyinit_io_write: 0x2e4063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4087, value : 32'hd0}, //phyinit_io_write: 0x2e4064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5063, value : 32'hd0}, //phyinit_io_write: 0x2e4087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5064, value : 32'hd0}, //phyinit_io_write: 0x2e5063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5087, value : 32'hd0}, //phyinit_io_write: 0x2e5064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6063, value : 32'hd0}, //phyinit_io_write: 0x2e5087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6064, value : 32'hd0}, //phyinit_io_write: 0x2e6063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6087, value : 32'hd0}, //phyinit_io_write: 0x2e6064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7063, value : 32'hd0}, //phyinit_io_write: 0x2e6087, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7064, value : 32'hd0}, //phyinit_io_write: 0x2e7063, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7087, value : 32'hd0}, //phyinit_io_write: 0x2e7064, 0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc0080, value : 32'h7}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming UcclkHclkEnables to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e003c, value : 32'h80}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming RxDQSSeVrefDAC0 to 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e103c, value : 32'h80}, //phyinit_io_write: 0x2e003c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e203c, value : 32'h80}, //phyinit_io_write: 0x2e103c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e303c, value : 32'h80}, //phyinit_io_write: 0x2e203c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e403c, value : 32'h80}, //phyinit_io_write: 0x2e303c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e503c, value : 32'h80}, //phyinit_io_write: 0x2e403c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e603c, value : 32'h80}, //phyinit_io_write: 0x2e503c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e703c, value : 32'h80}, //phyinit_io_write: 0x2e603c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h290817, value : 32'h29}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 2 Seq0BGPR23 to 0x29, NumMemClk_tRFCab=164.0, NumMemClk_7p5ns=3.0, NumMemClk_tXSR=167.0
                          '{ step_type : REG_WRITE, reg_addr : 32'h290818, value : 32'h0}, //phyinit_io_write: 0x290817, 0x29
                          '{ step_type : REG_WRITE, reg_addr : 32'h290819, value : 32'h0}, //phyinit_io_write: 0x290818, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2300eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 2 AC0 AcLcdlUpdInterval to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2310eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 2 AC1 AcLcdlUpdInterval to 0x0
//[dwc_ddrphy_phyinit_programDfiMode] Skip DfiMode Programming: Keeping the reset value of 0x3
//End of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), Pstate=2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2300d9, value : 32'h40}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming CKXTxDly to 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2300d8, value : 32'h40}, //phyinit_io_write: 0x2300d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2301d8, value : 32'h40}, //phyinit_io_write: 0x2300d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2302d8, value : 32'h40}, //phyinit_io_write: 0x2301d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2303d8, value : 32'h40}, //phyinit_io_write: 0x2302d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2304d8, value : 32'h40}, //phyinit_io_write: 0x2303d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2305d8, value : 32'h40}, //phyinit_io_write: 0x2304d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2306d8, value : 32'h40}, //phyinit_io_write: 0x2305d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2308d8, value : 32'h40}, //phyinit_io_write: 0x2306d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2309d8, value : 32'h40}, //phyinit_io_write: 0x2308d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2310d9, value : 32'h40}, //phyinit_io_write: 0x2309d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2310d8, value : 32'h40}, //phyinit_io_write: 0x2310d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2311d8, value : 32'h40}, //phyinit_io_write: 0x2310d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2312d8, value : 32'h40}, //phyinit_io_write: 0x2311d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2313d8, value : 32'h40}, //phyinit_io_write: 0x2312d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2314d8, value : 32'h40}, //phyinit_io_write: 0x2313d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2315d8, value : 32'h40}, //phyinit_io_write: 0x2314d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2316d8, value : 32'h40}, //phyinit_io_write: 0x2315d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2318d8, value : 32'h40}, //phyinit_io_write: 0x2316d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h2319d8, value : 32'h40}, //phyinit_io_write: 0x2318d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h210000, value : 32'h6}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming HwtMRL to 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h211000, value : 32'h6}, //phyinit_io_write: 0x210000, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h212000, value : 32'h6}, //phyinit_io_write: 0x211000, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h213000, value : 32'h6}, //phyinit_io_write: 0x212000, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h27000d, value : 32'h6}, //phyinit_io_write: 0x213000, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h21002a, value : 32'h200}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming TxWckDlyTg0/Tg1 to 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21002b, value : 32'h200}, //phyinit_io_write: 0x21002a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21102a, value : 32'h200}, //phyinit_io_write: 0x21002b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21102b, value : 32'h200}, //phyinit_io_write: 0x21102a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21202a, value : 32'h200}, //phyinit_io_write: 0x21102b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21202b, value : 32'h200}, //phyinit_io_write: 0x21202a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21302a, value : 32'h200}, //phyinit_io_write: 0x21202b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h21302b, value : 32'h200}, //phyinit_io_write: 0x21302a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h210028, value : 32'h87}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming TxDqsDlyTg0/Tg1 to 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h210029, value : 32'h87}, //phyinit_io_write: 0x210028, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h211028, value : 32'h87}, //phyinit_io_write: 0x210029, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h211029, value : 32'h87}, //phyinit_io_write: 0x211028, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h212028, value : 32'h87}, //phyinit_io_write: 0x211029, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h212029, value : 32'h87}, //phyinit_io_write: 0x212028, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h213028, value : 32'h87}, //phyinit_io_write: 0x212029, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h213029, value : 32'h87}, //phyinit_io_write: 0x213028, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21007a, value : 32'h87}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming TxDqDlyTg0/Tg1 to 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21007b, value : 32'h87}, //phyinit_io_write: 0x21007a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21017a, value : 32'h87}, //phyinit_io_write: 0x21007b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21017b, value : 32'h87}, //phyinit_io_write: 0x21017a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21027a, value : 32'h87}, //phyinit_io_write: 0x21017b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21027b, value : 32'h87}, //phyinit_io_write: 0x21027a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21037a, value : 32'h87}, //phyinit_io_write: 0x21027b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21037b, value : 32'h87}, //phyinit_io_write: 0x21037a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21047a, value : 32'h87}, //phyinit_io_write: 0x21037b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21047b, value : 32'h87}, //phyinit_io_write: 0x21047a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21057a, value : 32'h87}, //phyinit_io_write: 0x21047b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21057b, value : 32'h87}, //phyinit_io_write: 0x21057a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21067a, value : 32'h87}, //phyinit_io_write: 0x21057b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21067b, value : 32'h87}, //phyinit_io_write: 0x21067a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21077a, value : 32'h87}, //phyinit_io_write: 0x21067b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21077b, value : 32'h87}, //phyinit_io_write: 0x21077a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21087a, value : 32'h87}, //phyinit_io_write: 0x21077b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21087b, value : 32'h87}, //phyinit_io_write: 0x21087a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21107a, value : 32'h87}, //phyinit_io_write: 0x21087b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21107b, value : 32'h87}, //phyinit_io_write: 0x21107a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21117a, value : 32'h87}, //phyinit_io_write: 0x21107b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21117b, value : 32'h87}, //phyinit_io_write: 0x21117a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21127a, value : 32'h87}, //phyinit_io_write: 0x21117b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21127b, value : 32'h87}, //phyinit_io_write: 0x21127a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21137a, value : 32'h87}, //phyinit_io_write: 0x21127b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21137b, value : 32'h87}, //phyinit_io_write: 0x21137a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21147a, value : 32'h87}, //phyinit_io_write: 0x21137b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21147b, value : 32'h87}, //phyinit_io_write: 0x21147a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21157a, value : 32'h87}, //phyinit_io_write: 0x21147b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21157b, value : 32'h87}, //phyinit_io_write: 0x21157a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21167a, value : 32'h87}, //phyinit_io_write: 0x21157b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21167b, value : 32'h87}, //phyinit_io_write: 0x21167a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21177a, value : 32'h87}, //phyinit_io_write: 0x21167b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21177b, value : 32'h87}, //phyinit_io_write: 0x21177a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21187a, value : 32'h87}, //phyinit_io_write: 0x21177b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21187b, value : 32'h87}, //phyinit_io_write: 0x21187a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21207a, value : 32'h87}, //phyinit_io_write: 0x21187b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21207b, value : 32'h87}, //phyinit_io_write: 0x21207a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21217a, value : 32'h87}, //phyinit_io_write: 0x21207b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21217b, value : 32'h87}, //phyinit_io_write: 0x21217a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21227a, value : 32'h87}, //phyinit_io_write: 0x21217b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21227b, value : 32'h87}, //phyinit_io_write: 0x21227a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21237a, value : 32'h87}, //phyinit_io_write: 0x21227b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21237b, value : 32'h87}, //phyinit_io_write: 0x21237a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21247a, value : 32'h87}, //phyinit_io_write: 0x21237b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21247b, value : 32'h87}, //phyinit_io_write: 0x21247a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21257a, value : 32'h87}, //phyinit_io_write: 0x21247b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21257b, value : 32'h87}, //phyinit_io_write: 0x21257a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21267a, value : 32'h87}, //phyinit_io_write: 0x21257b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21267b, value : 32'h87}, //phyinit_io_write: 0x21267a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21277a, value : 32'h87}, //phyinit_io_write: 0x21267b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21277b, value : 32'h87}, //phyinit_io_write: 0x21277a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21287a, value : 32'h87}, //phyinit_io_write: 0x21277b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21287b, value : 32'h87}, //phyinit_io_write: 0x21287a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21307a, value : 32'h87}, //phyinit_io_write: 0x21287b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21307b, value : 32'h87}, //phyinit_io_write: 0x21307a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21317a, value : 32'h87}, //phyinit_io_write: 0x21307b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21317b, value : 32'h87}, //phyinit_io_write: 0x21317a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21327a, value : 32'h87}, //phyinit_io_write: 0x21317b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21327b, value : 32'h87}, //phyinit_io_write: 0x21327a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21337a, value : 32'h87}, //phyinit_io_write: 0x21327b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21337b, value : 32'h87}, //phyinit_io_write: 0x21337a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21347a, value : 32'h87}, //phyinit_io_write: 0x21337b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21347b, value : 32'h87}, //phyinit_io_write: 0x21347a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21357a, value : 32'h87}, //phyinit_io_write: 0x21347b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21357b, value : 32'h87}, //phyinit_io_write: 0x21357a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21367a, value : 32'h87}, //phyinit_io_write: 0x21357b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21367b, value : 32'h87}, //phyinit_io_write: 0x21367a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21377a, value : 32'h87}, //phyinit_io_write: 0x21367b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21377b, value : 32'h87}, //phyinit_io_write: 0x21377a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21387a, value : 32'h87}, //phyinit_io_write: 0x21377b, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h21387b, value : 32'h87}, //phyinit_io_write: 0x21387a, 0x87
                          '{ step_type : REG_WRITE, reg_addr : 32'h210078, value : 32'h2ec}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming RxDigStrbDlyTg0/Tg1 to 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210079, value : 32'h2ec}, //phyinit_io_write: 0x210078, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210178, value : 32'h2ec}, //phyinit_io_write: 0x210079, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210179, value : 32'h2ec}, //phyinit_io_write: 0x210178, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210278, value : 32'h2ec}, //phyinit_io_write: 0x210179, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210279, value : 32'h2ec}, //phyinit_io_write: 0x210278, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210378, value : 32'h2ec}, //phyinit_io_write: 0x210279, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210379, value : 32'h2ec}, //phyinit_io_write: 0x210378, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210478, value : 32'h2ec}, //phyinit_io_write: 0x210379, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210479, value : 32'h2ec}, //phyinit_io_write: 0x210478, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210578, value : 32'h2ec}, //phyinit_io_write: 0x210479, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210579, value : 32'h2ec}, //phyinit_io_write: 0x210578, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210678, value : 32'h2ec}, //phyinit_io_write: 0x210579, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210679, value : 32'h2ec}, //phyinit_io_write: 0x210678, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210778, value : 32'h2ec}, //phyinit_io_write: 0x210679, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210779, value : 32'h2ec}, //phyinit_io_write: 0x210778, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210878, value : 32'h2ec}, //phyinit_io_write: 0x210779, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210879, value : 32'h2ec}, //phyinit_io_write: 0x210878, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211078, value : 32'h2ec}, //phyinit_io_write: 0x210879, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211079, value : 32'h2ec}, //phyinit_io_write: 0x211078, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211178, value : 32'h2ec}, //phyinit_io_write: 0x211079, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211179, value : 32'h2ec}, //phyinit_io_write: 0x211178, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211278, value : 32'h2ec}, //phyinit_io_write: 0x211179, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211279, value : 32'h2ec}, //phyinit_io_write: 0x211278, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211378, value : 32'h2ec}, //phyinit_io_write: 0x211279, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211379, value : 32'h2ec}, //phyinit_io_write: 0x211378, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211478, value : 32'h2ec}, //phyinit_io_write: 0x211379, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211479, value : 32'h2ec}, //phyinit_io_write: 0x211478, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211578, value : 32'h2ec}, //phyinit_io_write: 0x211479, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211579, value : 32'h2ec}, //phyinit_io_write: 0x211578, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211678, value : 32'h2ec}, //phyinit_io_write: 0x211579, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211679, value : 32'h2ec}, //phyinit_io_write: 0x211678, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211778, value : 32'h2ec}, //phyinit_io_write: 0x211679, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211779, value : 32'h2ec}, //phyinit_io_write: 0x211778, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211878, value : 32'h2ec}, //phyinit_io_write: 0x211779, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h211879, value : 32'h2ec}, //phyinit_io_write: 0x211878, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212078, value : 32'h2ec}, //phyinit_io_write: 0x211879, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212079, value : 32'h2ec}, //phyinit_io_write: 0x212078, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212178, value : 32'h2ec}, //phyinit_io_write: 0x212079, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212179, value : 32'h2ec}, //phyinit_io_write: 0x212178, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212278, value : 32'h2ec}, //phyinit_io_write: 0x212179, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212279, value : 32'h2ec}, //phyinit_io_write: 0x212278, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212378, value : 32'h2ec}, //phyinit_io_write: 0x212279, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212379, value : 32'h2ec}, //phyinit_io_write: 0x212378, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212478, value : 32'h2ec}, //phyinit_io_write: 0x212379, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212479, value : 32'h2ec}, //phyinit_io_write: 0x212478, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212578, value : 32'h2ec}, //phyinit_io_write: 0x212479, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212579, value : 32'h2ec}, //phyinit_io_write: 0x212578, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212678, value : 32'h2ec}, //phyinit_io_write: 0x212579, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212679, value : 32'h2ec}, //phyinit_io_write: 0x212678, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212778, value : 32'h2ec}, //phyinit_io_write: 0x212679, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212779, value : 32'h2ec}, //phyinit_io_write: 0x212778, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212878, value : 32'h2ec}, //phyinit_io_write: 0x212779, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h212879, value : 32'h2ec}, //phyinit_io_write: 0x212878, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213078, value : 32'h2ec}, //phyinit_io_write: 0x212879, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213079, value : 32'h2ec}, //phyinit_io_write: 0x213078, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213178, value : 32'h2ec}, //phyinit_io_write: 0x213079, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213179, value : 32'h2ec}, //phyinit_io_write: 0x213178, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213278, value : 32'h2ec}, //phyinit_io_write: 0x213179, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213279, value : 32'h2ec}, //phyinit_io_write: 0x213278, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213378, value : 32'h2ec}, //phyinit_io_write: 0x213279, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213379, value : 32'h2ec}, //phyinit_io_write: 0x213378, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213478, value : 32'h2ec}, //phyinit_io_write: 0x213379, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213479, value : 32'h2ec}, //phyinit_io_write: 0x213478, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213578, value : 32'h2ec}, //phyinit_io_write: 0x213479, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213579, value : 32'h2ec}, //phyinit_io_write: 0x213578, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213678, value : 32'h2ec}, //phyinit_io_write: 0x213579, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213679, value : 32'h2ec}, //phyinit_io_write: 0x213678, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213778, value : 32'h2ec}, //phyinit_io_write: 0x213679, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213779, value : 32'h2ec}, //phyinit_io_write: 0x213778, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213878, value : 32'h2ec}, //phyinit_io_write: 0x213779, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h213879, value : 32'h2ec}, //phyinit_io_write: 0x213878, 0x2ec
                          '{ step_type : REG_WRITE, reg_addr : 32'h210020, value : 32'h24c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming RxEnDlyTg0/Tg1 to 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h210021, value : 32'h24c}, //phyinit_io_write: 0x210020, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h211020, value : 32'h24c}, //phyinit_io_write: 0x210021, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h211021, value : 32'h24c}, //phyinit_io_write: 0x211020, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h212020, value : 32'h24c}, //phyinit_io_write: 0x211021, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h212021, value : 32'h24c}, //phyinit_io_write: 0x212020, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h213020, value : 32'h24c}, //phyinit_io_write: 0x212021, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h213021, value : 32'h24c}, //phyinit_io_write: 0x213020, 0x24c
                          '{ step_type : REG_WRITE, reg_addr : 32'h210010, value : 32'h1a5}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming RxClkT2UIDlyTg0/Tg1 and RxClkC2UIDlyTg0/Tg1 to 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210011, value : 32'h1a5}, //phyinit_io_write: 0x210010, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210012, value : 32'h1a5}, //phyinit_io_write: 0x210011, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210013, value : 32'h1a5}, //phyinit_io_write: 0x210012, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210110, value : 32'h1a5}, //phyinit_io_write: 0x210013, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210111, value : 32'h1a5}, //phyinit_io_write: 0x210110, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210112, value : 32'h1a5}, //phyinit_io_write: 0x210111, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210113, value : 32'h1a5}, //phyinit_io_write: 0x210112, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210210, value : 32'h1a5}, //phyinit_io_write: 0x210113, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210211, value : 32'h1a5}, //phyinit_io_write: 0x210210, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210212, value : 32'h1a5}, //phyinit_io_write: 0x210211, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210213, value : 32'h1a5}, //phyinit_io_write: 0x210212, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210310, value : 32'h1a5}, //phyinit_io_write: 0x210213, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210311, value : 32'h1a5}, //phyinit_io_write: 0x210310, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210312, value : 32'h1a5}, //phyinit_io_write: 0x210311, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210313, value : 32'h1a5}, //phyinit_io_write: 0x210312, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210410, value : 32'h1a5}, //phyinit_io_write: 0x210313, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210411, value : 32'h1a5}, //phyinit_io_write: 0x210410, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210412, value : 32'h1a5}, //phyinit_io_write: 0x210411, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210413, value : 32'h1a5}, //phyinit_io_write: 0x210412, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210510, value : 32'h1a5}, //phyinit_io_write: 0x210413, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210511, value : 32'h1a5}, //phyinit_io_write: 0x210510, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210512, value : 32'h1a5}, //phyinit_io_write: 0x210511, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210513, value : 32'h1a5}, //phyinit_io_write: 0x210512, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210610, value : 32'h1a5}, //phyinit_io_write: 0x210513, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210611, value : 32'h1a5}, //phyinit_io_write: 0x210610, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210612, value : 32'h1a5}, //phyinit_io_write: 0x210611, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210613, value : 32'h1a5}, //phyinit_io_write: 0x210612, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210710, value : 32'h1a5}, //phyinit_io_write: 0x210613, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210711, value : 32'h1a5}, //phyinit_io_write: 0x210710, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210712, value : 32'h1a5}, //phyinit_io_write: 0x210711, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210713, value : 32'h1a5}, //phyinit_io_write: 0x210712, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210810, value : 32'h1a5}, //phyinit_io_write: 0x210713, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210811, value : 32'h1a5}, //phyinit_io_write: 0x210810, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210812, value : 32'h1a5}, //phyinit_io_write: 0x210811, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h210813, value : 32'h1a5}, //phyinit_io_write: 0x210812, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211010, value : 32'h1a5}, //phyinit_io_write: 0x210813, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211011, value : 32'h1a5}, //phyinit_io_write: 0x211010, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211012, value : 32'h1a5}, //phyinit_io_write: 0x211011, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211013, value : 32'h1a5}, //phyinit_io_write: 0x211012, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211110, value : 32'h1a5}, //phyinit_io_write: 0x211013, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211111, value : 32'h1a5}, //phyinit_io_write: 0x211110, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211112, value : 32'h1a5}, //phyinit_io_write: 0x211111, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211113, value : 32'h1a5}, //phyinit_io_write: 0x211112, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211210, value : 32'h1a5}, //phyinit_io_write: 0x211113, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211211, value : 32'h1a5}, //phyinit_io_write: 0x211210, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211212, value : 32'h1a5}, //phyinit_io_write: 0x211211, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211213, value : 32'h1a5}, //phyinit_io_write: 0x211212, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211310, value : 32'h1a5}, //phyinit_io_write: 0x211213, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211311, value : 32'h1a5}, //phyinit_io_write: 0x211310, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211312, value : 32'h1a5}, //phyinit_io_write: 0x211311, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211313, value : 32'h1a5}, //phyinit_io_write: 0x211312, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211410, value : 32'h1a5}, //phyinit_io_write: 0x211313, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211411, value : 32'h1a5}, //phyinit_io_write: 0x211410, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211412, value : 32'h1a5}, //phyinit_io_write: 0x211411, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211413, value : 32'h1a5}, //phyinit_io_write: 0x211412, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211510, value : 32'h1a5}, //phyinit_io_write: 0x211413, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211511, value : 32'h1a5}, //phyinit_io_write: 0x211510, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211512, value : 32'h1a5}, //phyinit_io_write: 0x211511, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211513, value : 32'h1a5}, //phyinit_io_write: 0x211512, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211610, value : 32'h1a5}, //phyinit_io_write: 0x211513, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211611, value : 32'h1a5}, //phyinit_io_write: 0x211610, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211612, value : 32'h1a5}, //phyinit_io_write: 0x211611, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211613, value : 32'h1a5}, //phyinit_io_write: 0x211612, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211710, value : 32'h1a5}, //phyinit_io_write: 0x211613, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211711, value : 32'h1a5}, //phyinit_io_write: 0x211710, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211712, value : 32'h1a5}, //phyinit_io_write: 0x211711, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211713, value : 32'h1a5}, //phyinit_io_write: 0x211712, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211810, value : 32'h1a5}, //phyinit_io_write: 0x211713, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211811, value : 32'h1a5}, //phyinit_io_write: 0x211810, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211812, value : 32'h1a5}, //phyinit_io_write: 0x211811, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h211813, value : 32'h1a5}, //phyinit_io_write: 0x211812, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212010, value : 32'h1a5}, //phyinit_io_write: 0x211813, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212011, value : 32'h1a5}, //phyinit_io_write: 0x212010, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212012, value : 32'h1a5}, //phyinit_io_write: 0x212011, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212013, value : 32'h1a5}, //phyinit_io_write: 0x212012, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212110, value : 32'h1a5}, //phyinit_io_write: 0x212013, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212111, value : 32'h1a5}, //phyinit_io_write: 0x212110, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212112, value : 32'h1a5}, //phyinit_io_write: 0x212111, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212113, value : 32'h1a5}, //phyinit_io_write: 0x212112, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212210, value : 32'h1a5}, //phyinit_io_write: 0x212113, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212211, value : 32'h1a5}, //phyinit_io_write: 0x212210, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212212, value : 32'h1a5}, //phyinit_io_write: 0x212211, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212213, value : 32'h1a5}, //phyinit_io_write: 0x212212, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212310, value : 32'h1a5}, //phyinit_io_write: 0x212213, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212311, value : 32'h1a5}, //phyinit_io_write: 0x212310, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212312, value : 32'h1a5}, //phyinit_io_write: 0x212311, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212313, value : 32'h1a5}, //phyinit_io_write: 0x212312, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212410, value : 32'h1a5}, //phyinit_io_write: 0x212313, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212411, value : 32'h1a5}, //phyinit_io_write: 0x212410, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212412, value : 32'h1a5}, //phyinit_io_write: 0x212411, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212413, value : 32'h1a5}, //phyinit_io_write: 0x212412, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212510, value : 32'h1a5}, //phyinit_io_write: 0x212413, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212511, value : 32'h1a5}, //phyinit_io_write: 0x212510, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212512, value : 32'h1a5}, //phyinit_io_write: 0x212511, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212513, value : 32'h1a5}, //phyinit_io_write: 0x212512, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212610, value : 32'h1a5}, //phyinit_io_write: 0x212513, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212611, value : 32'h1a5}, //phyinit_io_write: 0x212610, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212612, value : 32'h1a5}, //phyinit_io_write: 0x212611, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212613, value : 32'h1a5}, //phyinit_io_write: 0x212612, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212710, value : 32'h1a5}, //phyinit_io_write: 0x212613, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212711, value : 32'h1a5}, //phyinit_io_write: 0x212710, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212712, value : 32'h1a5}, //phyinit_io_write: 0x212711, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212713, value : 32'h1a5}, //phyinit_io_write: 0x212712, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212810, value : 32'h1a5}, //phyinit_io_write: 0x212713, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212811, value : 32'h1a5}, //phyinit_io_write: 0x212810, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212812, value : 32'h1a5}, //phyinit_io_write: 0x212811, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h212813, value : 32'h1a5}, //phyinit_io_write: 0x212812, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213010, value : 32'h1a5}, //phyinit_io_write: 0x212813, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213011, value : 32'h1a5}, //phyinit_io_write: 0x213010, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213012, value : 32'h1a5}, //phyinit_io_write: 0x213011, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213013, value : 32'h1a5}, //phyinit_io_write: 0x213012, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213110, value : 32'h1a5}, //phyinit_io_write: 0x213013, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213111, value : 32'h1a5}, //phyinit_io_write: 0x213110, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213112, value : 32'h1a5}, //phyinit_io_write: 0x213111, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213113, value : 32'h1a5}, //phyinit_io_write: 0x213112, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213210, value : 32'h1a5}, //phyinit_io_write: 0x213113, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213211, value : 32'h1a5}, //phyinit_io_write: 0x213210, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213212, value : 32'h1a5}, //phyinit_io_write: 0x213211, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213213, value : 32'h1a5}, //phyinit_io_write: 0x213212, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213310, value : 32'h1a5}, //phyinit_io_write: 0x213213, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213311, value : 32'h1a5}, //phyinit_io_write: 0x213310, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213312, value : 32'h1a5}, //phyinit_io_write: 0x213311, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213313, value : 32'h1a5}, //phyinit_io_write: 0x213312, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213410, value : 32'h1a5}, //phyinit_io_write: 0x213313, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213411, value : 32'h1a5}, //phyinit_io_write: 0x213410, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213412, value : 32'h1a5}, //phyinit_io_write: 0x213411, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213413, value : 32'h1a5}, //phyinit_io_write: 0x213412, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213510, value : 32'h1a5}, //phyinit_io_write: 0x213413, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213511, value : 32'h1a5}, //phyinit_io_write: 0x213510, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213512, value : 32'h1a5}, //phyinit_io_write: 0x213511, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213513, value : 32'h1a5}, //phyinit_io_write: 0x213512, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213610, value : 32'h1a5}, //phyinit_io_write: 0x213513, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213611, value : 32'h1a5}, //phyinit_io_write: 0x213610, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213612, value : 32'h1a5}, //phyinit_io_write: 0x213611, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213613, value : 32'h1a5}, //phyinit_io_write: 0x213612, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213710, value : 32'h1a5}, //phyinit_io_write: 0x213613, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213711, value : 32'h1a5}, //phyinit_io_write: 0x213710, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213712, value : 32'h1a5}, //phyinit_io_write: 0x213711, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213713, value : 32'h1a5}, //phyinit_io_write: 0x213712, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213810, value : 32'h1a5}, //phyinit_io_write: 0x213713, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213811, value : 32'h1a5}, //phyinit_io_write: 0x213810, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213812, value : 32'h1a5}, //phyinit_io_write: 0x213811, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h213813, value : 32'h1a5}, //phyinit_io_write: 0x213812, 0x1a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21000c, value : 32'h67}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming PptWck2DqoCntInvTrn1 to 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21000d, value : 32'h67}, //phyinit_io_write: 0x21000c, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h210014, value : 32'hcd}, //phyinit_io_write: 0x21000d, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h210015, value : 32'hcd}, //phyinit_io_write: 0x210014, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21100c, value : 32'h67}, //phyinit_io_write: 0x210015, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21100d, value : 32'h67}, //phyinit_io_write: 0x21100c, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h211014, value : 32'hcd}, //phyinit_io_write: 0x21100d, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h211015, value : 32'hcd}, //phyinit_io_write: 0x211014, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21200c, value : 32'h67}, //phyinit_io_write: 0x211015, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21200d, value : 32'h67}, //phyinit_io_write: 0x21200c, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h212014, value : 32'hcd}, //phyinit_io_write: 0x21200d, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h212015, value : 32'hcd}, //phyinit_io_write: 0x212014, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21300c, value : 32'h67}, //phyinit_io_write: 0x212015, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h21300d, value : 32'h67}, //phyinit_io_write: 0x21300c, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h213014, value : 32'hcd}, //phyinit_io_write: 0x21300d, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h213015, value : 32'hcd}, //phyinit_io_write: 0x213014, 0xcd
                          '{ step_type : REG_WRITE, reg_addr : 32'h70077, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming HwtCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h220071, value : 32'h55}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming HMRxReplicaLcdlSeed HMRxSeed to 0xc5 HMRxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h200063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h201063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h202063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h203063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h204063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h205063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h207063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h208063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h209063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h20a063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h20b063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h20c063, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=2, Memclk=400MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0xc5 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0063, value : 32'hc5}, //phyinit_io_write: 0x20c063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0064, value : 32'hc5}, //phyinit_io_write: 0x2e0063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e0087, value : 32'hc5}, //phyinit_io_write: 0x2e0064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1063, value : 32'hc5}, //phyinit_io_write: 0x2e0087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1064, value : 32'hc5}, //phyinit_io_write: 0x2e1063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e1087, value : 32'hc5}, //phyinit_io_write: 0x2e1064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2063, value : 32'hc5}, //phyinit_io_write: 0x2e1087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2064, value : 32'hc5}, //phyinit_io_write: 0x2e2063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e2087, value : 32'hc5}, //phyinit_io_write: 0x2e2064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3063, value : 32'hc5}, //phyinit_io_write: 0x2e2087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3064, value : 32'hc5}, //phyinit_io_write: 0x2e3063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e3087, value : 32'hc5}, //phyinit_io_write: 0x2e3064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4063, value : 32'hc5}, //phyinit_io_write: 0x2e3087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4064, value : 32'hc5}, //phyinit_io_write: 0x2e4063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e4087, value : 32'hc5}, //phyinit_io_write: 0x2e4064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5063, value : 32'hc5}, //phyinit_io_write: 0x2e4087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5064, value : 32'hc5}, //phyinit_io_write: 0x2e5063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e5087, value : 32'hc5}, //phyinit_io_write: 0x2e5064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6063, value : 32'hc5}, //phyinit_io_write: 0x2e5087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6064, value : 32'hc5}, //phyinit_io_write: 0x2e6063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e6087, value : 32'hc5}, //phyinit_io_write: 0x2e6064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7063, value : 32'hc5}, //phyinit_io_write: 0x2e6087, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7064, value : 32'hc5}, //phyinit_io_write: 0x2e7063, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e7087, value : 32'hc5}, //phyinit_io_write: 0x2e7064, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080a, value : 32'h2c5}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=2 Programming Seq0bGPR10 to mission mode HMTxLcdlSeed value 0x2c5
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080b, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=2 Programming Seq0bGPR11 to mission mode HMTxLcdlSeed value 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h290815, value : 32'h2c5}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=2 Programming Seq0bGPR21 to mission mode HMTxLcdlSeed value 0x2c5
                          '{ step_type : REG_WRITE, reg_addr : 32'h290816, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=2 Programming Seq0bGPR22 to mission mode HMTxLcdlSeed value 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21015f, value : 32'hc5}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=2, Memclk=400MHz, Programming RDqRDqsCntrl to 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21115f, value : 32'hc5}, //phyinit_io_write: 0x21015f, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21215f, value : 32'hc5}, //phyinit_io_write: 0x21115f, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h21315f, value : 32'hc5}, //phyinit_io_write: 0x21215f, 0xc5
                          '{ step_type : REG_WRITE, reg_addr : 32'h260009, value : 32'h10}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Memclk=400MHz, Programming CPllDacValIn to 0x10
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102a1, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaPathPhase1 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102a2, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaPathPhase2 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102a3, value : 32'hda}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaPathPhase3 to 0xda
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102a4, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaPathPhase4 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112a1, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaPathPhase1 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112a2, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaPathPhase2 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112a3, value : 32'hda}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaPathPhase3 to 0xda
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112a4, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaPathPhase4 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122a1, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaPathPhase1 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122a2, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaPathPhase2 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122a3, value : 32'hda}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaPathPhase3 to 0xda
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122a4, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaPathPhase4 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132a1, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaPathPhase1 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132a2, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaPathPhase2 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132a3, value : 32'hda}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaPathPhase3 to 0xda
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132a4, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaPathPhase4 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132ad, value : 32'h2}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaCtl01::RxReplicaSelPathPhase to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h2102af, value : 32'h46}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE0.RxReplicaCtl03 to 0x46
                          '{ step_type : REG_WRITE, reg_addr : 32'h2112af, value : 32'h46}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE1.RxReplicaCtl03 to 0x46
                          '{ step_type : REG_WRITE, reg_addr : 32'h2122af, value : 32'h46}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE2.RxReplicaCtl03 to 0x46
                          '{ step_type : REG_WRITE, reg_addr : 32'h2132af, value : 32'h46}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming DBYTE3.RxReplicaCtl03 to 0x46
                          '{ step_type : REG_WRITE, reg_addr : 32'h290807, value : 32'h9701}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming Seq0BGPR7 to save ZQCalCodeOvrValPU=0x12e and ZQCalCodeOvrEnPU=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h290808, value : 32'hb681}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=2, Programming Seq0BGPR8 to save ZQCalCodeOvrValPD=0x16d and ZQCalCodeOvrEnPD=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
//[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] End of dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(), PState=2
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Start of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=2
                          '{ step_type : REG_WRITE, reg_addr : 32'h260008, value : 32'h4956}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_I_loadPIEImagePsLoop] Pstate=2,  Memclk=400MHz, Programming CpllCtrl5 to 0x4956.
                          '{ step_type : REG_WRITE, reg_addr : 32'h60006, value : 32'h3f0}, //End of dwc_ddrphy_phyinit_programPLL(), PState=2
                          '{ step_type : REG_WRITE, reg_addr : 32'h230015, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h231015, value : 32'h0}, //phyinit_io_write: 0x230015, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21007c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21107c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21207c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21307c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h270141, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming ACSMWckFreeRunMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming GPR12 with Zcalkclkdiv to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h210027, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming RxClkCntl1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h211027, value : 32'h0}, //phyinit_io_write: 0x210027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h212027, value : 32'h0}, //phyinit_io_write: 0x211027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h213027, value : 32'h0}, //phyinit_io_write: 0x212027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h21020f, value : 32'h8}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=2, Programming RxReplicaCtl04 to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h21120f, value : 32'h8}, //phyinit_io_write: 0x21020f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h21220f, value : 32'h8}, //phyinit_io_write: 0x21120f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h21320f, value : 32'h8}, //phyinit_io_write: 0x21220f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e003f, value : 32'h0}, //phyinit_io_write: 0x21320f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e008d, value : 32'h0}, //phyinit_io_write: 0x2e003f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e103f, value : 32'h0}, //phyinit_io_write: 0x2e008d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e108d, value : 32'h0}, //phyinit_io_write: 0x2e103f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e203f, value : 32'h0}, //phyinit_io_write: 0x2e108d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e208d, value : 32'h0}, //phyinit_io_write: 0x2e203f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e303f, value : 32'h0}, //phyinit_io_write: 0x2e208d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e308d, value : 32'h0}, //phyinit_io_write: 0x2e303f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e403f, value : 32'h0}, //phyinit_io_write: 0x2e308d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e408d, value : 32'h0}, //phyinit_io_write: 0x2e403f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e503f, value : 32'h0}, //phyinit_io_write: 0x2e408d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e508d, value : 32'h0}, //phyinit_io_write: 0x2e503f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e603f, value : 32'h0}, //phyinit_io_write: 0x2e508d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e608d, value : 32'h0}, //phyinit_io_write: 0x2e603f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e703f, value : 32'h0}, //phyinit_io_write: 0x2e608d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h2e708d, value : 32'h0}, //phyinit_io_write: 0x2e703f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h290903, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] PState=2, Programming RtrnMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70072, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnA to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080e, value : 32'h3}, //phyinit_io_write: 0x70072, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70073, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnB to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h29080f, value : 32'h3}, //phyinit_io_write: 0x70073, 0x3
//phyinit_io_write: 0x29080f, 0x3
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] End of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=2
//[dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop] End of dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop(), PState=2
//Start of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), PState=3, tck_ps=5000ps
                          '{ step_type : REG_WRITE, reg_addr : 32'h2008b, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, programming PState = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h390801, value : 32'h8692}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming Seq0BGPR1 to 0x8692
                          '{ step_type : REG_WRITE, reg_addr : 32'h390802, value : 32'h0}, //phyinit_io_write: 0x390801, 0x8692
                          '{ step_type : REG_WRITE, reg_addr : 32'h390806, value : 32'h1}, //phyinit_io_write: 0x390802, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3a03ff, value : 32'h4101}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming OdtSeg120 to 0x4101
                          '{ step_type : REG_WRITE, reg_addr : 32'h3a030b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming ZCalCompCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h360008, value : 32'h4962}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_C_initPhyConfigPsLoop] Pstate=3,  Memclk=200MHz, Programming CpllCtrl5 to 0x4962.
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e0, value : 32'h19}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY0 to 0x19 (0.5us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e1, value : 32'h4b}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY1 to 0x4b (tZQCal PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e2, value : 32'h1f4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY2 to 0x1f4 (10.us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e3, value : 32'h40}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY3 to 0x40 (dllLock PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e4, value : 32'h5}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY4 to 0x5 (0.1us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e5, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY5 to 0x0 (RxReplicaCalWait delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e6, value : 32'h43}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY6 to 0x43 (Oscillator PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908e7, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY7 to 0x0 (tXDSM_XP PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908ea, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY10 to 0x1 (tPDXCSODTON 20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908eb, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY11 to 0x1 (20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908ec, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY12 to 0x3 (50ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h3908ed, value : 32'h14}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming Seq0BDLY13 to 0x14 (tXSR PIE delay, tRFCab delay is 380ns)
                          '{ step_type : REG_WRITE, reg_addr : 32'h320002, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming PclkPtrInitVal to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h360040, value : 32'h3}, //phyinit_io_write: 0x320002, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h320000, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DfiFreqRatio to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h3100fb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming RxDigStrbEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3110fb, value : 32'h0}, //phyinit_io_write: 0x3100fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3120fb, value : 32'h0}, //phyinit_io_write: 0x3110fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3130fb, value : 32'h0}, //phyinit_io_write: 0x3120fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e000b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DxDigStrobeMode HMDBYTE to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e100b, value : 32'h0}, //phyinit_io_write: 0x3e000b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e200b, value : 32'h0}, //phyinit_io_write: 0x3e100b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e300b, value : 32'h0}, //phyinit_io_write: 0x3e200b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e400b, value : 32'h0}, //phyinit_io_write: 0x3e300b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e500b, value : 32'h0}, //phyinit_io_write: 0x3e400b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e600b, value : 32'h0}, //phyinit_io_write: 0x3e500b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e700b, value : 32'h0}, //phyinit_io_write: 0x3e600b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h310024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE0.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h311024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE1.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h312024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE2.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h313024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE3.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h310025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE0.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h311025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE1.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h312025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE2.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h313025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE3.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h310004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE0.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h310003, value : 32'h0}, //phyinit_io_write: 0x310004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h311004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE1.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h311003, value : 32'h0}, //phyinit_io_write: 0x311004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h312004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE2.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h312003, value : 32'h0}, //phyinit_io_write: 0x312004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h313004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE3.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h313003, value : 32'h0}, //phyinit_io_write: 0x313004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3b0004, value : 32'hc8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ZCalClkInfo::ZCalDfiClkTicksPer1uS to 0xc8
                          '{ step_type : REG_WRITE, reg_addr : 32'h3a030c, value : 32'h0},
                          '{ step_type : REG_WRITE, reg_addr : 32'h31003e, value : 32'h5}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE RxGainCurrAdjRxReplica to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h31103e, value : 32'h5}, //phyinit_io_write: 0x31003e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h31203e, value : 32'h5}, //phyinit_io_write: 0x31103e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h31303e, value : 32'h5}, //phyinit_io_write: 0x31203e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h320003, value : 32'h1}, //phyinit_io_write: 0x31303e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h32000b, value : 32'h1111}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming CPclkDivRatio to 0x1111
                          '{ step_type : REG_WRITE, reg_addr : 32'h310108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE0.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h311108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE1.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h312108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE2.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h313108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming DBYTE3.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70005, value : 32'h0}, //[phyinit_C_initPhyConfig] Programming EnPhyUpdZQCalUpdate to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h7000f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming DisableZQupdateOnSnoop to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31000e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h31100e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h31200e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h31300e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h320019, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming EnRxDqsTracking::DqsSampNegRxEnSense to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e002c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e102c, value : 32'h33}, //phyinit_io_write: 0x3e002c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e002d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e102d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e202c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e302c, value : 32'h33}, //phyinit_io_write: 0x3e202c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e202d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e302d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e402c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e502c, value : 32'h33}, //phyinit_io_write: 0x3e402c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e402d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e502d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e602c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e702c, value : 32'h33}, //phyinit_io_write: 0x3e602c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e602d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e702d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h300070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC0 Instance0 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h301070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC1 Instance1 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h302070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC2 Instance2 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h303070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC3 Instance3 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h304070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming AC0 HMAC4 Instance4 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h305070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC5 Instance5 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h307070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC0 Instance7 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h308070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC1 Instance8 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h309070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC2 Instance9 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h30a070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC3 Instance10 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h30b070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming AC1 HMAC4 Instance11 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h30c070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC5 Instance12 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e002e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e102e, value : 32'h30}, //phyinit_io_write: 0x3e002e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e002f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e102f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e202e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e302e, value : 32'h30}, //phyinit_io_write: 0x3e202e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e202f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e302f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e402e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e502e, value : 32'h30}, //phyinit_io_write: 0x3e402e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e402f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e502f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e602e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e702e, value : 32'h30}, //phyinit_io_write: 0x3e602e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e602f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e702f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h300079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC0 Instance0 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h301079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC1 Instance1 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h302079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC2 Instance2 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h303079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC3 Instance3 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h304079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC4 Instance4 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h305079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC5 DIFF5 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h307079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC0 Instance7 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h308079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC1 Instance8 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h309079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC2 Instance9 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h30a079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC3 Instance10 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h30b079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC4 Instance11 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h30c079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC5 DIFF12 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e001c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 0 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e101c, value : 32'h3}, //phyinit_io_write: 0x3e001c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e201c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 1 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e301c, value : 32'h3}, //phyinit_io_write: 0x3e201c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e401c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 2 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e501c, value : 32'h3}, //phyinit_io_write: 0x3e401c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e601c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming HMDBYTE 3 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e701c, value : 32'h3}, //phyinit_io_write: 0x3e601c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h30006d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC0 Instance0 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30106d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC1 Instance1 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30206d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC2 Instance2 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30306d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC3 Instance3 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30406d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC4 Instance4 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h30506d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX0 HMAC5 Instance5 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30706d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC0 Instance7 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30806d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC1 Instance8 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30906d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC2 Instance9 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30a06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC3 Instance10 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30b06d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC4 Instance11 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h30c06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACX1 HMAC5 Instance12 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e003e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming HMDBYTE RxDQSCtrl::RxDQSDiffSeVrefDACEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e103e, value : 32'h0}, //phyinit_io_write: 0x3e003e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e203e, value : 32'h0}, //phyinit_io_write: 0x3e103e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e303e, value : 32'h0}, //phyinit_io_write: 0x3e203e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e403e, value : 32'h0}, //phyinit_io_write: 0x3e303e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e503e, value : 32'h0}, //phyinit_io_write: 0x3e403e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e603e, value : 32'h0}, //phyinit_io_write: 0x3e503e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e703e, value : 32'h0}, //phyinit_io_write: 0x3e603e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h310001, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming WriteLinkEcc to 0
                          '{ step_type : REG_WRITE, reg_addr : 32'h311001, value : 32'h0}, //phyinit_io_write: 0x310001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h312001, value : 32'h0}, //phyinit_io_write: 0x311001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h313001, value : 32'h0}, //phyinit_io_write: 0x312001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h370040, value : 32'h5a}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming PPTTrainSetup::PhyMstrMaxReqToAck to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h370041, value : 32'hf}, //phyinit_io_write: 0x370040, 0x5a
                          '{ step_type : REG_WRITE, reg_addr : 32'h3100a5, value : 32'h1}, //phyinit_io_write: 0x370041, 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h3110a5, value : 32'h1}, //phyinit_io_write: 0x3100a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3120a5, value : 32'h1}, //phyinit_io_write: 0x3110a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3130a5, value : 32'h1}, //phyinit_io_write: 0x3120a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h310209, value : 32'h3232}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming RxReplicaRangeVal 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h311209, value : 32'h3232}, //phyinit_io_write: 0x310209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h312209, value : 32'h3232}, //phyinit_io_write: 0x311209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h313209, value : 32'h3232}, //phyinit_io_write: 0x312209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h31020f, value : 32'h6}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming RxReplicaCtl04 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h31120f, value : 32'h6}, //phyinit_io_write: 0x31020f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h31220f, value : 32'h6}, //phyinit_io_write: 0x31120f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h31320f, value : 32'h6}, //phyinit_io_write: 0x31220f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h320005, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, DfiFreq=200MHz, Programming PipeCtl[AcInPipeEn]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h310008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, DfiFreq=200MHz, Programming DBYTE0.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h311008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, DfiFreq=200MHz, Programming DBYTE1.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h312008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, DfiFreq=200MHz, Programming DBYTE2.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h313008, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, DfiFreq=200MHz, Programming DBYTE3.LP5DfiDataEnLatency[LP5RLm13]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h37006b, value : 32'h222}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, DfiFreq=200MHz, Programming DfiHandshakeDelays[PhyUpdReqDelay]=0x2 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h370066, value : 32'h20}, //phyinit_io_write: 0x37006b, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h3700eb, value : 32'h222}, //phyinit_io_write: 0x370066, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h3700e6, value : 32'h20}, //phyinit_io_write: 0x3700eb, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h370135, value : 32'h400}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth to 0x19, ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleDelay to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h370136, value : 32'h400}, //phyinit_io_write: 0x370135, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h370137, value : 32'h404}, //phyinit_io_write: 0x370136, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h370138, value : 32'h1908}, //phyinit_io_write: 0x370137, 0x404
                          '{ step_type : REG_WRITE, reg_addr : 32'h370139, value : 32'h400}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleWidth to 0x21, ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleDelay to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h37013a, value : 32'h400}, //phyinit_io_write: 0x370139, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h37013b, value : 32'h404}, //phyinit_io_write: 0x37013a, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h37013c, value : 32'h2108}, //phyinit_io_write: 0x37013b, 0x404
                          '{ step_type : REG_WRITE, reg_addr : 32'h37013d, value : 32'h400}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleWidth to 0x11, ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleDelay to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h37013e, value : 32'h400}, //phyinit_io_write: 0x37013d, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h37013f, value : 32'h404}, //phyinit_io_write: 0x37013e, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h370140, value : 32'h1108}, //phyinit_io_write: 0x37013f, 0x404
                          '{ step_type : REG_WRITE, reg_addr : 32'h37012c, value : 32'h80f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMRxValPulse::ACSMRxValDelay to 0xf, ACSMRxValPulse::ACSMRxValWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h37012d, value : 32'h80f}, //phyinit_io_write: 0x37012c, 0x80f
                          '{ step_type : REG_WRITE, reg_addr : 32'h370130, value : 32'h80f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMRdcsPulse::ACSMRdcsDelay to 0xf, ACSMRdcsPulse::ACSMRdcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h37012e, value : 32'h807}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMTxEnPulse::ACSMTxEnDelay to 0x7, ACSMTxEnPulse::ACSMTxEnWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h37012f, value : 32'h807}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming ACSMWrcsPulse::ACSMWrcsDelay to 0x7, ACSMWrcsPulse::ACSMWrcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h330008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming AcPipeEn AC0 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h331008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, Programming AcPipeEn AC1 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0013, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming csr_EnaRxStrobeEnB to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1013, value : 32'h1}, //phyinit_io_write: 0x3e0013, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2013, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming csr_EnaRxStrobeEnB to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3013, value : 32'h1}, //phyinit_io_write: 0x3e2013, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4013, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming csr_EnaRxStrobeEnB to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5013, value : 32'h1}, //phyinit_io_write: 0x3e4013, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6013, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming csr_EnaRxStrobeEnB to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7013, value : 32'h1}, //phyinit_io_write: 0x3e6013, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0002, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Programming HMDBYTE RxDFECtrlDq to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1002, value : 32'h0}, //phyinit_io_write: 0x3e0002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2002, value : 32'h0}, //phyinit_io_write: 0x3e1002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3002, value : 32'h0}, //phyinit_io_write: 0x3e2002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4002, value : 32'h0}, //phyinit_io_write: 0x3e3002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5002, value : 32'h0}, //phyinit_io_write: 0x3e4002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6002, value : 32'h0}, //phyinit_io_write: 0x3e5002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7002, value : 32'h0}, //phyinit_io_write: 0x3e6002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31010b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=3, Memclk=200MHz, freqThreshold=200MHz, NoRDQS=0 Programming InhibitTxRdPtrInit::DisableRxEnDlyLoad to 0x0, InhibitTxRdPtrInit::DisableTxDqDly to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31110b, value : 32'h0}, //phyinit_io_write: 0x31010b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31210b, value : 32'h0}, //phyinit_io_write: 0x31110b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31310b, value : 32'h0}, //phyinit_io_write: 0x31210b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h300063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h301063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h302063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h303063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h304063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h305063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h307063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h308063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h309063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h30a063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h30b063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h30c063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080a, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR10 to HMTxLcdlSeed Full search value = 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080b, value : 32'h2d0}, //phyinit_io_write: 0x39080a, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h390815, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR21 to ACHMTxLcdlSeed Full search value = 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h390816, value : 32'h2d0}, //phyinit_io_write: 0x390815, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0063, value : 32'h2d0}, //phyinit_io_write: 0x390816, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0064, value : 32'h2d0}, //phyinit_io_write: 0x3e0063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0087, value : 32'h2d0}, //phyinit_io_write: 0x3e0064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1063, value : 32'h2d0}, //phyinit_io_write: 0x3e0087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1064, value : 32'h2d0}, //phyinit_io_write: 0x3e1063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1087, value : 32'h2d0}, //phyinit_io_write: 0x3e1064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2063, value : 32'h2d0}, //phyinit_io_write: 0x3e1087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2064, value : 32'h2d0}, //phyinit_io_write: 0x3e2063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2087, value : 32'h2d0}, //phyinit_io_write: 0x3e2064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3063, value : 32'h2d0}, //phyinit_io_write: 0x3e2087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3064, value : 32'h2d0}, //phyinit_io_write: 0x3e3063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3087, value : 32'h2d0}, //phyinit_io_write: 0x3e3064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4063, value : 32'h2d0}, //phyinit_io_write: 0x3e3087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4064, value : 32'h2d0}, //phyinit_io_write: 0x3e4063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4087, value : 32'h2d0}, //phyinit_io_write: 0x3e4064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5063, value : 32'h2d0}, //phyinit_io_write: 0x3e4087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5064, value : 32'h2d0}, //phyinit_io_write: 0x3e5063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5087, value : 32'h2d0}, //phyinit_io_write: 0x3e5064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6063, value : 32'h2d0}, //phyinit_io_write: 0x3e5087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6064, value : 32'h2d0}, //phyinit_io_write: 0x3e6063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6087, value : 32'h2d0}, //phyinit_io_write: 0x3e6064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7063, value : 32'h2d0}, //phyinit_io_write: 0x3e6087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7064, value : 32'h2d0}, //phyinit_io_write: 0x3e7063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7087, value : 32'h2d0}, //phyinit_io_write: 0x3e7064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc0080, value : 32'h7}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming UcclkHclkEnables to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e003c, value : 32'h80}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming RxDQSSeVrefDAC0 to 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e103c, value : 32'h80}, //phyinit_io_write: 0x3e003c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e203c, value : 32'h80}, //phyinit_io_write: 0x3e103c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e303c, value : 32'h80}, //phyinit_io_write: 0x3e203c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e403c, value : 32'h80}, //phyinit_io_write: 0x3e303c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e503c, value : 32'h80}, //phyinit_io_write: 0x3e403c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e603c, value : 32'h80}, //phyinit_io_write: 0x3e503c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e703c, value : 32'h80}, //phyinit_io_write: 0x3e603c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h390817, value : 32'h14}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 3 Seq0BGPR23 to 0x14, NumMemClk_tRFCab=82.0, NumMemClk_7p5ns=1.5, NumMemClk_tXSR=84.0
                          '{ step_type : REG_WRITE, reg_addr : 32'h390818, value : 32'h0}, //phyinit_io_write: 0x390817, 0x14
                          '{ step_type : REG_WRITE, reg_addr : 32'h390819, value : 32'h0}, //phyinit_io_write: 0x390818, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3300eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 3 AC0 AcLcdlUpdInterval to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3310eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 3 AC1 AcLcdlUpdInterval to 0x0
//[dwc_ddrphy_phyinit_programDfiMode] Skip DfiMode Programming: Keeping the reset value of 0x3
//End of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), Pstate=3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3300d9, value : 32'h40}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming CKXTxDly to 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3300d8, value : 32'h40}, //phyinit_io_write: 0x3300d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3301d8, value : 32'h40}, //phyinit_io_write: 0x3300d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3302d8, value : 32'h40}, //phyinit_io_write: 0x3301d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3303d8, value : 32'h40}, //phyinit_io_write: 0x3302d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3304d8, value : 32'h40}, //phyinit_io_write: 0x3303d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3305d8, value : 32'h40}, //phyinit_io_write: 0x3304d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3306d8, value : 32'h40}, //phyinit_io_write: 0x3305d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3308d8, value : 32'h40}, //phyinit_io_write: 0x3306d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3309d8, value : 32'h40}, //phyinit_io_write: 0x3308d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3310d9, value : 32'h40}, //phyinit_io_write: 0x3309d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3310d8, value : 32'h40}, //phyinit_io_write: 0x3310d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3311d8, value : 32'h40}, //phyinit_io_write: 0x3310d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3312d8, value : 32'h40}, //phyinit_io_write: 0x3311d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3313d8, value : 32'h40}, //phyinit_io_write: 0x3312d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3314d8, value : 32'h40}, //phyinit_io_write: 0x3313d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3315d8, value : 32'h40}, //phyinit_io_write: 0x3314d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3316d8, value : 32'h40}, //phyinit_io_write: 0x3315d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3318d8, value : 32'h40}, //phyinit_io_write: 0x3316d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h3319d8, value : 32'h40}, //phyinit_io_write: 0x3318d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h310000, value : 32'h5}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming HwtMRL to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h311000, value : 32'h5}, //phyinit_io_write: 0x310000, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h312000, value : 32'h5}, //phyinit_io_write: 0x311000, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h313000, value : 32'h5}, //phyinit_io_write: 0x312000, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h37000d, value : 32'h5}, //phyinit_io_write: 0x313000, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h31002a, value : 32'h200}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming TxWckDlyTg0/Tg1 to 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31002b, value : 32'h200}, //phyinit_io_write: 0x31002a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31102a, value : 32'h200}, //phyinit_io_write: 0x31002b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31102b, value : 32'h200}, //phyinit_io_write: 0x31102a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31202a, value : 32'h200}, //phyinit_io_write: 0x31102b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31202b, value : 32'h200}, //phyinit_io_write: 0x31202a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31302a, value : 32'h200}, //phyinit_io_write: 0x31202b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h31302b, value : 32'h200}, //phyinit_io_write: 0x31302a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h310028, value : 32'h54}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming TxDqsDlyTg0/Tg1 to 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h310029, value : 32'h54}, //phyinit_io_write: 0x310028, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h311028, value : 32'h54}, //phyinit_io_write: 0x310029, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h311029, value : 32'h54}, //phyinit_io_write: 0x311028, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h312028, value : 32'h54}, //phyinit_io_write: 0x311029, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h312029, value : 32'h54}, //phyinit_io_write: 0x312028, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h313028, value : 32'h54}, //phyinit_io_write: 0x312029, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h313029, value : 32'h54}, //phyinit_io_write: 0x313028, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31007a, value : 32'h54}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming TxDqDlyTg0/Tg1 to 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31007b, value : 32'h54}, //phyinit_io_write: 0x31007a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31017a, value : 32'h54}, //phyinit_io_write: 0x31007b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31017b, value : 32'h54}, //phyinit_io_write: 0x31017a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31027a, value : 32'h54}, //phyinit_io_write: 0x31017b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31027b, value : 32'h54}, //phyinit_io_write: 0x31027a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31037a, value : 32'h54}, //phyinit_io_write: 0x31027b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31037b, value : 32'h54}, //phyinit_io_write: 0x31037a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31047a, value : 32'h54}, //phyinit_io_write: 0x31037b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31047b, value : 32'h54}, //phyinit_io_write: 0x31047a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31057a, value : 32'h54}, //phyinit_io_write: 0x31047b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31057b, value : 32'h54}, //phyinit_io_write: 0x31057a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31067a, value : 32'h54}, //phyinit_io_write: 0x31057b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31067b, value : 32'h54}, //phyinit_io_write: 0x31067a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31077a, value : 32'h54}, //phyinit_io_write: 0x31067b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31077b, value : 32'h54}, //phyinit_io_write: 0x31077a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31087a, value : 32'h54}, //phyinit_io_write: 0x31077b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31087b, value : 32'h54}, //phyinit_io_write: 0x31087a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31107a, value : 32'h54}, //phyinit_io_write: 0x31087b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31107b, value : 32'h54}, //phyinit_io_write: 0x31107a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31117a, value : 32'h54}, //phyinit_io_write: 0x31107b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31117b, value : 32'h54}, //phyinit_io_write: 0x31117a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31127a, value : 32'h54}, //phyinit_io_write: 0x31117b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31127b, value : 32'h54}, //phyinit_io_write: 0x31127a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31137a, value : 32'h54}, //phyinit_io_write: 0x31127b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31137b, value : 32'h54}, //phyinit_io_write: 0x31137a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31147a, value : 32'h54}, //phyinit_io_write: 0x31137b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31147b, value : 32'h54}, //phyinit_io_write: 0x31147a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31157a, value : 32'h54}, //phyinit_io_write: 0x31147b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31157b, value : 32'h54}, //phyinit_io_write: 0x31157a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31167a, value : 32'h54}, //phyinit_io_write: 0x31157b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31167b, value : 32'h54}, //phyinit_io_write: 0x31167a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31177a, value : 32'h54}, //phyinit_io_write: 0x31167b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31177b, value : 32'h54}, //phyinit_io_write: 0x31177a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31187a, value : 32'h54}, //phyinit_io_write: 0x31177b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31187b, value : 32'h54}, //phyinit_io_write: 0x31187a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31207a, value : 32'h54}, //phyinit_io_write: 0x31187b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31207b, value : 32'h54}, //phyinit_io_write: 0x31207a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31217a, value : 32'h54}, //phyinit_io_write: 0x31207b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31217b, value : 32'h54}, //phyinit_io_write: 0x31217a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31227a, value : 32'h54}, //phyinit_io_write: 0x31217b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31227b, value : 32'h54}, //phyinit_io_write: 0x31227a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31237a, value : 32'h54}, //phyinit_io_write: 0x31227b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31237b, value : 32'h54}, //phyinit_io_write: 0x31237a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31247a, value : 32'h54}, //phyinit_io_write: 0x31237b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31247b, value : 32'h54}, //phyinit_io_write: 0x31247a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31257a, value : 32'h54}, //phyinit_io_write: 0x31247b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31257b, value : 32'h54}, //phyinit_io_write: 0x31257a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31267a, value : 32'h54}, //phyinit_io_write: 0x31257b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31267b, value : 32'h54}, //phyinit_io_write: 0x31267a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31277a, value : 32'h54}, //phyinit_io_write: 0x31267b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31277b, value : 32'h54}, //phyinit_io_write: 0x31277a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31287a, value : 32'h54}, //phyinit_io_write: 0x31277b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31287b, value : 32'h54}, //phyinit_io_write: 0x31287a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31307a, value : 32'h54}, //phyinit_io_write: 0x31287b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31307b, value : 32'h54}, //phyinit_io_write: 0x31307a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31317a, value : 32'h54}, //phyinit_io_write: 0x31307b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31317b, value : 32'h54}, //phyinit_io_write: 0x31317a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31327a, value : 32'h54}, //phyinit_io_write: 0x31317b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31327b, value : 32'h54}, //phyinit_io_write: 0x31327a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31337a, value : 32'h54}, //phyinit_io_write: 0x31327b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31337b, value : 32'h54}, //phyinit_io_write: 0x31337a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31347a, value : 32'h54}, //phyinit_io_write: 0x31337b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31347b, value : 32'h54}, //phyinit_io_write: 0x31347a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31357a, value : 32'h54}, //phyinit_io_write: 0x31347b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31357b, value : 32'h54}, //phyinit_io_write: 0x31357a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31367a, value : 32'h54}, //phyinit_io_write: 0x31357b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31367b, value : 32'h54}, //phyinit_io_write: 0x31367a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31377a, value : 32'h54}, //phyinit_io_write: 0x31367b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31377b, value : 32'h54}, //phyinit_io_write: 0x31377a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31387a, value : 32'h54}, //phyinit_io_write: 0x31377b, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h31387b, value : 32'h54}, //phyinit_io_write: 0x31387a, 0x54
                          '{ step_type : REG_WRITE, reg_addr : 32'h310078, value : 32'h286}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming RxDigStrbDlyTg0/Tg1 to 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310079, value : 32'h286}, //phyinit_io_write: 0x310078, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310178, value : 32'h286}, //phyinit_io_write: 0x310079, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310179, value : 32'h286}, //phyinit_io_write: 0x310178, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310278, value : 32'h286}, //phyinit_io_write: 0x310179, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310279, value : 32'h286}, //phyinit_io_write: 0x310278, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310378, value : 32'h286}, //phyinit_io_write: 0x310279, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310379, value : 32'h286}, //phyinit_io_write: 0x310378, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310478, value : 32'h286}, //phyinit_io_write: 0x310379, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310479, value : 32'h286}, //phyinit_io_write: 0x310478, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310578, value : 32'h286}, //phyinit_io_write: 0x310479, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310579, value : 32'h286}, //phyinit_io_write: 0x310578, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310678, value : 32'h286}, //phyinit_io_write: 0x310579, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310679, value : 32'h286}, //phyinit_io_write: 0x310678, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310778, value : 32'h286}, //phyinit_io_write: 0x310679, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310779, value : 32'h286}, //phyinit_io_write: 0x310778, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310878, value : 32'h286}, //phyinit_io_write: 0x310779, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310879, value : 32'h286}, //phyinit_io_write: 0x310878, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311078, value : 32'h286}, //phyinit_io_write: 0x310879, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311079, value : 32'h286}, //phyinit_io_write: 0x311078, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311178, value : 32'h286}, //phyinit_io_write: 0x311079, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311179, value : 32'h286}, //phyinit_io_write: 0x311178, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311278, value : 32'h286}, //phyinit_io_write: 0x311179, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311279, value : 32'h286}, //phyinit_io_write: 0x311278, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311378, value : 32'h286}, //phyinit_io_write: 0x311279, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311379, value : 32'h286}, //phyinit_io_write: 0x311378, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311478, value : 32'h286}, //phyinit_io_write: 0x311379, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311479, value : 32'h286}, //phyinit_io_write: 0x311478, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311578, value : 32'h286}, //phyinit_io_write: 0x311479, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311579, value : 32'h286}, //phyinit_io_write: 0x311578, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311678, value : 32'h286}, //phyinit_io_write: 0x311579, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311679, value : 32'h286}, //phyinit_io_write: 0x311678, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311778, value : 32'h286}, //phyinit_io_write: 0x311679, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311779, value : 32'h286}, //phyinit_io_write: 0x311778, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311878, value : 32'h286}, //phyinit_io_write: 0x311779, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h311879, value : 32'h286}, //phyinit_io_write: 0x311878, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312078, value : 32'h286}, //phyinit_io_write: 0x311879, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312079, value : 32'h286}, //phyinit_io_write: 0x312078, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312178, value : 32'h286}, //phyinit_io_write: 0x312079, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312179, value : 32'h286}, //phyinit_io_write: 0x312178, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312278, value : 32'h286}, //phyinit_io_write: 0x312179, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312279, value : 32'h286}, //phyinit_io_write: 0x312278, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312378, value : 32'h286}, //phyinit_io_write: 0x312279, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312379, value : 32'h286}, //phyinit_io_write: 0x312378, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312478, value : 32'h286}, //phyinit_io_write: 0x312379, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312479, value : 32'h286}, //phyinit_io_write: 0x312478, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312578, value : 32'h286}, //phyinit_io_write: 0x312479, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312579, value : 32'h286}, //phyinit_io_write: 0x312578, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312678, value : 32'h286}, //phyinit_io_write: 0x312579, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312679, value : 32'h286}, //phyinit_io_write: 0x312678, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312778, value : 32'h286}, //phyinit_io_write: 0x312679, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312779, value : 32'h286}, //phyinit_io_write: 0x312778, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312878, value : 32'h286}, //phyinit_io_write: 0x312779, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h312879, value : 32'h286}, //phyinit_io_write: 0x312878, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313078, value : 32'h286}, //phyinit_io_write: 0x312879, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313079, value : 32'h286}, //phyinit_io_write: 0x313078, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313178, value : 32'h286}, //phyinit_io_write: 0x313079, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313179, value : 32'h286}, //phyinit_io_write: 0x313178, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313278, value : 32'h286}, //phyinit_io_write: 0x313179, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313279, value : 32'h286}, //phyinit_io_write: 0x313278, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313378, value : 32'h286}, //phyinit_io_write: 0x313279, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313379, value : 32'h286}, //phyinit_io_write: 0x313378, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313478, value : 32'h286}, //phyinit_io_write: 0x313379, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313479, value : 32'h286}, //phyinit_io_write: 0x313478, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313578, value : 32'h286}, //phyinit_io_write: 0x313479, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313579, value : 32'h286}, //phyinit_io_write: 0x313578, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313678, value : 32'h286}, //phyinit_io_write: 0x313579, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313679, value : 32'h286}, //phyinit_io_write: 0x313678, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313778, value : 32'h286}, //phyinit_io_write: 0x313679, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313779, value : 32'h286}, //phyinit_io_write: 0x313778, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313878, value : 32'h286}, //phyinit_io_write: 0x313779, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h313879, value : 32'h286}, //phyinit_io_write: 0x313878, 0x286
                          '{ step_type : REG_WRITE, reg_addr : 32'h310020, value : 32'h1e6}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming RxEnDlyTg0/Tg1 to 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h310021, value : 32'h1e6}, //phyinit_io_write: 0x310020, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h311020, value : 32'h1e6}, //phyinit_io_write: 0x310021, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h311021, value : 32'h1e6}, //phyinit_io_write: 0x311020, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h312020, value : 32'h1e6}, //phyinit_io_write: 0x311021, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h312021, value : 32'h1e6}, //phyinit_io_write: 0x312020, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h313020, value : 32'h1e6}, //phyinit_io_write: 0x312021, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h313021, value : 32'h1e6}, //phyinit_io_write: 0x313020, 0x1e6
                          '{ step_type : REG_WRITE, reg_addr : 32'h310010, value : 32'h202}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming RxClkT2UIDlyTg0/Tg1 and RxClkC2UIDlyTg0/Tg1 to 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310011, value : 32'h202}, //phyinit_io_write: 0x310010, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310012, value : 32'h202}, //phyinit_io_write: 0x310011, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310013, value : 32'h202}, //phyinit_io_write: 0x310012, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310110, value : 32'h202}, //phyinit_io_write: 0x310013, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310111, value : 32'h202}, //phyinit_io_write: 0x310110, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310112, value : 32'h202}, //phyinit_io_write: 0x310111, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310113, value : 32'h202}, //phyinit_io_write: 0x310112, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310210, value : 32'h202}, //phyinit_io_write: 0x310113, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310211, value : 32'h202}, //phyinit_io_write: 0x310210, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310212, value : 32'h202}, //phyinit_io_write: 0x310211, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310213, value : 32'h202}, //phyinit_io_write: 0x310212, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310310, value : 32'h202}, //phyinit_io_write: 0x310213, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310311, value : 32'h202}, //phyinit_io_write: 0x310310, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310312, value : 32'h202}, //phyinit_io_write: 0x310311, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310313, value : 32'h202}, //phyinit_io_write: 0x310312, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310410, value : 32'h202}, //phyinit_io_write: 0x310313, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310411, value : 32'h202}, //phyinit_io_write: 0x310410, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310412, value : 32'h202}, //phyinit_io_write: 0x310411, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310413, value : 32'h202}, //phyinit_io_write: 0x310412, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310510, value : 32'h202}, //phyinit_io_write: 0x310413, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310511, value : 32'h202}, //phyinit_io_write: 0x310510, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310512, value : 32'h202}, //phyinit_io_write: 0x310511, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310513, value : 32'h202}, //phyinit_io_write: 0x310512, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310610, value : 32'h202}, //phyinit_io_write: 0x310513, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310611, value : 32'h202}, //phyinit_io_write: 0x310610, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310612, value : 32'h202}, //phyinit_io_write: 0x310611, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310613, value : 32'h202}, //phyinit_io_write: 0x310612, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310710, value : 32'h202}, //phyinit_io_write: 0x310613, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310711, value : 32'h202}, //phyinit_io_write: 0x310710, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310712, value : 32'h202}, //phyinit_io_write: 0x310711, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310713, value : 32'h202}, //phyinit_io_write: 0x310712, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310810, value : 32'h202}, //phyinit_io_write: 0x310713, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310811, value : 32'h202}, //phyinit_io_write: 0x310810, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310812, value : 32'h202}, //phyinit_io_write: 0x310811, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h310813, value : 32'h202}, //phyinit_io_write: 0x310812, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311010, value : 32'h202}, //phyinit_io_write: 0x310813, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311011, value : 32'h202}, //phyinit_io_write: 0x311010, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311012, value : 32'h202}, //phyinit_io_write: 0x311011, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311013, value : 32'h202}, //phyinit_io_write: 0x311012, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311110, value : 32'h202}, //phyinit_io_write: 0x311013, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311111, value : 32'h202}, //phyinit_io_write: 0x311110, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311112, value : 32'h202}, //phyinit_io_write: 0x311111, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311113, value : 32'h202}, //phyinit_io_write: 0x311112, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311210, value : 32'h202}, //phyinit_io_write: 0x311113, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311211, value : 32'h202}, //phyinit_io_write: 0x311210, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311212, value : 32'h202}, //phyinit_io_write: 0x311211, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311213, value : 32'h202}, //phyinit_io_write: 0x311212, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311310, value : 32'h202}, //phyinit_io_write: 0x311213, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311311, value : 32'h202}, //phyinit_io_write: 0x311310, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311312, value : 32'h202}, //phyinit_io_write: 0x311311, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311313, value : 32'h202}, //phyinit_io_write: 0x311312, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311410, value : 32'h202}, //phyinit_io_write: 0x311313, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311411, value : 32'h202}, //phyinit_io_write: 0x311410, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311412, value : 32'h202}, //phyinit_io_write: 0x311411, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311413, value : 32'h202}, //phyinit_io_write: 0x311412, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311510, value : 32'h202}, //phyinit_io_write: 0x311413, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311511, value : 32'h202}, //phyinit_io_write: 0x311510, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311512, value : 32'h202}, //phyinit_io_write: 0x311511, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311513, value : 32'h202}, //phyinit_io_write: 0x311512, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311610, value : 32'h202}, //phyinit_io_write: 0x311513, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311611, value : 32'h202}, //phyinit_io_write: 0x311610, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311612, value : 32'h202}, //phyinit_io_write: 0x311611, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311613, value : 32'h202}, //phyinit_io_write: 0x311612, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311710, value : 32'h202}, //phyinit_io_write: 0x311613, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311711, value : 32'h202}, //phyinit_io_write: 0x311710, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311712, value : 32'h202}, //phyinit_io_write: 0x311711, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311713, value : 32'h202}, //phyinit_io_write: 0x311712, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311810, value : 32'h202}, //phyinit_io_write: 0x311713, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311811, value : 32'h202}, //phyinit_io_write: 0x311810, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311812, value : 32'h202}, //phyinit_io_write: 0x311811, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h311813, value : 32'h202}, //phyinit_io_write: 0x311812, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312010, value : 32'h202}, //phyinit_io_write: 0x311813, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312011, value : 32'h202}, //phyinit_io_write: 0x312010, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312012, value : 32'h202}, //phyinit_io_write: 0x312011, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312013, value : 32'h202}, //phyinit_io_write: 0x312012, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312110, value : 32'h202}, //phyinit_io_write: 0x312013, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312111, value : 32'h202}, //phyinit_io_write: 0x312110, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312112, value : 32'h202}, //phyinit_io_write: 0x312111, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312113, value : 32'h202}, //phyinit_io_write: 0x312112, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312210, value : 32'h202}, //phyinit_io_write: 0x312113, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312211, value : 32'h202}, //phyinit_io_write: 0x312210, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312212, value : 32'h202}, //phyinit_io_write: 0x312211, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312213, value : 32'h202}, //phyinit_io_write: 0x312212, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312310, value : 32'h202}, //phyinit_io_write: 0x312213, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312311, value : 32'h202}, //phyinit_io_write: 0x312310, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312312, value : 32'h202}, //phyinit_io_write: 0x312311, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312313, value : 32'h202}, //phyinit_io_write: 0x312312, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312410, value : 32'h202}, //phyinit_io_write: 0x312313, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312411, value : 32'h202}, //phyinit_io_write: 0x312410, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312412, value : 32'h202}, //phyinit_io_write: 0x312411, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312413, value : 32'h202}, //phyinit_io_write: 0x312412, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312510, value : 32'h202}, //phyinit_io_write: 0x312413, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312511, value : 32'h202}, //phyinit_io_write: 0x312510, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312512, value : 32'h202}, //phyinit_io_write: 0x312511, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312513, value : 32'h202}, //phyinit_io_write: 0x312512, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312610, value : 32'h202}, //phyinit_io_write: 0x312513, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312611, value : 32'h202}, //phyinit_io_write: 0x312610, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312612, value : 32'h202}, //phyinit_io_write: 0x312611, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312613, value : 32'h202}, //phyinit_io_write: 0x312612, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312710, value : 32'h202}, //phyinit_io_write: 0x312613, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312711, value : 32'h202}, //phyinit_io_write: 0x312710, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312712, value : 32'h202}, //phyinit_io_write: 0x312711, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312713, value : 32'h202}, //phyinit_io_write: 0x312712, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312810, value : 32'h202}, //phyinit_io_write: 0x312713, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312811, value : 32'h202}, //phyinit_io_write: 0x312810, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312812, value : 32'h202}, //phyinit_io_write: 0x312811, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h312813, value : 32'h202}, //phyinit_io_write: 0x312812, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313010, value : 32'h202}, //phyinit_io_write: 0x312813, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313011, value : 32'h202}, //phyinit_io_write: 0x313010, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313012, value : 32'h202}, //phyinit_io_write: 0x313011, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313013, value : 32'h202}, //phyinit_io_write: 0x313012, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313110, value : 32'h202}, //phyinit_io_write: 0x313013, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313111, value : 32'h202}, //phyinit_io_write: 0x313110, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313112, value : 32'h202}, //phyinit_io_write: 0x313111, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313113, value : 32'h202}, //phyinit_io_write: 0x313112, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313210, value : 32'h202}, //phyinit_io_write: 0x313113, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313211, value : 32'h202}, //phyinit_io_write: 0x313210, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313212, value : 32'h202}, //phyinit_io_write: 0x313211, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313213, value : 32'h202}, //phyinit_io_write: 0x313212, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313310, value : 32'h202}, //phyinit_io_write: 0x313213, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313311, value : 32'h202}, //phyinit_io_write: 0x313310, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313312, value : 32'h202}, //phyinit_io_write: 0x313311, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313313, value : 32'h202}, //phyinit_io_write: 0x313312, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313410, value : 32'h202}, //phyinit_io_write: 0x313313, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313411, value : 32'h202}, //phyinit_io_write: 0x313410, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313412, value : 32'h202}, //phyinit_io_write: 0x313411, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313413, value : 32'h202}, //phyinit_io_write: 0x313412, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313510, value : 32'h202}, //phyinit_io_write: 0x313413, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313511, value : 32'h202}, //phyinit_io_write: 0x313510, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313512, value : 32'h202}, //phyinit_io_write: 0x313511, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313513, value : 32'h202}, //phyinit_io_write: 0x313512, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313610, value : 32'h202}, //phyinit_io_write: 0x313513, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313611, value : 32'h202}, //phyinit_io_write: 0x313610, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313612, value : 32'h202}, //phyinit_io_write: 0x313611, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313613, value : 32'h202}, //phyinit_io_write: 0x313612, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313710, value : 32'h202}, //phyinit_io_write: 0x313613, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313711, value : 32'h202}, //phyinit_io_write: 0x313710, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313712, value : 32'h202}, //phyinit_io_write: 0x313711, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313713, value : 32'h202}, //phyinit_io_write: 0x313712, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313810, value : 32'h202}, //phyinit_io_write: 0x313713, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313811, value : 32'h202}, //phyinit_io_write: 0x313810, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313812, value : 32'h202}, //phyinit_io_write: 0x313811, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h313813, value : 32'h202}, //phyinit_io_write: 0x313812, 0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h31000c, value : 32'h34}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming PptWck2DqoCntInvTrn1 to 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31000d, value : 32'h34}, //phyinit_io_write: 0x31000c, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h310014, value : 32'h67}, //phyinit_io_write: 0x31000d, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h310015, value : 32'h67}, //phyinit_io_write: 0x310014, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31100c, value : 32'h34}, //phyinit_io_write: 0x310015, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31100d, value : 32'h34}, //phyinit_io_write: 0x31100c, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h311014, value : 32'h67}, //phyinit_io_write: 0x31100d, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h311015, value : 32'h67}, //phyinit_io_write: 0x311014, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31200c, value : 32'h34}, //phyinit_io_write: 0x311015, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31200d, value : 32'h34}, //phyinit_io_write: 0x31200c, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h312014, value : 32'h67}, //phyinit_io_write: 0x31200d, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h312015, value : 32'h67}, //phyinit_io_write: 0x312014, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31300c, value : 32'h34}, //phyinit_io_write: 0x312015, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h31300d, value : 32'h34}, //phyinit_io_write: 0x31300c, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h313014, value : 32'h67}, //phyinit_io_write: 0x31300d, 0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h313015, value : 32'h67}, //phyinit_io_write: 0x313014, 0x67
                          '{ step_type : REG_WRITE, reg_addr : 32'h70077, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming HwtCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h320071, value : 32'h44}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming HMRxReplicaLcdlSeed HMRxSeed to 0xd0 HMRxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h300063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h301063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h302063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h303063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h304063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h305063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h307063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h308063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h309063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h30a063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h30b063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h30c063, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=3, Memclk=200MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0xd0 HMTxSeedIs1UI 0x1 
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0063, value : 32'h2d0}, //phyinit_io_write: 0x30c063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0064, value : 32'h2d0}, //phyinit_io_write: 0x3e0063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e0087, value : 32'h2d0}, //phyinit_io_write: 0x3e0064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1063, value : 32'h2d0}, //phyinit_io_write: 0x3e0087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1064, value : 32'h2d0}, //phyinit_io_write: 0x3e1063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e1087, value : 32'h2d0}, //phyinit_io_write: 0x3e1064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2063, value : 32'h2d0}, //phyinit_io_write: 0x3e1087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2064, value : 32'h2d0}, //phyinit_io_write: 0x3e2063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e2087, value : 32'h2d0}, //phyinit_io_write: 0x3e2064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3063, value : 32'h2d0}, //phyinit_io_write: 0x3e2087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3064, value : 32'h2d0}, //phyinit_io_write: 0x3e3063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e3087, value : 32'h2d0}, //phyinit_io_write: 0x3e3064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4063, value : 32'h2d0}, //phyinit_io_write: 0x3e3087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4064, value : 32'h2d0}, //phyinit_io_write: 0x3e4063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e4087, value : 32'h2d0}, //phyinit_io_write: 0x3e4064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5063, value : 32'h2d0}, //phyinit_io_write: 0x3e4087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5064, value : 32'h2d0}, //phyinit_io_write: 0x3e5063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e5087, value : 32'h2d0}, //phyinit_io_write: 0x3e5064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6063, value : 32'h2d0}, //phyinit_io_write: 0x3e5087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6064, value : 32'h2d0}, //phyinit_io_write: 0x3e6063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e6087, value : 32'h2d0}, //phyinit_io_write: 0x3e6064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7063, value : 32'h2d0}, //phyinit_io_write: 0x3e6087, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7064, value : 32'h2d0}, //phyinit_io_write: 0x3e7063, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e7087, value : 32'h2d0}, //phyinit_io_write: 0x3e7064, 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080a, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=3 Programming Seq0bGPR10 to mission mode HMTxLcdlSeed value 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080b, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=3 Programming Seq0bGPR11 to mission mode HMTxLcdlSeed value 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h390815, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=3 Programming Seq0bGPR21 to mission mode HMTxLcdlSeed value 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h390816, value : 32'h2d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=3 Programming Seq0bGPR22 to mission mode HMTxLcdlSeed value 0x2d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31015f, value : 32'h14d0}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=3, Memclk=200MHz, Programming RDqRDqsCntrl to 0x14d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31115f, value : 32'h14d0}, //phyinit_io_write: 0x31015f, 0x14d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31215f, value : 32'h14d0}, //phyinit_io_write: 0x31115f, 0x14d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31315f, value : 32'h14d0}, //phyinit_io_write: 0x31215f, 0x14d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h360009, value : 32'h10}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Memclk=200MHz, Programming CPllDacValIn to 0x10
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102a1, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaPathPhase1 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102a2, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaPathPhase2 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102a3, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaPathPhase3 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102a4, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaPathPhase4 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112a1, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaPathPhase1 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112a2, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaPathPhase2 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112a3, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaPathPhase3 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112a4, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaPathPhase4 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122a1, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaPathPhase1 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122a2, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaPathPhase2 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122a3, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaPathPhase3 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122a4, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaPathPhase4 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132a1, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaPathPhase1 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132a2, value : 32'h142}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaPathPhase2 to 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132a3, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaPathPhase3 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132a4, value : 32'h1ff}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaPathPhase4 to 0x1ff
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102ad, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaCtl01::RxReplicaSelPathPhase to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112ad, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaCtl01::RxReplicaSelPathPhase to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122ad, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaCtl01::RxReplicaSelPathPhase to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132ad, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaCtl01::RxReplicaSelPathPhase to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h3102af, value : 32'h23}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE0.RxReplicaCtl03 to 0x23
                          '{ step_type : REG_WRITE, reg_addr : 32'h3112af, value : 32'h23}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE1.RxReplicaCtl03 to 0x23
                          '{ step_type : REG_WRITE, reg_addr : 32'h3122af, value : 32'h23}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE2.RxReplicaCtl03 to 0x23
                          '{ step_type : REG_WRITE, reg_addr : 32'h3132af, value : 32'h23}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming DBYTE3.RxReplicaCtl03 to 0x23
                          '{ step_type : REG_WRITE, reg_addr : 32'h390807, value : 32'h9701}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming Seq0BGPR7 to save ZQCalCodeOvrValPU=0x12e and ZQCalCodeOvrEnPU=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h390808, value : 32'hb681}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=3, Programming Seq0BGPR8 to save ZQCalCodeOvrValPD=0x16d and ZQCalCodeOvrEnPD=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
//[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] End of dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(), PState=3
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Start of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=3
                          '{ step_type : REG_WRITE, reg_addr : 32'h360008, value : 32'h4822}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_I_loadPIEImagePsLoop] Pstate=3,  Memclk=200MHz, Programming CpllCtrl5 to 0x4822.
                          '{ step_type : REG_WRITE, reg_addr : 32'h60006, value : 32'h3f0}, //End of dwc_ddrphy_phyinit_programPLL(), PState=3
                          '{ step_type : REG_WRITE, reg_addr : 32'h330015, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h331015, value : 32'h0}, //phyinit_io_write: 0x330015, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31007c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31107c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31207c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31307c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h370141, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming ACSMWckFreeRunMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming GPR12 with Zcalkclkdiv to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h310027, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming RxClkCntl1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h311027, value : 32'h0}, //phyinit_io_write: 0x310027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h312027, value : 32'h0}, //phyinit_io_write: 0x311027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h313027, value : 32'h0}, //phyinit_io_write: 0x312027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31020f, value : 32'h8}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=3, Programming RxReplicaCtl04 to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h31120f, value : 32'h8}, //phyinit_io_write: 0x31020f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h31220f, value : 32'h8}, //phyinit_io_write: 0x31120f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h31320f, value : 32'h8}, //phyinit_io_write: 0x31220f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e003f, value : 32'h0}, //phyinit_io_write: 0x31320f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e008d, value : 32'h0}, //phyinit_io_write: 0x3e003f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e103f, value : 32'h0}, //phyinit_io_write: 0x3e008d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e108d, value : 32'h0}, //phyinit_io_write: 0x3e103f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e203f, value : 32'h0}, //phyinit_io_write: 0x3e108d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e208d, value : 32'h0}, //phyinit_io_write: 0x3e203f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e303f, value : 32'h0}, //phyinit_io_write: 0x3e208d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e308d, value : 32'h0}, //phyinit_io_write: 0x3e303f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e403f, value : 32'h0}, //phyinit_io_write: 0x3e308d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e408d, value : 32'h0}, //phyinit_io_write: 0x3e403f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e503f, value : 32'h0}, //phyinit_io_write: 0x3e408d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e508d, value : 32'h0}, //phyinit_io_write: 0x3e503f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e603f, value : 32'h0}, //phyinit_io_write: 0x3e508d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e608d, value : 32'h0}, //phyinit_io_write: 0x3e603f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e703f, value : 32'h0}, //phyinit_io_write: 0x3e608d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h3e708d, value : 32'h0}, //phyinit_io_write: 0x3e703f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h390903, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] PState=3, Programming RtrnMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70072, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnA to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080e, value : 32'h3}, //phyinit_io_write: 0x70072, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70073, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnB to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h39080f, value : 32'h3}, //phyinit_io_write: 0x70073, 0x3
//phyinit_io_write: 0x39080f, 0x3
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] End of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=3
//[dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop] End of dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop(), PState=3
//Start of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), PState=0, tck_ps=1250ps
                          '{ step_type : REG_WRITE, reg_addr : 32'h2008b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, programming PState = 0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90801, value : 32'hc0a2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming Seq0BGPR1 to 0xc0a2
                          '{ step_type : REG_WRITE, reg_addr : 32'h90802, value : 32'h0}, //phyinit_io_write: 0x90801, 0xc0a2
                          '{ step_type : REG_WRITE, reg_addr : 32'h90806, value : 32'h1}, //phyinit_io_write: 0x90802, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'ha03ff, value : 32'h4101}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming OdtSeg120 to 0x4101
                          '{ step_type : REG_WRITE, reg_addr : 32'ha030b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming ZCalCompCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h60008, value : 32'h2e9a}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_C_initPhyConfigPsLoop] Pstate=0,  Memclk=800MHz, Programming CpllCtrl5 to 0x2e9a.
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e0, value : 32'h64}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY0 to 0x64 (0.5us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e1, value : 32'h12c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY1 to 0x12c (tZQCal PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e2, value : 32'h7d0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY2 to 0x7d0 (10.us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e3, value : 32'h58}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY3 to 0x58 (dllLock PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e4, value : 32'h14}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY4 to 0x14 (0.1us PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e5, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY5 to 0x0 (RxReplicaCalWait delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e6, value : 32'h43}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY6 to 0x43 (Oscillator PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e7, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY7 to 0x0 (tXDSM_XP PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908ea, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY10 to 0x4 (tPDXCSODTON 20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908eb, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY11 to 0x4 (20ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908ec, value : 32'ha}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY12 to 0xa (50ns PIE delay)
                          '{ step_type : REG_WRITE, reg_addr : 32'h908ed, value : 32'h4e}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming Seq0BDLY13 to 0x4e (tXSR PIE delay, tRFCab delay is 380ns)
                          '{ step_type : REG_WRITE, reg_addr : 32'h20002, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming PclkPtrInitVal to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h60040, value : 32'h3}, //phyinit_io_write: 0x20002, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h20000, value : 32'h2}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DfiFreqRatio to 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h100fb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming RxDigStrbEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h110fb, value : 32'h0}, //phyinit_io_write: 0x100fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h120fb, value : 32'h0}, //phyinit_io_write: 0x110fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h130fb, value : 32'h0}, //phyinit_io_write: 0x120fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he000b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DxDigStrobeMode HMDBYTE to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he100b, value : 32'h0}, //phyinit_io_write: 0xe000b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he200b, value : 32'h0}, //phyinit_io_write: 0xe100b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he300b, value : 32'h0}, //phyinit_io_write: 0xe200b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he400b, value : 32'h0}, //phyinit_io_write: 0xe300b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he500b, value : 32'h0}, //phyinit_io_write: 0xe400b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he600b, value : 32'h0}, //phyinit_io_write: 0xe500b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he700b, value : 32'h0}, //phyinit_io_write: 0xe600b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE0.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE1.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE2.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13024, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE3.DqsPreambleControl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE0.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h11025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE1.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h12025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE2.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h13025, value : 32'h2c}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE3.DbyteRxDqsModeCntrl to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h10004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE0.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10003, value : 32'h0}, //phyinit_io_write: 0x10004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE1.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11003, value : 32'h0}, //phyinit_io_write: 0x11004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE2.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12003, value : 32'h0}, //phyinit_io_write: 0x12004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13004, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE3.DxDfiClkDis to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13003, value : 32'h0}, //phyinit_io_write: 0x13004, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb0004, value : 32'h320}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ZCalClkInfo::ZCalDfiClkTicksPer1uS to 0x320
                          '{ step_type : REG_WRITE, reg_addr : 32'ha030c, value : 32'h0},
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003e, value : 32'h5}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE RxGainCurrAdjRxReplica to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103e, value : 32'h5}, //phyinit_io_write: 0x1003e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203e, value : 32'h5}, //phyinit_io_write: 0x1103e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303e, value : 32'h5}, //phyinit_io_write: 0x1203e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h20003, value : 32'h1}, //phyinit_io_write: 0x1303e, 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h2000b, value : 32'h1111}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming CPclkDivRatio to 0x1111
                          '{ step_type : REG_WRITE, reg_addr : 32'h10108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE0.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE1.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE2.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13108, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming DBYTE3.DMIPinPresent::RdDbiEnabled to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70005, value : 32'h0}, //[phyinit_C_initPhyConfig] Programming EnPhyUpdZQCalUpdate to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h7000f, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming DisableZQupdateOnSnoop to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1000e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h1100e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h1200e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h1300e, value : 32'h1300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming TrackingModeCntrl to 0x1300
                          '{ step_type : REG_WRITE, reg_addr : 32'h20019, value : 32'h4}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming EnRxDqsTracking::DqsSampNegRxEnSense to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he002c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he102c, value : 32'h33}, //phyinit_io_write: 0xe002c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'he002d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he102d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he202c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he302c, value : 32'h33}, //phyinit_io_write: 0xe202c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'he202d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he302d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he402c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he502c, value : 32'h33}, //phyinit_io_write: 0xe402c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'he402d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he502d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he602c, value : 32'h33}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 TxImpedanceDq::TxStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he702c, value : 32'h33}, //phyinit_io_write: 0xe602c, 0x33
                          '{ step_type : REG_WRITE, reg_addr : 32'he602d, value : 32'h303}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 TxImpedanceDqs::TxStrenCodeDqsPDC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he702d, value : 32'h3333}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 WCK TxImpedanceDqs::TxStrenCodeDqsPDT/C to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC0 Instance0 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC1 Instance1 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h2070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC2 Instance2 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h3070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC3 Instance3 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h4070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming AC0 HMAC4 Instance4 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'h5070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC5 Instance5 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h7070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC0 Instance7 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h8070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC1 Instance8 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h9070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC2 Instance9 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'ha070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC3 Instance10 SE TxImpedanceAC::TxStrenCodePDAC to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'hb070, value : 32'hff}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming AC1 HMAC4 Instance11 CS TxImpedanceAC::TxStrenCodePDAC to 0xff
                          '{ step_type : REG_WRITE, reg_addr : 32'hc070, value : 32'h77}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC5 Instance12 TxImpedanceAC::TxStrenCodePD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'he002e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he102e, value : 32'h30}, //phyinit_io_write: 0xe002e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'he002f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he102f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'he202e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he302e, value : 32'h30}, //phyinit_io_write: 0xe202e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'he202f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he302f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'he402e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he502e, value : 32'h30}, //phyinit_io_write: 0xe402e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'he402f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he502f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'he602e, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 OdtImpedanceDq::OdtStrenCodeDqPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he702e, value : 32'h30}, //phyinit_io_write: 0xe602e, 0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'he602f, value : 32'h3300}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 OdtImpedanceDqs::OdtStrenCodeDqsPD to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he702f, value : 32'h7700}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 WCK OdtImpedanceDqs::OdtStrenCodeWckPD to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h79, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC0 Instance0 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h1079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC1 Instance1 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h2079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC2 Instance2 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h3079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC3 Instance3 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h4079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC4 Instance4 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h5079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC5 DIFF5 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h7079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC0 Instance7 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h8079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC1 Instance8 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h9079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC2 Instance9 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'ha079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC3 Instance10 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'hb079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC4 Instance11 SE OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'hc079, value : 32'h30}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC5 DIFF12 OdtImpedanceAC::OdtStrenCodePDAC to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he001c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 0 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he101c, value : 32'h3}, //phyinit_io_write: 0xe001c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he201c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 1 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he301c, value : 32'h3}, //phyinit_io_write: 0xe201c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he401c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 2 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he501c, value : 32'h3}, //phyinit_io_write: 0xe401c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'he601c, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming HMDBYTE 3 TxDQSlew::TxDQSlewPD to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he701c, value : 32'h3}, //phyinit_io_write: 0xe601c, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h6d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC0 Instance0 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h106d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC1 Instance1 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h206d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC2 Instance2 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h306d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC3 Instance3 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h406d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC4 Instance4 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h506d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX0 HMAC5 Instance5 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h706d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC0 Instance7 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h806d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC1 Instance8 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h906d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC2 Instance9 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'ha06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC3 Instance10 SE TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb06d, value : 32'hf8}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC4 Instance11 CS TxSlewAC::TxSlewPDAC to 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'hc06d, value : 32'h3}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACX1 HMAC5 Instance12 TxSlewAC::TxSlewPDAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he003e, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming HMDBYTE RxDQSCtrl::RxDQSDiffSeVrefDACEn to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he103e, value : 32'h0}, //phyinit_io_write: 0xe003e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he203e, value : 32'h0}, //phyinit_io_write: 0xe103e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he303e, value : 32'h0}, //phyinit_io_write: 0xe203e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he403e, value : 32'h0}, //phyinit_io_write: 0xe303e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he503e, value : 32'h0}, //phyinit_io_write: 0xe403e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he603e, value : 32'h0}, //phyinit_io_write: 0xe503e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he703e, value : 32'h0}, //phyinit_io_write: 0xe603e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10001, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming WriteLinkEcc to 0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11001, value : 32'h0}, //phyinit_io_write: 0x10001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12001, value : 32'h0}, //phyinit_io_write: 0x11001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13001, value : 32'h0}, //phyinit_io_write: 0x12001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70040, value : 32'h5a}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming PPTTrainSetup::PhyMstrMaxReqToAck to 0x5
                          '{ step_type : REG_WRITE, reg_addr : 32'h70041, value : 32'hf}, //phyinit_io_write: 0x70040, 0x5a
                          '{ step_type : REG_WRITE, reg_addr : 32'h100a5, value : 32'h1}, //phyinit_io_write: 0x70041, 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h110a5, value : 32'h1}, //phyinit_io_write: 0x100a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h120a5, value : 32'h1}, //phyinit_io_write: 0x110a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h130a5, value : 32'h1}, //phyinit_io_write: 0x120a5, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h10209, value : 32'h3232}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming RxReplicaRangeVal 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h11209, value : 32'h3232}, //phyinit_io_write: 0x10209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h12209, value : 32'h3232}, //phyinit_io_write: 0x11209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h13209, value : 32'h3232}, //phyinit_io_write: 0x12209, 0x3232
                          '{ step_type : REG_WRITE, reg_addr : 32'h1020f, value : 32'h6}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming RxReplicaCtl04 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h1120f, value : 32'h6}, //phyinit_io_write: 0x1020f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h1220f, value : 32'h6}, //phyinit_io_write: 0x1120f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h1320f, value : 32'h6}, //phyinit_io_write: 0x1220f, 0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h20005, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, DfiFreq=800MHz, Programming PipeCtl[AcInPipeEn]=0x0 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h10008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, DfiFreq=800MHz, Programming DBYTE0.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h11008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, DfiFreq=800MHz, Programming DBYTE1.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h12008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, DfiFreq=800MHz, Programming DBYTE2.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h13008, value : 32'h1}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, DfiFreq=800MHz, Programming DBYTE3.LP5DfiDataEnLatency[LP5RLm13]=0x1 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h7006b, value : 32'h222}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, DfiFreq=800MHz, Programming DfiHandshakeDelays[PhyUpdReqDelay]=0x2 DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h70066, value : 32'h20}, //phyinit_io_write: 0x7006b, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h700eb, value : 32'h222}, //phyinit_io_write: 0x70066, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h700e6, value : 32'h20}, //phyinit_io_write: 0x700eb, 0x222
                          '{ step_type : REG_WRITE, reg_addr : 32'h70135, value : 32'h100c}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleWidth to 0x19, ACSMWckWriteFastTogglePulse::ACSMWckWriteFastToggleDelay to 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h70136, value : 32'h100c}, //phyinit_io_write: 0x70135, 0x100c
                          '{ step_type : REG_WRITE, reg_addr : 32'h70137, value : 32'h41c}, //phyinit_io_write: 0x70136, 0x100c
                          '{ step_type : REG_WRITE, reg_addr : 32'h70138, value : 32'h1920}, //phyinit_io_write: 0x70137, 0x41c
                          '{ step_type : REG_WRITE, reg_addr : 32'h70139, value : 32'h1018}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleWidth to 0x2d, ACSMWckReadFastTogglePulse::ACSMWckReadFastToggleDelay to 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h7013a, value : 32'h1018}, //phyinit_io_write: 0x70139, 0x1018
                          '{ step_type : REG_WRITE, reg_addr : 32'h7013b, value : 32'h428}, //phyinit_io_write: 0x7013a, 0x1018
                          '{ step_type : REG_WRITE, reg_addr : 32'h7013c, value : 32'h2d2c}, //phyinit_io_write: 0x7013b, 0x428
                          '{ step_type : REG_WRITE, reg_addr : 32'h7013d, value : 32'h1004}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleWidth to 0x11, ACSMWckFreqFastTogglePulse::ACSMWckFreqFastToggleDelay to 0x18
                          '{ step_type : REG_WRITE, reg_addr : 32'h7013e, value : 32'h1004}, //phyinit_io_write: 0x7013d, 0x1004
                          '{ step_type : REG_WRITE, reg_addr : 32'h7013f, value : 32'h414}, //phyinit_io_write: 0x7013e, 0x1004
                          '{ step_type : REG_WRITE, reg_addr : 32'h70140, value : 32'h1118}, //phyinit_io_write: 0x7013f, 0x414
                          '{ step_type : REG_WRITE, reg_addr : 32'h7012c, value : 32'h837}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMRxValPulse::ACSMRxValDelay to 0x37, ACSMRxValPulse::ACSMRxValWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h7012d, value : 32'h837}, //phyinit_io_write: 0x7012c, 0x837
                          '{ step_type : REG_WRITE, reg_addr : 32'h70130, value : 32'h837}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMRdcsPulse::ACSMRdcsDelay to 0x37, ACSMRdcsPulse::ACSMRdcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h7012e, value : 32'h81f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMTxEnPulse::ACSMTxEnDelay to 0x1f, ACSMTxEnPulse::ACSMTxEnWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h7012f, value : 32'h81f}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming ACSMWrcsPulse::ACSMWrcsDelay to 0x1f, ACSMWrcsPulse::ACSMWrcsWidth to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h30008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming AcPipeEn AC0 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h31008, value : 32'h0}, //[dwc_ddrphy_phyinit_ACSM_delay] [phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, Programming AcPipeEn AC1 to 0. DFI ratio is 2
                          '{ step_type : REG_WRITE, reg_addr : 32'he0013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he1013, value : 32'h0}, //phyinit_io_write: 0xe0013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he2013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he3013, value : 32'h0}, //phyinit_io_write: 0xe2013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he4013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he5013, value : 32'h0}, //phyinit_io_write: 0xe4013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he6013, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming csr_EnaRxStrobeEnB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he7013, value : 32'h0}, //phyinit_io_write: 0xe6013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC0 Instance0 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h15e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC1 Instance1 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h25e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC2 Instance2 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h35e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC3 Instance3 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h45e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC4 Instance4 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h55e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC5 Instance5 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h75e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC0 Instance7 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h85e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC1 Instance8 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h95e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC2 Instance9 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'ha5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC3 Instance10 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'hb5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC4 Instance11 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'hc5e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC5 Instance12 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he05e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE0 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he15e3, value : 32'h4}, //phyinit_io_write: 0xe05e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he25e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE1 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he35e3, value : 32'h4}, //phyinit_io_write: 0xe25e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he45e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE2 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he55e3, value : 32'h4}, //phyinit_io_write: 0xe45e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he65e3, value : 32'h4}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE3 PclkDCALcdlAddDlySampEn to 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'he75e3, value : 32'h4}, //phyinit_io_write: 0xe65e3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC0 Instance0 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h150a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC1 Instance1 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h250a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC2 Instance2 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h350a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC3 Instance3 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h450a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC4 Instance4 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h550a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX0 HMAC5 Instance5 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h750a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC0 Instance7 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h850a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC1 Instance8 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h950a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC2 Instance9 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'ha50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC3 Instance10 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC4 Instance11 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc50a, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming ACX1 HMAC5 Instance12 PclkDCASampDelayLCDLAC to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1080b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE0 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1180b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE1 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1280b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE2 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1380b, value : 32'h0}, //[dwc_ddrphy_phyinit_programPclkDca] Programming DBYTE3 PclkDCASampDelayLCDLDB to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30803, value : 32'h106a}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming PclkDCAStaticCtr0AC to 0x106a
                          '{ step_type : REG_WRITE, reg_addr : 32'h31803, value : 32'h106a}, //phyinit_io_write: 0x30803, 0x106a
                          '{ step_type : REG_WRITE, reg_addr : 32'h10803, value : 32'h106a}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming PclkDCAStaticCtr0DB to 0x106a
                          '{ step_type : REG_WRITE, reg_addr : 32'h11803, value : 32'h106a}, //phyinit_io_write: 0x10803, 0x106a
                          '{ step_type : REG_WRITE, reg_addr : 32'h12803, value : 32'h106a}, //phyinit_io_write: 0x11803, 0x106a
                          '{ step_type : REG_WRITE, reg_addr : 32'h13803, value : 32'h106a}, //phyinit_io_write: 0x12803, 0x106a
                          '{ step_type : REG_WRITE, reg_addr : 32'h503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC0 Instance0 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC1 Instance1 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h2503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC2 Instance2 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h3503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC3 Instance3 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h4503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC4 Instance4 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h5503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC5 Instance5 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h7503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC0 Instance7 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h8503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC1 Instance8 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h9503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC2 Instance9 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'ha503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC3 Instance10 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'hb503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC4 Instance11 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'hc503, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC5 Instance12 PclkDCAStaticCtrl1AC to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h10c03, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming PclkDCAStaticCtrl1DB to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h11c03, value : 32'h1f}, //phyinit_io_write: 0x10c03, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h12c03, value : 32'h1f}, //phyinit_io_write: 0x11c03, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h13c03, value : 32'h1f}, //phyinit_io_write: 0x12c03, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC0 Instance0 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h1110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC1 Instance1 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h2110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC2 Instance2 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h3110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC3 Instance3 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC4 Instance4 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h5110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX0 HMAC5 Instance5 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h7110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC0 Instance7 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h8110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC1 Instance8 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h9110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC2 Instance9 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'ha110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC3 Instance10 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'hb110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC4 Instance11 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'hc110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming ACX1 HMAC5 Instance12 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he0110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE0 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he1110, value : 32'h1f}, //phyinit_io_write: 0xe0110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he2110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE1 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he3110, value : 32'h1f}, //phyinit_io_write: 0xe2110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he4110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE2 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he5110, value : 32'h1f}, //phyinit_io_write: 0xe4110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he6110, value : 32'h1f}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming HMDBYTE3 PclkDCATxLcdlPhase to 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'he7110, value : 32'h1f}, //phyinit_io_write: 0xe6110, 0x1f
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e8, value : 32'h13}, //[dwc_ddrphy_phyinit_programPclkDca] Pstate=0, Programming Seq0BDLY9 to 64
                          '{ step_type : REG_WRITE, reg_addr : 32'h908e9, value : 32'h40}, //phyinit_io_write: 0x908e8, 0x13
                          '{ step_type : REG_WRITE, reg_addr : 32'he0002, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Programming HMDBYTE RxDFECtrlDq to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he1002, value : 32'h0}, //phyinit_io_write: 0xe0002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he2002, value : 32'h0}, //phyinit_io_write: 0xe1002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he3002, value : 32'h0}, //phyinit_io_write: 0xe2002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he4002, value : 32'h0}, //phyinit_io_write: 0xe3002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he5002, value : 32'h0}, //phyinit_io_write: 0xe4002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he6002, value : 32'h0}, //phyinit_io_write: 0xe5002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'he7002, value : 32'h0}, //phyinit_io_write: 0xe6002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1010b, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Pstate=0, Memclk=800MHz, freqThreshold=200MHz, NoRDQS=0 Programming InhibitTxRdPtrInit::DisableRxEnDlyLoad to 0x0, InhibitTxRdPtrInit::DisableTxDqDly to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1110b, value : 32'h0}, //phyinit_io_write: 0x1010b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1210b, value : 32'h0}, //phyinit_io_write: 0x1110b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1310b, value : 32'h0}, //phyinit_io_write: 0x1210b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h63, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h1063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h2063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h3063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h4063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h5063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h7063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h8063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h9063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'ha063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'hb063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'hc063, value : 32'h68}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0x68 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080a, value : 32'h268}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR10 to HMTxLcdlSeed Full search value = 0x268
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080b, value : 32'h68}, //phyinit_io_write: 0x9080a, 0x268
                          '{ step_type : REG_WRITE, reg_addr : 32'h90815, value : 32'h268}, //[dwc_ddrphy_phyinit_programLCDLSeed] Programming Seq0BGPR21 to ACHMTxLcdlSeed Full search value = 0x268
                          '{ step_type : REG_WRITE, reg_addr : 32'h90816, value : 32'h68}, //phyinit_io_write: 0x90815, 0x268
                          '{ step_type : REG_WRITE, reg_addr : 32'he0063, value : 32'h68}, //phyinit_io_write: 0x90816, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he0064, value : 32'h68}, //phyinit_io_write: 0xe0063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he0087, value : 32'h68}, //phyinit_io_write: 0xe0064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he1063, value : 32'h68}, //phyinit_io_write: 0xe0087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he1064, value : 32'h68}, //phyinit_io_write: 0xe1063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he1087, value : 32'h68}, //phyinit_io_write: 0xe1064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he2063, value : 32'h68}, //phyinit_io_write: 0xe1087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he2064, value : 32'h68}, //phyinit_io_write: 0xe2063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he2087, value : 32'h68}, //phyinit_io_write: 0xe2064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he3063, value : 32'h68}, //phyinit_io_write: 0xe2087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he3064, value : 32'h68}, //phyinit_io_write: 0xe3063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he3087, value : 32'h68}, //phyinit_io_write: 0xe3064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he4063, value : 32'h68}, //phyinit_io_write: 0xe3087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he4064, value : 32'h68}, //phyinit_io_write: 0xe4063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he4087, value : 32'h68}, //phyinit_io_write: 0xe4064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he5063, value : 32'h68}, //phyinit_io_write: 0xe4087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he5064, value : 32'h68}, //phyinit_io_write: 0xe5063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he5087, value : 32'h68}, //phyinit_io_write: 0xe5064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he6063, value : 32'h68}, //phyinit_io_write: 0xe5087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he6064, value : 32'h68}, //phyinit_io_write: 0xe6063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he6087, value : 32'h68}, //phyinit_io_write: 0xe6064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he7063, value : 32'h68}, //phyinit_io_write: 0xe6087, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he7064, value : 32'h68}, //phyinit_io_write: 0xe7063, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'he7087, value : 32'h68}, //phyinit_io_write: 0xe7064, 0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'hc0080, value : 32'h7}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming UcclkHclkEnables to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'he003c, value : 32'h80}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming RxDQSSeVrefDAC0 to 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he103c, value : 32'h80}, //phyinit_io_write: 0xe003c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he203c, value : 32'h80}, //phyinit_io_write: 0xe103c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he303c, value : 32'h80}, //phyinit_io_write: 0xe203c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he403c, value : 32'h80}, //phyinit_io_write: 0xe303c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he503c, value : 32'h80}, //phyinit_io_write: 0xe403c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he603c, value : 32'h80}, //phyinit_io_write: 0xe503c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'he703c, value : 32'h80}, //phyinit_io_write: 0xe603c, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h90817, value : 32'h53}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 0 Seq0BGPR23 to 0x53, NumMemClk_tRFCab=328.0, NumMemClk_7p5ns=6.0, NumMemClk_tXSR=334.0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90818, value : 32'h0}, //phyinit_io_write: 0x90817, 0x53
                          '{ step_type : REG_WRITE, reg_addr : 32'h90819, value : 32'h0}, //phyinit_io_write: 0x90818, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h300eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 0 AC0 AcLcdlUpdInterval to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h310eb, value : 32'h0}, //[dwc_ddrphy_phyinit_C_initPhyConfigPsLoop] Programming PState 0 AC1 AcLcdlUpdInterval to 0x0
//[dwc_ddrphy_phyinit_programDfiMode] Skip DfiMode Programming: Keeping the reset value of 0x3
//End of dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(), Pstate=0
                          '{ step_type : REG_WRITE, reg_addr : 32'h300d9, value : 32'h40}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming CKXTxDly to 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h300d8, value : 32'h40}, //phyinit_io_write: 0x300d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h301d8, value : 32'h40}, //phyinit_io_write: 0x300d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h302d8, value : 32'h40}, //phyinit_io_write: 0x301d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h303d8, value : 32'h40}, //phyinit_io_write: 0x302d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h304d8, value : 32'h40}, //phyinit_io_write: 0x303d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h305d8, value : 32'h40}, //phyinit_io_write: 0x304d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h306d8, value : 32'h40}, //phyinit_io_write: 0x305d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h308d8, value : 32'h40}, //phyinit_io_write: 0x306d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h309d8, value : 32'h40}, //phyinit_io_write: 0x308d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h310d9, value : 32'h40}, //phyinit_io_write: 0x309d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h310d8, value : 32'h40}, //phyinit_io_write: 0x310d9, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h311d8, value : 32'h40}, //phyinit_io_write: 0x310d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h312d8, value : 32'h40}, //phyinit_io_write: 0x311d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h313d8, value : 32'h40}, //phyinit_io_write: 0x312d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h314d8, value : 32'h40}, //phyinit_io_write: 0x313d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h315d8, value : 32'h40}, //phyinit_io_write: 0x314d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h316d8, value : 32'h40}, //phyinit_io_write: 0x315d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h318d8, value : 32'h40}, //phyinit_io_write: 0x316d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h319d8, value : 32'h40}, //phyinit_io_write: 0x318d8, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h10000, value : 32'h7}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming HwtMRL to 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h11000, value : 32'h7}, //phyinit_io_write: 0x10000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h12000, value : 32'h7}, //phyinit_io_write: 0x11000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h13000, value : 32'h7}, //phyinit_io_write: 0x12000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h7000d, value : 32'h7}, //phyinit_io_write: 0x13000, 0x7
                          '{ step_type : REG_WRITE, reg_addr : 32'h1002a, value : 32'h200}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming TxWckDlyTg0/Tg1 to 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1002b, value : 32'h200}, //phyinit_io_write: 0x1002a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102a, value : 32'h200}, //phyinit_io_write: 0x1002b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1102b, value : 32'h200}, //phyinit_io_write: 0x1102a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1202a, value : 32'h200}, //phyinit_io_write: 0x1102b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1202b, value : 32'h200}, //phyinit_io_write: 0x1202a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1302a, value : 32'h200}, //phyinit_io_write: 0x1202b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h1302b, value : 32'h200}, //phyinit_io_write: 0x1302a, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h10028, value : 32'hed}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming TxDqsDlyTg0/Tg1 to 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h10029, value : 32'hed}, //phyinit_io_write: 0x10028, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h11028, value : 32'hed}, //phyinit_io_write: 0x10029, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h11029, value : 32'hed}, //phyinit_io_write: 0x11028, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h12028, value : 32'hed}, //phyinit_io_write: 0x11029, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h12029, value : 32'hed}, //phyinit_io_write: 0x12028, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h13028, value : 32'hed}, //phyinit_io_write: 0x12029, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h13029, value : 32'hed}, //phyinit_io_write: 0x13028, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1007a, value : 32'hed}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming TxDqDlyTg0/Tg1 to 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1007b, value : 32'hed}, //phyinit_io_write: 0x1007a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1017a, value : 32'hed}, //phyinit_io_write: 0x1007b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1017b, value : 32'hed}, //phyinit_io_write: 0x1017a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1027a, value : 32'hed}, //phyinit_io_write: 0x1017b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1027b, value : 32'hed}, //phyinit_io_write: 0x1027a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1037a, value : 32'hed}, //phyinit_io_write: 0x1027b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1037b, value : 32'hed}, //phyinit_io_write: 0x1037a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1047a, value : 32'hed}, //phyinit_io_write: 0x1037b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1047b, value : 32'hed}, //phyinit_io_write: 0x1047a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1057a, value : 32'hed}, //phyinit_io_write: 0x1047b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1057b, value : 32'hed}, //phyinit_io_write: 0x1057a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1067a, value : 32'hed}, //phyinit_io_write: 0x1057b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1067b, value : 32'hed}, //phyinit_io_write: 0x1067a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1077a, value : 32'hed}, //phyinit_io_write: 0x1067b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1077b, value : 32'hed}, //phyinit_io_write: 0x1077a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1087a, value : 32'hed}, //phyinit_io_write: 0x1077b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1087b, value : 32'hed}, //phyinit_io_write: 0x1087a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1107a, value : 32'hed}, //phyinit_io_write: 0x1087b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1107b, value : 32'hed}, //phyinit_io_write: 0x1107a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1117a, value : 32'hed}, //phyinit_io_write: 0x1107b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1117b, value : 32'hed}, //phyinit_io_write: 0x1117a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1127a, value : 32'hed}, //phyinit_io_write: 0x1117b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1127b, value : 32'hed}, //phyinit_io_write: 0x1127a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1137a, value : 32'hed}, //phyinit_io_write: 0x1127b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1137b, value : 32'hed}, //phyinit_io_write: 0x1137a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1147a, value : 32'hed}, //phyinit_io_write: 0x1137b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1147b, value : 32'hed}, //phyinit_io_write: 0x1147a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1157a, value : 32'hed}, //phyinit_io_write: 0x1147b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1157b, value : 32'hed}, //phyinit_io_write: 0x1157a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1167a, value : 32'hed}, //phyinit_io_write: 0x1157b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1167b, value : 32'hed}, //phyinit_io_write: 0x1167a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1177a, value : 32'hed}, //phyinit_io_write: 0x1167b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1177b, value : 32'hed}, //phyinit_io_write: 0x1177a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1187a, value : 32'hed}, //phyinit_io_write: 0x1177b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1187b, value : 32'hed}, //phyinit_io_write: 0x1187a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1207a, value : 32'hed}, //phyinit_io_write: 0x1187b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1207b, value : 32'hed}, //phyinit_io_write: 0x1207a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1217a, value : 32'hed}, //phyinit_io_write: 0x1207b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1217b, value : 32'hed}, //phyinit_io_write: 0x1217a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1227a, value : 32'hed}, //phyinit_io_write: 0x1217b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1227b, value : 32'hed}, //phyinit_io_write: 0x1227a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1237a, value : 32'hed}, //phyinit_io_write: 0x1227b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1237b, value : 32'hed}, //phyinit_io_write: 0x1237a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1247a, value : 32'hed}, //phyinit_io_write: 0x1237b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1247b, value : 32'hed}, //phyinit_io_write: 0x1247a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1257a, value : 32'hed}, //phyinit_io_write: 0x1247b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1257b, value : 32'hed}, //phyinit_io_write: 0x1257a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1267a, value : 32'hed}, //phyinit_io_write: 0x1257b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1267b, value : 32'hed}, //phyinit_io_write: 0x1267a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1277a, value : 32'hed}, //phyinit_io_write: 0x1267b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1277b, value : 32'hed}, //phyinit_io_write: 0x1277a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1287a, value : 32'hed}, //phyinit_io_write: 0x1277b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1287b, value : 32'hed}, //phyinit_io_write: 0x1287a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1307a, value : 32'hed}, //phyinit_io_write: 0x1287b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1307b, value : 32'hed}, //phyinit_io_write: 0x1307a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1317a, value : 32'hed}, //phyinit_io_write: 0x1307b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1317b, value : 32'hed}, //phyinit_io_write: 0x1317a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1327a, value : 32'hed}, //phyinit_io_write: 0x1317b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1327b, value : 32'hed}, //phyinit_io_write: 0x1327a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1337a, value : 32'hed}, //phyinit_io_write: 0x1327b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1337b, value : 32'hed}, //phyinit_io_write: 0x1337a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1347a, value : 32'hed}, //phyinit_io_write: 0x1337b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1347b, value : 32'hed}, //phyinit_io_write: 0x1347a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1357a, value : 32'hed}, //phyinit_io_write: 0x1347b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1357b, value : 32'hed}, //phyinit_io_write: 0x1357a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1367a, value : 32'hed}, //phyinit_io_write: 0x1357b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1367b, value : 32'hed}, //phyinit_io_write: 0x1367a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1377a, value : 32'hed}, //phyinit_io_write: 0x1367b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1377b, value : 32'hed}, //phyinit_io_write: 0x1377a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1387a, value : 32'hed}, //phyinit_io_write: 0x1377b, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h1387b, value : 32'hed}, //phyinit_io_write: 0x1387a, 0xed
                          '{ step_type : REG_WRITE, reg_addr : 32'h10078, value : 32'h3b9}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming RxDigStrbDlyTg0/Tg1 to 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10079, value : 32'h3b9}, //phyinit_io_write: 0x10078, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10178, value : 32'h3b9}, //phyinit_io_write: 0x10079, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10179, value : 32'h3b9}, //phyinit_io_write: 0x10178, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10278, value : 32'h3b9}, //phyinit_io_write: 0x10179, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10279, value : 32'h3b9}, //phyinit_io_write: 0x10278, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10378, value : 32'h3b9}, //phyinit_io_write: 0x10279, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10379, value : 32'h3b9}, //phyinit_io_write: 0x10378, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10478, value : 32'h3b9}, //phyinit_io_write: 0x10379, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10479, value : 32'h3b9}, //phyinit_io_write: 0x10478, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10578, value : 32'h3b9}, //phyinit_io_write: 0x10479, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10579, value : 32'h3b9}, //phyinit_io_write: 0x10578, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10678, value : 32'h3b9}, //phyinit_io_write: 0x10579, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10679, value : 32'h3b9}, //phyinit_io_write: 0x10678, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10778, value : 32'h3b9}, //phyinit_io_write: 0x10679, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10779, value : 32'h3b9}, //phyinit_io_write: 0x10778, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10878, value : 32'h3b9}, //phyinit_io_write: 0x10779, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10879, value : 32'h3b9}, //phyinit_io_write: 0x10878, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11078, value : 32'h3b9}, //phyinit_io_write: 0x10879, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11079, value : 32'h3b9}, //phyinit_io_write: 0x11078, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11178, value : 32'h3b9}, //phyinit_io_write: 0x11079, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11179, value : 32'h3b9}, //phyinit_io_write: 0x11178, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11278, value : 32'h3b9}, //phyinit_io_write: 0x11179, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11279, value : 32'h3b9}, //phyinit_io_write: 0x11278, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11378, value : 32'h3b9}, //phyinit_io_write: 0x11279, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11379, value : 32'h3b9}, //phyinit_io_write: 0x11378, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11478, value : 32'h3b9}, //phyinit_io_write: 0x11379, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11479, value : 32'h3b9}, //phyinit_io_write: 0x11478, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11578, value : 32'h3b9}, //phyinit_io_write: 0x11479, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11579, value : 32'h3b9}, //phyinit_io_write: 0x11578, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11678, value : 32'h3b9}, //phyinit_io_write: 0x11579, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11679, value : 32'h3b9}, //phyinit_io_write: 0x11678, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11778, value : 32'h3b9}, //phyinit_io_write: 0x11679, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11779, value : 32'h3b9}, //phyinit_io_write: 0x11778, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11878, value : 32'h3b9}, //phyinit_io_write: 0x11779, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h11879, value : 32'h3b9}, //phyinit_io_write: 0x11878, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12078, value : 32'h3b9}, //phyinit_io_write: 0x11879, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12079, value : 32'h3b9}, //phyinit_io_write: 0x12078, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12178, value : 32'h3b9}, //phyinit_io_write: 0x12079, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12179, value : 32'h3b9}, //phyinit_io_write: 0x12178, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12278, value : 32'h3b9}, //phyinit_io_write: 0x12179, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12279, value : 32'h3b9}, //phyinit_io_write: 0x12278, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12378, value : 32'h3b9}, //phyinit_io_write: 0x12279, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12379, value : 32'h3b9}, //phyinit_io_write: 0x12378, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12478, value : 32'h3b9}, //phyinit_io_write: 0x12379, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12479, value : 32'h3b9}, //phyinit_io_write: 0x12478, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12578, value : 32'h3b9}, //phyinit_io_write: 0x12479, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12579, value : 32'h3b9}, //phyinit_io_write: 0x12578, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12678, value : 32'h3b9}, //phyinit_io_write: 0x12579, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12679, value : 32'h3b9}, //phyinit_io_write: 0x12678, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12778, value : 32'h3b9}, //phyinit_io_write: 0x12679, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12779, value : 32'h3b9}, //phyinit_io_write: 0x12778, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12878, value : 32'h3b9}, //phyinit_io_write: 0x12779, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h12879, value : 32'h3b9}, //phyinit_io_write: 0x12878, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13078, value : 32'h3b9}, //phyinit_io_write: 0x12879, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13079, value : 32'h3b9}, //phyinit_io_write: 0x13078, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13178, value : 32'h3b9}, //phyinit_io_write: 0x13079, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13179, value : 32'h3b9}, //phyinit_io_write: 0x13178, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13278, value : 32'h3b9}, //phyinit_io_write: 0x13179, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13279, value : 32'h3b9}, //phyinit_io_write: 0x13278, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13378, value : 32'h3b9}, //phyinit_io_write: 0x13279, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13379, value : 32'h3b9}, //phyinit_io_write: 0x13378, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13478, value : 32'h3b9}, //phyinit_io_write: 0x13379, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13479, value : 32'h3b9}, //phyinit_io_write: 0x13478, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13578, value : 32'h3b9}, //phyinit_io_write: 0x13479, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13579, value : 32'h3b9}, //phyinit_io_write: 0x13578, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13678, value : 32'h3b9}, //phyinit_io_write: 0x13579, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13679, value : 32'h3b9}, //phyinit_io_write: 0x13678, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13778, value : 32'h3b9}, //phyinit_io_write: 0x13679, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13779, value : 32'h3b9}, //phyinit_io_write: 0x13778, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13878, value : 32'h3b9}, //phyinit_io_write: 0x13779, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h13879, value : 32'h3b9}, //phyinit_io_write: 0x13878, 0x3b9
                          '{ step_type : REG_WRITE, reg_addr : 32'h10020, value : 32'h319}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming RxEnDlyTg0/Tg1 to 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h10021, value : 32'h319}, //phyinit_io_write: 0x10020, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h11020, value : 32'h319}, //phyinit_io_write: 0x10021, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h11021, value : 32'h319}, //phyinit_io_write: 0x11020, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h12020, value : 32'h319}, //phyinit_io_write: 0x11021, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h12021, value : 32'h319}, //phyinit_io_write: 0x12020, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h13020, value : 32'h319}, //phyinit_io_write: 0x12021, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h13021, value : 32'h319}, //phyinit_io_write: 0x13020, 0x319
                          '{ step_type : REG_WRITE, reg_addr : 32'h10010, value : 32'h12b}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming RxClkT2UIDlyTg0/Tg1 and RxClkC2UIDlyTg0/Tg1 to 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10011, value : 32'h12b}, //phyinit_io_write: 0x10010, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10012, value : 32'h12b}, //phyinit_io_write: 0x10011, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10013, value : 32'h12b}, //phyinit_io_write: 0x10012, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10110, value : 32'h12b}, //phyinit_io_write: 0x10013, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10111, value : 32'h12b}, //phyinit_io_write: 0x10110, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10112, value : 32'h12b}, //phyinit_io_write: 0x10111, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10113, value : 32'h12b}, //phyinit_io_write: 0x10112, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10210, value : 32'h12b}, //phyinit_io_write: 0x10113, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10211, value : 32'h12b}, //phyinit_io_write: 0x10210, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10212, value : 32'h12b}, //phyinit_io_write: 0x10211, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10213, value : 32'h12b}, //phyinit_io_write: 0x10212, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10310, value : 32'h12b}, //phyinit_io_write: 0x10213, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10311, value : 32'h12b}, //phyinit_io_write: 0x10310, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10312, value : 32'h12b}, //phyinit_io_write: 0x10311, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10313, value : 32'h12b}, //phyinit_io_write: 0x10312, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10410, value : 32'h12b}, //phyinit_io_write: 0x10313, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10411, value : 32'h12b}, //phyinit_io_write: 0x10410, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10412, value : 32'h12b}, //phyinit_io_write: 0x10411, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10413, value : 32'h12b}, //phyinit_io_write: 0x10412, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10510, value : 32'h12b}, //phyinit_io_write: 0x10413, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10511, value : 32'h12b}, //phyinit_io_write: 0x10510, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10512, value : 32'h12b}, //phyinit_io_write: 0x10511, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10513, value : 32'h12b}, //phyinit_io_write: 0x10512, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10610, value : 32'h12b}, //phyinit_io_write: 0x10513, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10611, value : 32'h12b}, //phyinit_io_write: 0x10610, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10612, value : 32'h12b}, //phyinit_io_write: 0x10611, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10613, value : 32'h12b}, //phyinit_io_write: 0x10612, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10710, value : 32'h12b}, //phyinit_io_write: 0x10613, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10711, value : 32'h12b}, //phyinit_io_write: 0x10710, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10712, value : 32'h12b}, //phyinit_io_write: 0x10711, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10713, value : 32'h12b}, //phyinit_io_write: 0x10712, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10810, value : 32'h12b}, //phyinit_io_write: 0x10713, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10811, value : 32'h12b}, //phyinit_io_write: 0x10810, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10812, value : 32'h12b}, //phyinit_io_write: 0x10811, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h10813, value : 32'h12b}, //phyinit_io_write: 0x10812, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11010, value : 32'h12b}, //phyinit_io_write: 0x10813, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11011, value : 32'h12b}, //phyinit_io_write: 0x11010, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11012, value : 32'h12b}, //phyinit_io_write: 0x11011, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11013, value : 32'h12b}, //phyinit_io_write: 0x11012, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11110, value : 32'h12b}, //phyinit_io_write: 0x11013, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11111, value : 32'h12b}, //phyinit_io_write: 0x11110, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11112, value : 32'h12b}, //phyinit_io_write: 0x11111, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11113, value : 32'h12b}, //phyinit_io_write: 0x11112, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11210, value : 32'h12b}, //phyinit_io_write: 0x11113, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11211, value : 32'h12b}, //phyinit_io_write: 0x11210, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11212, value : 32'h12b}, //phyinit_io_write: 0x11211, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11213, value : 32'h12b}, //phyinit_io_write: 0x11212, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11310, value : 32'h12b}, //phyinit_io_write: 0x11213, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11311, value : 32'h12b}, //phyinit_io_write: 0x11310, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11312, value : 32'h12b}, //phyinit_io_write: 0x11311, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11313, value : 32'h12b}, //phyinit_io_write: 0x11312, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11410, value : 32'h12b}, //phyinit_io_write: 0x11313, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11411, value : 32'h12b}, //phyinit_io_write: 0x11410, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11412, value : 32'h12b}, //phyinit_io_write: 0x11411, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11413, value : 32'h12b}, //phyinit_io_write: 0x11412, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11510, value : 32'h12b}, //phyinit_io_write: 0x11413, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11511, value : 32'h12b}, //phyinit_io_write: 0x11510, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11512, value : 32'h12b}, //phyinit_io_write: 0x11511, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11513, value : 32'h12b}, //phyinit_io_write: 0x11512, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11610, value : 32'h12b}, //phyinit_io_write: 0x11513, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11611, value : 32'h12b}, //phyinit_io_write: 0x11610, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11612, value : 32'h12b}, //phyinit_io_write: 0x11611, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11613, value : 32'h12b}, //phyinit_io_write: 0x11612, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11710, value : 32'h12b}, //phyinit_io_write: 0x11613, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11711, value : 32'h12b}, //phyinit_io_write: 0x11710, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11712, value : 32'h12b}, //phyinit_io_write: 0x11711, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11713, value : 32'h12b}, //phyinit_io_write: 0x11712, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11810, value : 32'h12b}, //phyinit_io_write: 0x11713, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11811, value : 32'h12b}, //phyinit_io_write: 0x11810, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11812, value : 32'h12b}, //phyinit_io_write: 0x11811, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h11813, value : 32'h12b}, //phyinit_io_write: 0x11812, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12010, value : 32'h12b}, //phyinit_io_write: 0x11813, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12011, value : 32'h12b}, //phyinit_io_write: 0x12010, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12012, value : 32'h12b}, //phyinit_io_write: 0x12011, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12013, value : 32'h12b}, //phyinit_io_write: 0x12012, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12110, value : 32'h12b}, //phyinit_io_write: 0x12013, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12111, value : 32'h12b}, //phyinit_io_write: 0x12110, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12112, value : 32'h12b}, //phyinit_io_write: 0x12111, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12113, value : 32'h12b}, //phyinit_io_write: 0x12112, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12210, value : 32'h12b}, //phyinit_io_write: 0x12113, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12211, value : 32'h12b}, //phyinit_io_write: 0x12210, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12212, value : 32'h12b}, //phyinit_io_write: 0x12211, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12213, value : 32'h12b}, //phyinit_io_write: 0x12212, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12310, value : 32'h12b}, //phyinit_io_write: 0x12213, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12311, value : 32'h12b}, //phyinit_io_write: 0x12310, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12312, value : 32'h12b}, //phyinit_io_write: 0x12311, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12313, value : 32'h12b}, //phyinit_io_write: 0x12312, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12410, value : 32'h12b}, //phyinit_io_write: 0x12313, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12411, value : 32'h12b}, //phyinit_io_write: 0x12410, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12412, value : 32'h12b}, //phyinit_io_write: 0x12411, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12413, value : 32'h12b}, //phyinit_io_write: 0x12412, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12510, value : 32'h12b}, //phyinit_io_write: 0x12413, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12511, value : 32'h12b}, //phyinit_io_write: 0x12510, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12512, value : 32'h12b}, //phyinit_io_write: 0x12511, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12513, value : 32'h12b}, //phyinit_io_write: 0x12512, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12610, value : 32'h12b}, //phyinit_io_write: 0x12513, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12611, value : 32'h12b}, //phyinit_io_write: 0x12610, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12612, value : 32'h12b}, //phyinit_io_write: 0x12611, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12613, value : 32'h12b}, //phyinit_io_write: 0x12612, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12710, value : 32'h12b}, //phyinit_io_write: 0x12613, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12711, value : 32'h12b}, //phyinit_io_write: 0x12710, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12712, value : 32'h12b}, //phyinit_io_write: 0x12711, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12713, value : 32'h12b}, //phyinit_io_write: 0x12712, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12810, value : 32'h12b}, //phyinit_io_write: 0x12713, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12811, value : 32'h12b}, //phyinit_io_write: 0x12810, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12812, value : 32'h12b}, //phyinit_io_write: 0x12811, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h12813, value : 32'h12b}, //phyinit_io_write: 0x12812, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13010, value : 32'h12b}, //phyinit_io_write: 0x12813, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13011, value : 32'h12b}, //phyinit_io_write: 0x13010, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13012, value : 32'h12b}, //phyinit_io_write: 0x13011, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13013, value : 32'h12b}, //phyinit_io_write: 0x13012, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13110, value : 32'h12b}, //phyinit_io_write: 0x13013, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13111, value : 32'h12b}, //phyinit_io_write: 0x13110, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13112, value : 32'h12b}, //phyinit_io_write: 0x13111, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13113, value : 32'h12b}, //phyinit_io_write: 0x13112, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13210, value : 32'h12b}, //phyinit_io_write: 0x13113, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13211, value : 32'h12b}, //phyinit_io_write: 0x13210, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13212, value : 32'h12b}, //phyinit_io_write: 0x13211, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13213, value : 32'h12b}, //phyinit_io_write: 0x13212, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13310, value : 32'h12b}, //phyinit_io_write: 0x13213, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13311, value : 32'h12b}, //phyinit_io_write: 0x13310, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13312, value : 32'h12b}, //phyinit_io_write: 0x13311, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13313, value : 32'h12b}, //phyinit_io_write: 0x13312, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13410, value : 32'h12b}, //phyinit_io_write: 0x13313, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13411, value : 32'h12b}, //phyinit_io_write: 0x13410, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13412, value : 32'h12b}, //phyinit_io_write: 0x13411, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13413, value : 32'h12b}, //phyinit_io_write: 0x13412, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13510, value : 32'h12b}, //phyinit_io_write: 0x13413, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13511, value : 32'h12b}, //phyinit_io_write: 0x13510, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13512, value : 32'h12b}, //phyinit_io_write: 0x13511, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13513, value : 32'h12b}, //phyinit_io_write: 0x13512, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13610, value : 32'h12b}, //phyinit_io_write: 0x13513, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13611, value : 32'h12b}, //phyinit_io_write: 0x13610, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13612, value : 32'h12b}, //phyinit_io_write: 0x13611, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13613, value : 32'h12b}, //phyinit_io_write: 0x13612, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13710, value : 32'h12b}, //phyinit_io_write: 0x13613, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13711, value : 32'h12b}, //phyinit_io_write: 0x13710, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13712, value : 32'h12b}, //phyinit_io_write: 0x13711, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13713, value : 32'h12b}, //phyinit_io_write: 0x13712, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13810, value : 32'h12b}, //phyinit_io_write: 0x13713, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13811, value : 32'h12b}, //phyinit_io_write: 0x13810, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13812, value : 32'h12b}, //phyinit_io_write: 0x13811, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h13813, value : 32'h12b}, //phyinit_io_write: 0x13812, 0x12b
                          '{ step_type : REG_WRITE, reg_addr : 32'h1000c, value : 32'hcc}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming PptWck2DqoCntInvTrn1 to 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1000d, value : 32'hcc}, //phyinit_io_write: 0x1000c, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h10014, value : 32'h198}, //phyinit_io_write: 0x1000d, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h10015, value : 32'h198}, //phyinit_io_write: 0x10014, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1100c, value : 32'hcc}, //phyinit_io_write: 0x10015, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1100d, value : 32'hcc}, //phyinit_io_write: 0x1100c, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h11014, value : 32'h198}, //phyinit_io_write: 0x1100d, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h11015, value : 32'h198}, //phyinit_io_write: 0x11014, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1200c, value : 32'hcc}, //phyinit_io_write: 0x11015, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1200d, value : 32'hcc}, //phyinit_io_write: 0x1200c, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h12014, value : 32'h198}, //phyinit_io_write: 0x1200d, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h12015, value : 32'h198}, //phyinit_io_write: 0x12014, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1300c, value : 32'hcc}, //phyinit_io_write: 0x12015, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h1300d, value : 32'hcc}, //phyinit_io_write: 0x1300c, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h13014, value : 32'h198}, //phyinit_io_write: 0x1300d, 0xcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h13015, value : 32'h198}, //phyinit_io_write: 0x13014, 0x198
                          '{ step_type : REG_WRITE, reg_addr : 32'h70077, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming HwtCtrl to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h20071, value : 32'h66}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming HMRxReplicaLcdlSeed HMRxSeed to 0x62 HMRxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h63, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC0 Instance0 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h1063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC1 Instance1 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h2063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC2 Instance2 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h3063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC3 Instance3 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h4063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC4 Instance4 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h5063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX0 HMAC5 Instance5 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h7063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC0 Instance7 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h8063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC1 Instance8 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'h9063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC2 Instance9 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'ha063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC3 Instance10 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'hb063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC4 Instance11 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'hc063, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] LcdlSeed Pstate=0, Memclk=800MHz, Programming ACX1 HMAC5 Instance12 HMTxLcdlSeed HMTxSeed to 0x62 HMTxSeedIs1UI 0x0 
                          '{ step_type : REG_WRITE, reg_addr : 32'he0063, value : 32'h62}, //phyinit_io_write: 0xc063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he0064, value : 32'h62}, //phyinit_io_write: 0xe0063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he0087, value : 32'h62}, //phyinit_io_write: 0xe0064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he1063, value : 32'h62}, //phyinit_io_write: 0xe0087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he1064, value : 32'h62}, //phyinit_io_write: 0xe1063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he1087, value : 32'h62}, //phyinit_io_write: 0xe1064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he2063, value : 32'h62}, //phyinit_io_write: 0xe1087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he2064, value : 32'h62}, //phyinit_io_write: 0xe2063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he2087, value : 32'h62}, //phyinit_io_write: 0xe2064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he3063, value : 32'h62}, //phyinit_io_write: 0xe2087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he3064, value : 32'h62}, //phyinit_io_write: 0xe3063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he3087, value : 32'h62}, //phyinit_io_write: 0xe3064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he4063, value : 32'h62}, //phyinit_io_write: 0xe3087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he4064, value : 32'h62}, //phyinit_io_write: 0xe4063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he4087, value : 32'h62}, //phyinit_io_write: 0xe4064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he5063, value : 32'h62}, //phyinit_io_write: 0xe4087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he5064, value : 32'h62}, //phyinit_io_write: 0xe5063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he5087, value : 32'h62}, //phyinit_io_write: 0xe5064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he6063, value : 32'h62}, //phyinit_io_write: 0xe5087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he6064, value : 32'h62}, //phyinit_io_write: 0xe6063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he6087, value : 32'h62}, //phyinit_io_write: 0xe6064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he7063, value : 32'h62}, //phyinit_io_write: 0xe6087, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he7064, value : 32'h62}, //phyinit_io_write: 0xe7063, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'he7087, value : 32'h62}, //phyinit_io_write: 0xe7064, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080a, value : 32'h262}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=0 Programming Seq0bGPR10 to mission mode HMTxLcdlSeed value 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080b, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=0 Programming Seq0bGPR11 to mission mode HMTxLcdlSeed value 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h90815, value : 32'h262}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=0 Programming Seq0bGPR21 to mission mode HMTxLcdlSeed value 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h90816, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=0 Programming Seq0bGPR22 to mission mode HMTxLcdlSeed value 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h1015f, value : 32'h62}, //[dwc_ddrphy_phyinit_programLCDLSeed] Pstate=0, Memclk=800MHz, Programming RDqRDqsCntrl to 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h1115f, value : 32'h62}, //phyinit_io_write: 0x1015f, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h1215f, value : 32'h62}, //phyinit_io_write: 0x1115f, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h1315f, value : 32'h62}, //phyinit_io_write: 0x1215f, 0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h60009, value : 32'h10}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Memclk=800MHz, Programming CPllDacValIn to 0x10
                          '{ step_type : REG_WRITE, reg_addr : 32'h102a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h102a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h102a2, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaPathPhase2 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h102a3, value : 32'h3e}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaPathPhase3 to 0x3e
                          '{ step_type : REG_WRITE, reg_addr : 32'h102a4, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaPathPhase4 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h112a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h112a2, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaPathPhase2 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h112a3, value : 32'h3e}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaPathPhase3 to 0x3e
                          '{ step_type : REG_WRITE, reg_addr : 32'h112a4, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaPathPhase4 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h122a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h122a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h122a2, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaPathPhase2 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h122a3, value : 32'h3e}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaPathPhase3 to 0x3e
                          '{ step_type : REG_WRITE, reg_addr : 32'h122a4, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaPathPhase4 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h132a0, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaPathPhase0 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h132a1, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaPathPhase1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h132a2, value : 32'ha}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaPathPhase2 to 0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h132a3, value : 32'h3e}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaPathPhase3 to 0x3e
                          '{ step_type : REG_WRITE, reg_addr : 32'h132a4, value : 32'h72}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaPathPhase4 to 0x72
                          '{ step_type : REG_WRITE, reg_addr : 32'h102ad, value : 32'h3}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaCtl01::RxReplicaSelPathPhase to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h112ad, value : 32'h3}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaCtl01::RxReplicaSelPathPhase to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h122ad, value : 32'h3}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaCtl01::RxReplicaSelPathPhase to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h132ad, value : 32'h3}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaCtl01::RxReplicaSelPathPhase to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h102af, value : 32'h4c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE0.RxReplicaCtl03 to 0x4c
                          '{ step_type : REG_WRITE, reg_addr : 32'h112af, value : 32'h4c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE1.RxReplicaCtl03 to 0x4c
                          '{ step_type : REG_WRITE, reg_addr : 32'h122af, value : 32'h4c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE2.RxReplicaCtl03 to 0x4c
                          '{ step_type : REG_WRITE, reg_addr : 32'h132af, value : 32'h4c}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming DBYTE3.RxReplicaCtl03 to 0x4c
                          '{ step_type : REG_WRITE, reg_addr : 32'h90807, value : 32'h9701}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming Seq0BGPR7 to save ZQCalCodeOvrValPU=0x12e and ZQCalCodeOvrEnPU=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h90808, value : 32'hb681}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Pstate=0, Programming Seq0BGPR8 to save ZQCalCodeOvrValPD=0x16d and ZQCalCodeOvrEnPD=1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1003f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1103f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1203f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h1}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h1303f, value : 32'h0}, //[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] Programming TtcfControl[TtcfForceSendAll] to 0x0
//[dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop] End of dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(), PState=0
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Start of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb0310, value : 32'h1}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming ZCalRun to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'hb0311, value : 32'h1},
                          '{ step_type : REG_WRITE, reg_addr : 32'h60008, value : 32'h2d56}, //[dwc_ddrphy_phyinit_programPLL] [phyinit_I_loadPIEImagePsLoop] Pstate=0,  Memclk=800MHz, Programming CpllCtrl5 to 0x2d56.
                          '{ step_type : REG_WRITE, reg_addr : 32'h60006, value : 32'h3f0}, //End of dwc_ddrphy_phyinit_programPLL(), PState=0
                          '{ step_type : REG_WRITE, reg_addr : 32'h30015, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h31015, value : 32'h0}, //phyinit_io_write: 0x30015, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1007c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1107c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1207c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1307c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming SingleEndedMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70141, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming ACSMWckFreeRunMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hb0001, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming ZcalClkDiv to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080c, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming GPR12 with Zcalkclkdiv to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h10027, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming RxClkCntl1 to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h11027, value : 32'h0}, //phyinit_io_write: 0x10027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h12027, value : 32'h0}, //phyinit_io_write: 0x11027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h13027, value : 32'h0}, //phyinit_io_write: 0x12027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h1020f, value : 32'h8}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Pstate=0, Programming RxReplicaCtl04 to 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h1120f, value : 32'h8}, //phyinit_io_write: 0x1020f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h1220f, value : 32'h8}, //phyinit_io_write: 0x1120f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h1320f, value : 32'h8}, //phyinit_io_write: 0x1220f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'he003f, value : 32'h1}, //phyinit_io_write: 0x1320f, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'he008d, value : 32'h1}, //phyinit_io_write: 0xe003f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he103f, value : 32'h1}, //phyinit_io_write: 0xe008d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he108d, value : 32'h1}, //phyinit_io_write: 0xe103f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he203f, value : 32'h1}, //phyinit_io_write: 0xe108d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he208d, value : 32'h1}, //phyinit_io_write: 0xe203f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he303f, value : 32'h1}, //phyinit_io_write: 0xe208d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he308d, value : 32'h1}, //phyinit_io_write: 0xe303f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he403f, value : 32'h1}, //phyinit_io_write: 0xe308d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he408d, value : 32'h1}, //phyinit_io_write: 0xe403f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he503f, value : 32'h1}, //phyinit_io_write: 0xe408d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he508d, value : 32'h1}, //phyinit_io_write: 0xe503f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he603f, value : 32'h1}, //phyinit_io_write: 0xe508d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he608d, value : 32'h1}, //phyinit_io_write: 0xe603f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he703f, value : 32'h1}, //phyinit_io_write: 0xe608d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'he708d, value : 32'h1}, //phyinit_io_write: 0xe703f, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h90903, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] PState=0, Programming RtrnMode to 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70072, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnA to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080e, value : 32'h3}, //phyinit_io_write: 0x70072, 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70073, value : 32'h3}, //[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] Programming HwtLpCsEnB to 0x3
                          '{ step_type : REG_WRITE, reg_addr : 32'h9080f, value : 32'h3}, //phyinit_io_write: 0x70073, 0x3
//phyinit_io_write: 0x9080f, 0x3
//[dwc_ddrphy_phyinit_I_loadPIEImagePsLoop] End of dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(), PState=0
//[dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop] End of dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop(), PState=0
//[dwc_ddrphy_phyinit_I_loadPIEImage] Start of dwc_ddrphy_phyinit_I_loadPIEImage() prog_csr=1
                          '{ step_type : WAIT_DFI, reg_addr : 0, value : 40},
                          '{ step_type : REG_WRITE, reg_addr : 32'hd0000, value : 32'h0}, //Calling  [dwc_ddrphy_phyinit_userCustom_wait] to wait 40 DfiClks;
                          '{ step_type : REG_WRITE, reg_addr : 32'h41000, value : 32'h0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41001, value : 32'h0}, //phyinit_io_write: 0x41000, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41002, value : 32'h0}, //phyinit_io_write: 0x41001, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41003, value : 32'h0}, //phyinit_io_write: 0x41002, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41454, value : 32'hc028}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 16
                          '{ step_type : REG_WRITE, reg_addr : 32'h41455, value : 32'h100000}, //phyinit_io_write: 0x41454, 0xc028
                          '{ step_type : REG_WRITE, reg_addr : 32'h41456, value : 32'h0}, //phyinit_io_write: 0x41455, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41457, value : 32'h0}, //phyinit_io_write: 0x41456, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41458, value : 32'h0}, //phyinit_io_write: 0x41457, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41459, value : 32'h4000000}, //phyinit_io_write: 0x41458, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4145a, value : 32'h0}, //phyinit_io_write: 0x41459, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4145b, value : 32'h0}, //phyinit_io_write: 0x4145a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4145c, value : 32'h0}, //phyinit_io_write: 0x4145b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4145d, value : 32'h0}, //phyinit_io_write: 0x4145c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4145e, value : 32'h0}, //phyinit_io_write: 0x4145d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4145f, value : 32'h0}, //phyinit_io_write: 0x4145e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41460, value : 32'hc858}, //phyinit_io_write: 0x4145f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41461, value : 32'h100000}, //phyinit_io_write: 0x41460, 0xc858
                          '{ step_type : REG_WRITE, reg_addr : 32'h41462, value : 32'he088}, //phyinit_io_write: 0x41461, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41463, value : 32'h100000}, //phyinit_io_write: 0x41462, 0xe088
                          '{ step_type : REG_WRITE, reg_addr : 32'h41464, value : 32'he038}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41465, value : 32'h100000}, //phyinit_io_write: 0x41464, 0xe038
                          '{ step_type : REG_WRITE, reg_addr : 32'h41466, value : 32'hc858}, //phyinit_io_write: 0x41465, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41467, value : 32'h100000}, //phyinit_io_write: 0x41466, 0xc858
                          '{ step_type : REG_WRITE, reg_addr : 32'h41468, value : 32'hc088}, //phyinit_io_write: 0x41467, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41469, value : 32'h100000}, //phyinit_io_write: 0x41468, 0xc088
                          '{ step_type : REG_WRITE, reg_addr : 32'h4146a, value : 32'h0}, //phyinit_io_write: 0x41469, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4146b, value : 32'h0}, //phyinit_io_write: 0x4146a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4146c, value : 32'hc028}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 16
                          '{ step_type : REG_WRITE, reg_addr : 32'h4146d, value : 32'h100000}, //phyinit_io_write: 0x4146c, 0xc028
                          '{ step_type : REG_WRITE, reg_addr : 32'h4146e, value : 32'h0}, //phyinit_io_write: 0x4146d, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4146f, value : 32'h0}, //phyinit_io_write: 0x4146e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41470, value : 32'h0}, //phyinit_io_write: 0x4146f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41471, value : 32'h4000000}, //phyinit_io_write: 0x41470, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41472, value : 32'h0}, //phyinit_io_write: 0x41471, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41473, value : 32'h0}, //phyinit_io_write: 0x41472, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41474, value : 32'h0}, //phyinit_io_write: 0x41473, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41475, value : 32'h0}, //phyinit_io_write: 0x41474, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41476, value : 32'h0}, //phyinit_io_write: 0x41475, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41477, value : 32'h0}, //phyinit_io_write: 0x41476, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41478, value : 32'hc858}, //phyinit_io_write: 0x41477, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41479, value : 32'h100000}, //phyinit_io_write: 0x41478, 0xc858
                          '{ step_type : REG_WRITE, reg_addr : 32'h4147a, value : 32'he208}, //phyinit_io_write: 0x41479, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4147b, value : 32'h100000}, //phyinit_io_write: 0x4147a, 0xe208
                          '{ step_type : REG_WRITE, reg_addr : 32'h4147c, value : 32'he038}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4147d, value : 32'h100000}, //phyinit_io_write: 0x4147c, 0xe038
                          '{ step_type : REG_WRITE, reg_addr : 32'h4147e, value : 32'hc858}, //phyinit_io_write: 0x4147d, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4147f, value : 32'h100000}, //phyinit_io_write: 0x4147e, 0xc858
                          '{ step_type : REG_WRITE, reg_addr : 32'h41480, value : 32'hc208}, //phyinit_io_write: 0x4147f, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41481, value : 32'h100000}, //phyinit_io_write: 0x41480, 0xc208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41482, value : 32'h0}, //phyinit_io_write: 0x41481, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41483, value : 32'h0}, //phyinit_io_write: 0x41482, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41484, value : 32'hc040}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41485, value : 32'h100000}, //phyinit_io_write: 0x41484, 0xc040
                          '{ step_type : REG_WRITE, reg_addr : 32'h41486, value : 32'h0}, //phyinit_io_write: 0x41485, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41487, value : 32'h100000}, //phyinit_io_write: 0x41486, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41488, value : 32'hc068}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41489, value : 32'h100000}, //phyinit_io_write: 0x41488, 0xc068
                          '{ step_type : REG_WRITE, reg_addr : 32'h4148a, value : 32'h0}, //phyinit_io_write: 0x41489, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4148b, value : 32'h0}, //phyinit_io_write: 0x4148a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4148c, value : 32'hce58}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4148d, value : 32'h100000}, //phyinit_io_write: 0x4148c, 0xce58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4148e, value : 32'hc208}, //phyinit_io_write: 0x4148d, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4148f, value : 32'h100000}, //phyinit_io_write: 0x4148e, 0xc208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41490, value : 32'h0}, //phyinit_io_write: 0x4148f, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41491, value : 32'h0}, //phyinit_io_write: 0x41490, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41492, value : 32'h0}, //phyinit_io_write: 0x41491, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41493, value : 32'h0}, //phyinit_io_write: 0x41492, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41494, value : 32'hc370}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41495, value : 32'h100000}, //phyinit_io_write: 0x41494, 0xc370
                          '{ step_type : REG_WRITE, reg_addr : 32'h41496, value : 32'h0}, //phyinit_io_write: 0x41495, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41497, value : 32'h0}, //phyinit_io_write: 0x41496, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41498, value : 32'hd2d8}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 100
                          '{ step_type : REG_WRITE, reg_addr : 32'h41499, value : 32'h100000}, //phyinit_io_write: 0x41498, 0xd2d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4149a, value : 32'he008}, //phyinit_io_write: 0x41499, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4149b, value : 32'h100000}, //phyinit_io_write: 0x4149a, 0xe008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4149c, value : 32'h0}, //phyinit_io_write: 0x4149b, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4149d, value : 32'h7b000000}, //phyinit_io_write: 0x4149c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4149e, value : 32'h0}, //phyinit_io_write: 0x4149d, 0x7b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4149f, value : 32'h0}, //phyinit_io_write: 0x4149e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a0, value : 32'hc0f0}, //phyinit_io_write: 0x4149f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a1, value : 32'h100000}, //phyinit_io_write: 0x414a0, 0xc0f0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a2, value : 32'hcfd8}, //phyinit_io_write: 0x414a1, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a3, value : 32'h100000}, //phyinit_io_write: 0x414a2, 0xcfd8
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a4, value : 32'hc008}, //phyinit_io_write: 0x414a3, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a5, value : 32'h100000}, //phyinit_io_write: 0x414a4, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a6, value : 32'h0}, //phyinit_io_write: 0x414a5, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a7, value : 32'h0}, //phyinit_io_write: 0x414a6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a8, value : 32'h0}, //phyinit_io_write: 0x414a7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414a9, value : 32'h3b000000}, //phyinit_io_write: 0x414a8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414aa, value : 32'h0}, //phyinit_io_write: 0x414a9, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ab, value : 32'h0}, //phyinit_io_write: 0x414aa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ac, value : 32'h0}, //phyinit_io_write: 0x414ab, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ad, value : 32'h0}, //phyinit_io_write: 0x414ac, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ae, value : 32'hd058}, //phyinit_io_write: 0x414ad, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414af, value : 32'h100000}, //phyinit_io_write: 0x414ae, 0xd058
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b0, value : 32'hc008}, //phyinit_io_write: 0x414af, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b1, value : 32'h100000}, //phyinit_io_write: 0x414b0, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b2, value : 32'h0}, //phyinit_io_write: 0x414b1, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b3, value : 32'h0}, //phyinit_io_write: 0x414b2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b4, value : 32'h0}, //phyinit_io_write: 0x414b3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b5, value : 32'h3b000000}, //phyinit_io_write: 0x414b4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b6, value : 32'h0}, //phyinit_io_write: 0x414b5, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b7, value : 32'h0}, //phyinit_io_write: 0x414b6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b8, value : 32'h0}, //phyinit_io_write: 0x414b7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414b9, value : 32'h0}, //phyinit_io_write: 0x414b8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ba, value : 32'hd0d8}, //phyinit_io_write: 0x414b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414bb, value : 32'h100000}, //phyinit_io_write: 0x414ba, 0xd0d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h414bc, value : 32'hc088}, //phyinit_io_write: 0x414bb, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414bd, value : 32'h100000}, //phyinit_io_write: 0x414bc, 0xc088
                          '{ step_type : REG_WRITE, reg_addr : 32'h414be, value : 32'h0}, //phyinit_io_write: 0x414bd, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414bf, value : 32'h0}, //phyinit_io_write: 0x414be, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c0, value : 32'h0}, //phyinit_io_write: 0x414bf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c1, value : 32'h3b000000}, //phyinit_io_write: 0x414c0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c2, value : 32'h0}, //phyinit_io_write: 0x414c1, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c3, value : 32'h0}, //phyinit_io_write: 0x414c2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c4, value : 32'h0}, //phyinit_io_write: 0x414c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c5, value : 32'h0}, //phyinit_io_write: 0x414c4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c6, value : 32'hd158}, //phyinit_io_write: 0x414c5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c7, value : 32'h100000}, //phyinit_io_write: 0x414c6, 0xd158
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c8, value : 32'hc008}, //phyinit_io_write: 0x414c7, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414c9, value : 32'h100000}, //phyinit_io_write: 0x414c8, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ca, value : 32'h0}, //phyinit_io_write: 0x414c9, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414cb, value : 32'h0}, //phyinit_io_write: 0x414ca, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414cc, value : 32'h0}, //phyinit_io_write: 0x414cb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414cd, value : 32'h6b000000}, //phyinit_io_write: 0x414cc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ce, value : 32'h0}, //phyinit_io_write: 0x414cd, 0x6b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414cf, value : 32'h0}, //phyinit_io_write: 0x414ce, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d0, value : 32'h0}, //phyinit_io_write: 0x414cf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d1, value : 32'h0}, //phyinit_io_write: 0x414d0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d2, value : 32'h0}, //phyinit_io_write: 0x414d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d3, value : 32'h0}, //phyinit_io_write: 0x414d2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d4, value : 32'hd00402c}, //phyinit_io_write: 0x414d3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d5, value : 32'h4000001}, //phyinit_io_write: 0x414d4, 0xd00402c
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d6, value : 32'h8004050}, //phyinit_io_write: 0x414d5, 0x4000001
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d7, value : 32'h0}, //phyinit_io_write: 0x414d6, 0x8004050
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d8, value : 32'h0}, //phyinit_io_write: 0x414d7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414d9, value : 32'h4000000}, //phyinit_io_write: 0x414d8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414da, value : 32'h0}, //phyinit_io_write: 0x414d9, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414db, value : 32'h0}, //phyinit_io_write: 0x414da, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414dc, value : 32'h0}, //phyinit_io_write: 0x414db, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414dd, value : 32'h4000000}, //phyinit_io_write: 0x414dc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414de, value : 32'h8034050}, //phyinit_io_write: 0x414dd, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414df, value : 32'h0}, //phyinit_io_write: 0x414de, 0x8034050
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e0, value : 32'h0}, //phyinit_io_write: 0x414df, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e1, value : 32'h1f000000}, //phyinit_io_write: 0x414e0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e2, value : 32'h0}, //phyinit_io_write: 0x414e1, 0x1f000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e3, value : 32'h8000000}, //phyinit_io_write: 0x414e2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e4, value : 32'h0}, //phyinit_io_write: 0x414e3, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e5, value : 32'h4000000}, //phyinit_io_write: 0x414e4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e6, value : 32'h407c}, //phyinit_io_write: 0x414e5, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e7, value : 32'h0}, //phyinit_io_write: 0x414e6, 0x407c
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e8, value : 32'h0}, //phyinit_io_write: 0x414e7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414e9, value : 32'h4000000}, //phyinit_io_write: 0x414e8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ea, value : 32'h0}, //phyinit_io_write: 0x414e9, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414eb, value : 32'h0}, //phyinit_io_write: 0x414ea, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ec, value : 32'h0}, //phyinit_io_write: 0x414eb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ed, value : 32'h4000001}, //phyinit_io_write: 0x414ec, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ee, value : 32'h0}, //phyinit_io_write: 0x414ed, 0x4000001
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ef, value : 32'h0}, //phyinit_io_write: 0x414ee, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f0, value : 32'h0}, //phyinit_io_write: 0x414ef, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f1, value : 32'h4000000}, //phyinit_io_write: 0x414f0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f2, value : 32'h0}, //phyinit_io_write: 0x414f1, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f3, value : 32'h0}, //phyinit_io_write: 0x414f2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f4, value : 32'h0}, //phyinit_io_write: 0x414f3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f5, value : 32'h1b000000}, //phyinit_io_write: 0x414f4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f6, value : 32'h0}, //phyinit_io_write: 0x414f5, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f7, value : 32'h0}, //phyinit_io_write: 0x414f6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f8, value : 32'h0}, //phyinit_io_write: 0x414f7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414f9, value : 32'h0}, //phyinit_io_write: 0x414f8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414fa, value : 32'h0}, //phyinit_io_write: 0x414f9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414fb, value : 32'h0}, //phyinit_io_write: 0x414fa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h414fc, value : 32'hd00802c}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 40
                          '{ step_type : REG_WRITE, reg_addr : 32'h414fd, value : 32'h4100001}, //phyinit_io_write: 0x414fc, 0xd00802c
                          '{ step_type : REG_WRITE, reg_addr : 32'h414fe, value : 32'h8008050}, //phyinit_io_write: 0x414fd, 0x4100001
                          '{ step_type : REG_WRITE, reg_addr : 32'h414ff, value : 32'h100000}, //phyinit_io_write: 0x414fe, 0x8008050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41500, value : 32'h0}, //phyinit_io_write: 0x414ff, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41501, value : 32'h4000000}, //phyinit_io_write: 0x41500, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41502, value : 32'h0}, //phyinit_io_write: 0x41501, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41503, value : 32'h0}, //phyinit_io_write: 0x41502, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41504, value : 32'h0}, //phyinit_io_write: 0x41503, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41505, value : 32'h4000000}, //phyinit_io_write: 0x41504, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41506, value : 32'h8038050}, //phyinit_io_write: 0x41505, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41507, value : 32'h100000}, //phyinit_io_write: 0x41506, 0x8038050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41508, value : 32'h0}, //phyinit_io_write: 0x41507, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41509, value : 32'h1f000000}, //phyinit_io_write: 0x41508, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4150a, value : 32'h0}, //phyinit_io_write: 0x41509, 0x1f000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4150b, value : 32'h8000000}, //phyinit_io_write: 0x4150a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4150c, value : 32'h0}, //phyinit_io_write: 0x4150b, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4150d, value : 32'h4000000}, //phyinit_io_write: 0x4150c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4150e, value : 32'h807c}, //phyinit_io_write: 0x4150d, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4150f, value : 32'h100000}, //phyinit_io_write: 0x4150e, 0x807c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41510, value : 32'h0}, //phyinit_io_write: 0x4150f, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41511, value : 32'h4000000}, //phyinit_io_write: 0x41510, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41512, value : 32'h0}, //phyinit_io_write: 0x41511, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41513, value : 32'h0}, //phyinit_io_write: 0x41512, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41514, value : 32'h0}, //phyinit_io_write: 0x41513, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41515, value : 32'h4000001}, //phyinit_io_write: 0x41514, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41516, value : 32'h0}, //phyinit_io_write: 0x41515, 0x4000001
                          '{ step_type : REG_WRITE, reg_addr : 32'h41517, value : 32'h0}, //phyinit_io_write: 0x41516, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41518, value : 32'h0}, //phyinit_io_write: 0x41517, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41519, value : 32'h4000000}, //phyinit_io_write: 0x41518, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4151a, value : 32'h0}, //phyinit_io_write: 0x41519, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4151b, value : 32'h0}, //phyinit_io_write: 0x4151a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4151c, value : 32'h0}, //phyinit_io_write: 0x4151b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4151d, value : 32'h1b000000}, //phyinit_io_write: 0x4151c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4151e, value : 32'h0}, //phyinit_io_write: 0x4151d, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4151f, value : 32'h0}, //phyinit_io_write: 0x4151e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41520, value : 32'h0}, //phyinit_io_write: 0x4151f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41521, value : 32'h0}, //phyinit_io_write: 0x41520, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41522, value : 32'h0}, //phyinit_io_write: 0x41521, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41523, value : 32'h0}, //phyinit_io_write: 0x41522, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41524, value : 32'hd00402c}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 96
                          '{ step_type : REG_WRITE, reg_addr : 32'h41525, value : 32'h1}, //phyinit_io_write: 0x41524, 0xd00402c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41526, value : 32'h8004050}, //phyinit_io_write: 0x41525, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h41527, value : 32'h0}, //phyinit_io_write: 0x41526, 0x8004050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41528, value : 32'h0}, //phyinit_io_write: 0x41527, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41529, value : 32'h0}, //phyinit_io_write: 0x41528, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4152a, value : 32'h0}, //phyinit_io_write: 0x41529, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4152b, value : 32'h0}, //phyinit_io_write: 0x4152a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4152c, value : 32'h0}, //phyinit_io_write: 0x4152b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4152d, value : 32'h0}, //phyinit_io_write: 0x4152c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4152e, value : 32'h8034050}, //phyinit_io_write: 0x4152d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4152f, value : 32'h0}, //phyinit_io_write: 0x4152e, 0x8034050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41530, value : 32'h0}, //phyinit_io_write: 0x4152f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41531, value : 32'h0}, //phyinit_io_write: 0x41530, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41532, value : 32'h0}, //phyinit_io_write: 0x41531, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41533, value : 32'h0}, //phyinit_io_write: 0x41532, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41534, value : 32'h0}, //phyinit_io_write: 0x41533, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41535, value : 32'h0}, //phyinit_io_write: 0x41534, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41536, value : 32'h8034050}, //phyinit_io_write: 0x41535, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41537, value : 32'h0}, //phyinit_io_write: 0x41536, 0x8034050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41538, value : 32'h0}, //phyinit_io_write: 0x41537, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41539, value : 32'h0}, //phyinit_io_write: 0x41538, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4153a, value : 32'h0}, //phyinit_io_write: 0x41539, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4153b, value : 32'h0}, //phyinit_io_write: 0x4153a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4153c, value : 32'h0}, //phyinit_io_write: 0x4153b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4153d, value : 32'h0}, //phyinit_io_write: 0x4153c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4153e, value : 32'h8004050}, //phyinit_io_write: 0x4153d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4153f, value : 32'h0}, //phyinit_io_write: 0x4153e, 0x8004050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41540, value : 32'h0}, //phyinit_io_write: 0x4153f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41541, value : 32'h1b000000}, //phyinit_io_write: 0x41540, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41542, value : 32'h0}, //phyinit_io_write: 0x41541, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41543, value : 32'h8000000}, //phyinit_io_write: 0x41542, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41544, value : 32'h0}, //phyinit_io_write: 0x41543, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41545, value : 32'h0}, //phyinit_io_write: 0x41544, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41546, value : 32'h407c}, //phyinit_io_write: 0x41545, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41547, value : 32'h0}, //phyinit_io_write: 0x41546, 0x407c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41548, value : 32'h0}, //phyinit_io_write: 0x41547, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41549, value : 32'h0}, //phyinit_io_write: 0x41548, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4154a, value : 32'h0}, //phyinit_io_write: 0x41549, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4154b, value : 32'h0}, //phyinit_io_write: 0x4154a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4154c, value : 32'h0}, //phyinit_io_write: 0x4154b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4154d, value : 32'h1}, //phyinit_io_write: 0x4154c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4154e, value : 32'h0}, //phyinit_io_write: 0x4154d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4154f, value : 32'h0}, //phyinit_io_write: 0x4154e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41550, value : 32'h0}, //phyinit_io_write: 0x4154f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41551, value : 32'h5b000000}, //phyinit_io_write: 0x41550, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41552, value : 32'h0}, //phyinit_io_write: 0x41551, 0x5b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41553, value : 32'h1c000000}, //phyinit_io_write: 0x41552, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41554, value : 32'hd00802c}, //phyinit_io_write: 0x41553, 0x1c000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41555, value : 32'h100001}, //phyinit_io_write: 0x41554, 0xd00802c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41556, value : 32'h8008050}, //phyinit_io_write: 0x41555, 0x100001
                          '{ step_type : REG_WRITE, reg_addr : 32'h41557, value : 32'h100000}, //phyinit_io_write: 0x41556, 0x8008050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41558, value : 32'h0}, //phyinit_io_write: 0x41557, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41559, value : 32'h0}, //phyinit_io_write: 0x41558, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4155a, value : 32'h0}, //phyinit_io_write: 0x41559, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4155b, value : 32'h0}, //phyinit_io_write: 0x4155a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4155c, value : 32'h0}, //phyinit_io_write: 0x4155b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4155d, value : 32'h0}, //phyinit_io_write: 0x4155c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4155e, value : 32'h8038050}, //phyinit_io_write: 0x4155d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4155f, value : 32'h100000}, //phyinit_io_write: 0x4155e, 0x8038050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41560, value : 32'h0}, //phyinit_io_write: 0x4155f, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41561, value : 32'h0}, //phyinit_io_write: 0x41560, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41562, value : 32'h0}, //phyinit_io_write: 0x41561, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41563, value : 32'h0}, //phyinit_io_write: 0x41562, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41564, value : 32'h0}, //phyinit_io_write: 0x41563, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41565, value : 32'h0}, //phyinit_io_write: 0x41564, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41566, value : 32'h8038050}, //phyinit_io_write: 0x41565, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41567, value : 32'h100000}, //phyinit_io_write: 0x41566, 0x8038050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41568, value : 32'h0}, //phyinit_io_write: 0x41567, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41569, value : 32'h0}, //phyinit_io_write: 0x41568, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4156a, value : 32'h0}, //phyinit_io_write: 0x41569, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4156b, value : 32'h0}, //phyinit_io_write: 0x4156a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4156c, value : 32'h0}, //phyinit_io_write: 0x4156b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4156d, value : 32'h0}, //phyinit_io_write: 0x4156c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4156e, value : 32'h8008050}, //phyinit_io_write: 0x4156d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4156f, value : 32'h100000}, //phyinit_io_write: 0x4156e, 0x8008050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41570, value : 32'h0}, //phyinit_io_write: 0x4156f, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41571, value : 32'h1b000000}, //phyinit_io_write: 0x41570, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41572, value : 32'h0}, //phyinit_io_write: 0x41571, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41573, value : 32'h8000000}, //phyinit_io_write: 0x41572, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41574, value : 32'h0}, //phyinit_io_write: 0x41573, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41575, value : 32'h0}, //phyinit_io_write: 0x41574, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41576, value : 32'h807c}, //phyinit_io_write: 0x41575, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41577, value : 32'h100000}, //phyinit_io_write: 0x41576, 0x807c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41578, value : 32'h0}, //phyinit_io_write: 0x41577, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41579, value : 32'h0}, //phyinit_io_write: 0x41578, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4157a, value : 32'h0}, //phyinit_io_write: 0x41579, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4157b, value : 32'h0}, //phyinit_io_write: 0x4157a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4157c, value : 32'h0}, //phyinit_io_write: 0x4157b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4157d, value : 32'h1}, //phyinit_io_write: 0x4157c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4157e, value : 32'h0}, //phyinit_io_write: 0x4157d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4157f, value : 32'h0}, //phyinit_io_write: 0x4157e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41580, value : 32'h0}, //phyinit_io_write: 0x4157f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41581, value : 32'h4b000000}, //phyinit_io_write: 0x41580, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41582, value : 32'h0}, //phyinit_io_write: 0x41581, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41583, value : 32'h28000000}, //phyinit_io_write: 0x41582, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41584, value : 32'hd00402c}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 64
                          '{ step_type : REG_WRITE, reg_addr : 32'h41585, value : 32'h1}, //phyinit_io_write: 0x41584, 0xd00402c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41586, value : 32'h8035198}, //phyinit_io_write: 0x41585, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h41587, value : 32'h0}, //phyinit_io_write: 0x41586, 0x8035198
                          '{ step_type : REG_WRITE, reg_addr : 32'h41588, value : 32'h0}, //phyinit_io_write: 0x41587, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41589, value : 32'h2b000000}, //phyinit_io_write: 0x41588, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4158a, value : 32'h0}, //phyinit_io_write: 0x41589, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4158b, value : 32'h0}, //phyinit_io_write: 0x4158a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4158c, value : 32'h0}, //phyinit_io_write: 0x4158b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4158d, value : 32'h0}, //phyinit_io_write: 0x4158c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4158e, value : 32'h8035218}, //phyinit_io_write: 0x4158d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4158f, value : 32'h0}, //phyinit_io_write: 0x4158e, 0x8035218
                          '{ step_type : REG_WRITE, reg_addr : 32'h41590, value : 32'h0}, //phyinit_io_write: 0x4158f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41591, value : 32'h1b000000}, //phyinit_io_write: 0x41590, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41592, value : 32'h0}, //phyinit_io_write: 0x41591, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41593, value : 32'h8000000}, //phyinit_io_write: 0x41592, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41594, value : 32'h0}, //phyinit_io_write: 0x41593, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41595, value : 32'h0}, //phyinit_io_write: 0x41594, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41596, value : 32'h407c}, //phyinit_io_write: 0x41595, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41597, value : 32'h0}, //phyinit_io_write: 0x41596, 0x407c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41598, value : 32'h0}, //phyinit_io_write: 0x41597, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41599, value : 32'h0}, //phyinit_io_write: 0x41598, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4159a, value : 32'h0}, //phyinit_io_write: 0x41599, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4159b, value : 32'h0}, //phyinit_io_write: 0x4159a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4159c, value : 32'h0}, //phyinit_io_write: 0x4159b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4159d, value : 32'h1}, //phyinit_io_write: 0x4159c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4159e, value : 32'h0}, //phyinit_io_write: 0x4159d, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4159f, value : 32'h0}, //phyinit_io_write: 0x4159e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a0, value : 32'h0}, //phyinit_io_write: 0x4159f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a1, value : 32'h1b000000}, //phyinit_io_write: 0x415a0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a2, value : 32'h0}, //phyinit_io_write: 0x415a1, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a3, value : 32'h0}, //phyinit_io_write: 0x415a2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a4, value : 32'hd00802c}, //phyinit_io_write: 0x415a3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a5, value : 32'h100001}, //phyinit_io_write: 0x415a4, 0xd00802c
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a6, value : 32'h8039198}, //phyinit_io_write: 0x415a5, 0x100001
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a7, value : 32'h100000}, //phyinit_io_write: 0x415a6, 0x8039198
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a8, value : 32'h0}, //phyinit_io_write: 0x415a7, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415a9, value : 32'h2b000000}, //phyinit_io_write: 0x415a8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415aa, value : 32'h0}, //phyinit_io_write: 0x415a9, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ab, value : 32'h0}, //phyinit_io_write: 0x415aa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ac, value : 32'h0}, //phyinit_io_write: 0x415ab, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ad, value : 32'h0}, //phyinit_io_write: 0x415ac, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ae, value : 32'h8039218}, //phyinit_io_write: 0x415ad, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415af, value : 32'h100000}, //phyinit_io_write: 0x415ae, 0x8039218
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b0, value : 32'h0}, //phyinit_io_write: 0x415af, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b1, value : 32'h1b000000}, //phyinit_io_write: 0x415b0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b2, value : 32'h0}, //phyinit_io_write: 0x415b1, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b3, value : 32'h8000000}, //phyinit_io_write: 0x415b2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b4, value : 32'h0}, //phyinit_io_write: 0x415b3, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b5, value : 32'h0}, //phyinit_io_write: 0x415b4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b6, value : 32'h807c}, //phyinit_io_write: 0x415b5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b7, value : 32'h100000}, //phyinit_io_write: 0x415b6, 0x807c
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b8, value : 32'h0}, //phyinit_io_write: 0x415b7, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415b9, value : 32'h0}, //phyinit_io_write: 0x415b8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ba, value : 32'h0}, //phyinit_io_write: 0x415b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415bb, value : 32'h0}, //phyinit_io_write: 0x415ba, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415bc, value : 32'h0}, //phyinit_io_write: 0x415bb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415bd, value : 32'h1}, //phyinit_io_write: 0x415bc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415be, value : 32'h0}, //phyinit_io_write: 0x415bd, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h415bf, value : 32'h0}, //phyinit_io_write: 0x415be, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c0, value : 32'h0}, //phyinit_io_write: 0x415bf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c1, value : 32'h3b000000}, //phyinit_io_write: 0x415c0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c2, value : 32'h0}, //phyinit_io_write: 0x415c1, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c3, value : 32'h4000000}, //phyinit_io_write: 0x415c2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c4, value : 32'hd2d8}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 96
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c5, value : 32'h100000}, //phyinit_io_write: 0x415c4, 0xd2d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c6, value : 32'he008}, //phyinit_io_write: 0x415c5, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c7, value : 32'h100000}, //phyinit_io_write: 0x415c6, 0xe008
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c8, value : 32'h0}, //phyinit_io_write: 0x415c7, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415c9, value : 32'h7b000000}, //phyinit_io_write: 0x415c8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ca, value : 32'h0}, //phyinit_io_write: 0x415c9, 0x7b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415cb, value : 32'h0}, //phyinit_io_write: 0x415ca, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415cc, value : 32'hc0f0}, //phyinit_io_write: 0x415cb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415cd, value : 32'h100000}, //phyinit_io_write: 0x415cc, 0xc0f0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ce, value : 32'hcfd8}, //phyinit_io_write: 0x415cd, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415cf, value : 32'h100000}, //phyinit_io_write: 0x415ce, 0xcfd8
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d0, value : 32'hc008}, //phyinit_io_write: 0x415cf, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d1, value : 32'h100000}, //phyinit_io_write: 0x415d0, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d2, value : 32'h0}, //phyinit_io_write: 0x415d1, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d3, value : 32'h0}, //phyinit_io_write: 0x415d2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d4, value : 32'h0}, //phyinit_io_write: 0x415d3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d5, value : 32'h3b000000}, //phyinit_io_write: 0x415d4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d6, value : 32'h0}, //phyinit_io_write: 0x415d5, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d7, value : 32'h0}, //phyinit_io_write: 0x415d6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d8, value : 32'h0}, //phyinit_io_write: 0x415d7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415d9, value : 32'h0}, //phyinit_io_write: 0x415d8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415da, value : 32'hd058}, //phyinit_io_write: 0x415d9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415db, value : 32'h100000}, //phyinit_io_write: 0x415da, 0xd058
                          '{ step_type : REG_WRITE, reg_addr : 32'h415dc, value : 32'hc008}, //phyinit_io_write: 0x415db, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415dd, value : 32'h100000}, //phyinit_io_write: 0x415dc, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h415de, value : 32'h0}, //phyinit_io_write: 0x415dd, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415df, value : 32'h0}, //phyinit_io_write: 0x415de, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e0, value : 32'h0}, //phyinit_io_write: 0x415df, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e1, value : 32'h3b000000}, //phyinit_io_write: 0x415e0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e2, value : 32'h0}, //phyinit_io_write: 0x415e1, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e3, value : 32'h0}, //phyinit_io_write: 0x415e2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e4, value : 32'h0}, //phyinit_io_write: 0x415e3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e5, value : 32'h0}, //phyinit_io_write: 0x415e4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e6, value : 32'hd0d8}, //phyinit_io_write: 0x415e5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e7, value : 32'h100000}, //phyinit_io_write: 0x415e6, 0xd0d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e8, value : 32'hc088}, //phyinit_io_write: 0x415e7, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415e9, value : 32'h100000}, //phyinit_io_write: 0x415e8, 0xc088
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ea, value : 32'h0}, //phyinit_io_write: 0x415e9, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415eb, value : 32'h0}, //phyinit_io_write: 0x415ea, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ec, value : 32'h0}, //phyinit_io_write: 0x415eb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ed, value : 32'h3b000000}, //phyinit_io_write: 0x415ec, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ee, value : 32'h0}, //phyinit_io_write: 0x415ed, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ef, value : 32'h0}, //phyinit_io_write: 0x415ee, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f0, value : 32'h0}, //phyinit_io_write: 0x415ef, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f1, value : 32'h0}, //phyinit_io_write: 0x415f0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f2, value : 32'hd158}, //phyinit_io_write: 0x415f1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f3, value : 32'h100000}, //phyinit_io_write: 0x415f2, 0xd158
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f4, value : 32'hc008}, //phyinit_io_write: 0x415f3, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f5, value : 32'h100000}, //phyinit_io_write: 0x415f4, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f6, value : 32'h0}, //phyinit_io_write: 0x415f5, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f7, value : 32'h0}, //phyinit_io_write: 0x415f6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f8, value : 32'h0}, //phyinit_io_write: 0x415f7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415f9, value : 32'h6b000000}, //phyinit_io_write: 0x415f8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415fa, value : 32'h0}, //phyinit_io_write: 0x415f9, 0x6b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h415fb, value : 32'h0}, //phyinit_io_write: 0x415fa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415fc, value : 32'h0}, //phyinit_io_write: 0x415fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415fd, value : 32'h0}, //phyinit_io_write: 0x415fc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415fe, value : 32'h0}, //phyinit_io_write: 0x415fd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h415ff, value : 32'h0}, //phyinit_io_write: 0x415fe, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41600, value : 32'hd00402c}, //phyinit_io_write: 0x415ff, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41601, value : 32'h4000001}, //phyinit_io_write: 0x41600, 0xd00402c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41602, value : 32'h8004050}, //phyinit_io_write: 0x41601, 0x4000001
                          '{ step_type : REG_WRITE, reg_addr : 32'h41603, value : 32'h0}, //phyinit_io_write: 0x41602, 0x8004050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41604, value : 32'h0}, //phyinit_io_write: 0x41603, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41605, value : 32'h4000000}, //phyinit_io_write: 0x41604, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41606, value : 32'h8034050}, //phyinit_io_write: 0x41605, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41607, value : 32'h0}, //phyinit_io_write: 0x41606, 0x8034050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41608, value : 32'h0}, //phyinit_io_write: 0x41607, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41609, value : 32'h4f000000}, //phyinit_io_write: 0x41608, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4160a, value : 32'h0}, //phyinit_io_write: 0x41609, 0x4f000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4160b, value : 32'h8000000}, //phyinit_io_write: 0x4160a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4160c, value : 32'h407c}, //phyinit_io_write: 0x4160b, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4160d, value : 32'h4000000}, //phyinit_io_write: 0x4160c, 0x407c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4160e, value : 32'h0}, //phyinit_io_write: 0x4160d, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4160f, value : 32'h0}, //phyinit_io_write: 0x4160e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41610, value : 32'h0}, //phyinit_io_write: 0x4160f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41611, value : 32'h1f000000}, //phyinit_io_write: 0x41610, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41612, value : 32'h0}, //phyinit_io_write: 0x41611, 0x1f000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41613, value : 32'h0}, //phyinit_io_write: 0x41612, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41614, value : 32'h0}, //phyinit_io_write: 0x41613, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41615, value : 32'h4000001}, //phyinit_io_write: 0x41614, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41616, value : 32'h0}, //phyinit_io_write: 0x41615, 0x4000001
                          '{ step_type : REG_WRITE, reg_addr : 32'h41617, value : 32'h0}, //phyinit_io_write: 0x41616, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41618, value : 32'h0}, //phyinit_io_write: 0x41617, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41619, value : 32'h4000000}, //phyinit_io_write: 0x41618, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4161a, value : 32'h0}, //phyinit_io_write: 0x41619, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4161b, value : 32'h0}, //phyinit_io_write: 0x4161a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4161c, value : 32'h0}, //phyinit_io_write: 0x4161b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4161d, value : 32'h1b000000}, //phyinit_io_write: 0x4161c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4161e, value : 32'h0}, //phyinit_io_write: 0x4161d, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4161f, value : 32'h0}, //phyinit_io_write: 0x4161e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41620, value : 32'h0}, //phyinit_io_write: 0x4161f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41621, value : 32'h0}, //phyinit_io_write: 0x41620, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41622, value : 32'h0}, //phyinit_io_write: 0x41621, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41623, value : 32'h0}, //phyinit_io_write: 0x41622, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41624, value : 32'hd00802c}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 36
                          '{ step_type : REG_WRITE, reg_addr : 32'h41625, value : 32'h4100001}, //phyinit_io_write: 0x41624, 0xd00802c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41626, value : 32'h8008050}, //phyinit_io_write: 0x41625, 0x4100001
                          '{ step_type : REG_WRITE, reg_addr : 32'h41627, value : 32'h100000}, //phyinit_io_write: 0x41626, 0x8008050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41628, value : 32'h0}, //phyinit_io_write: 0x41627, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41629, value : 32'h4000000}, //phyinit_io_write: 0x41628, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4162a, value : 32'h8038050}, //phyinit_io_write: 0x41629, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4162b, value : 32'h100000}, //phyinit_io_write: 0x4162a, 0x8038050
                          '{ step_type : REG_WRITE, reg_addr : 32'h4162c, value : 32'h0}, //phyinit_io_write: 0x4162b, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4162d, value : 32'h4f000000}, //phyinit_io_write: 0x4162c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4162e, value : 32'h0}, //phyinit_io_write: 0x4162d, 0x4f000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4162f, value : 32'h8000000}, //phyinit_io_write: 0x4162e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41630, value : 32'h807c}, //phyinit_io_write: 0x4162f, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41631, value : 32'h4100000}, //phyinit_io_write: 0x41630, 0x807c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41632, value : 32'h0}, //phyinit_io_write: 0x41631, 0x4100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41633, value : 32'h0}, //phyinit_io_write: 0x41632, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41634, value : 32'h0}, //phyinit_io_write: 0x41633, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41635, value : 32'h1f000000}, //phyinit_io_write: 0x41634, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41636, value : 32'h0}, //phyinit_io_write: 0x41635, 0x1f000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41637, value : 32'h0}, //phyinit_io_write: 0x41636, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41638, value : 32'h0}, //phyinit_io_write: 0x41637, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41639, value : 32'h4000001}, //phyinit_io_write: 0x41638, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4163a, value : 32'h0}, //phyinit_io_write: 0x41639, 0x4000001
                          '{ step_type : REG_WRITE, reg_addr : 32'h4163b, value : 32'h0}, //phyinit_io_write: 0x4163a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4163c, value : 32'h0}, //phyinit_io_write: 0x4163b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4163d, value : 32'h4000000}, //phyinit_io_write: 0x4163c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4163e, value : 32'h0}, //phyinit_io_write: 0x4163d, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4163f, value : 32'h0}, //phyinit_io_write: 0x4163e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41640, value : 32'h0}, //phyinit_io_write: 0x4163f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41641, value : 32'h1b000000}, //phyinit_io_write: 0x41640, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41642, value : 32'h0}, //phyinit_io_write: 0x41641, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41643, value : 32'h0}, //phyinit_io_write: 0x41642, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41644, value : 32'h0}, //phyinit_io_write: 0x41643, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41645, value : 32'h0}, //phyinit_io_write: 0x41644, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41646, value : 32'h0}, //phyinit_io_write: 0x41645, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41647, value : 32'h0}, //phyinit_io_write: 0x41646, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41648, value : 32'hd00402c}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 72
                          '{ step_type : REG_WRITE, reg_addr : 32'h41649, value : 32'h1}, //phyinit_io_write: 0x41648, 0xd00402c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4164a, value : 32'h8004050}, //phyinit_io_write: 0x41649, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4164b, value : 32'h0}, //phyinit_io_write: 0x4164a, 0x8004050
                          '{ step_type : REG_WRITE, reg_addr : 32'h4164c, value : 32'h0}, //phyinit_io_write: 0x4164b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4164d, value : 32'h0}, //phyinit_io_write: 0x4164c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4164e, value : 32'h8034050}, //phyinit_io_write: 0x4164d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4164f, value : 32'h0}, //phyinit_io_write: 0x4164e, 0x8034050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41650, value : 32'h0}, //phyinit_io_write: 0x4164f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41651, value : 32'h0}, //phyinit_io_write: 0x41650, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41652, value : 32'h8034050}, //phyinit_io_write: 0x41651, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41653, value : 32'h0}, //phyinit_io_write: 0x41652, 0x8034050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41654, value : 32'h0}, //phyinit_io_write: 0x41653, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41655, value : 32'h0}, //phyinit_io_write: 0x41654, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41656, value : 32'h8004050}, //phyinit_io_write: 0x41655, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41657, value : 32'h0}, //phyinit_io_write: 0x41656, 0x8004050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41658, value : 32'h0}, //phyinit_io_write: 0x41657, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41659, value : 32'h4b000000}, //phyinit_io_write: 0x41658, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4165a, value : 32'h0}, //phyinit_io_write: 0x41659, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4165b, value : 32'h8000000}, //phyinit_io_write: 0x4165a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4165c, value : 32'h407c}, //phyinit_io_write: 0x4165b, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4165d, value : 32'h0}, //phyinit_io_write: 0x4165c, 0x407c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4165e, value : 32'h0}, //phyinit_io_write: 0x4165d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4165f, value : 32'h0}, //phyinit_io_write: 0x4165e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41660, value : 32'h0}, //phyinit_io_write: 0x4165f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41661, value : 32'h1b000000}, //phyinit_io_write: 0x41660, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41662, value : 32'h0}, //phyinit_io_write: 0x41661, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41663, value : 32'h0}, //phyinit_io_write: 0x41662, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41664, value : 32'h0}, //phyinit_io_write: 0x41663, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41665, value : 32'h1}, //phyinit_io_write: 0x41664, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41666, value : 32'h0}, //phyinit_io_write: 0x41665, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h41667, value : 32'h0}, //phyinit_io_write: 0x41666, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41668, value : 32'h0}, //phyinit_io_write: 0x41667, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41669, value : 32'h5b000000}, //phyinit_io_write: 0x41668, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4166a, value : 32'h0}, //phyinit_io_write: 0x41669, 0x5b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4166b, value : 32'h1c000000}, //phyinit_io_write: 0x4166a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4166c, value : 32'hd00802c}, //phyinit_io_write: 0x4166b, 0x1c000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4166d, value : 32'h100001}, //phyinit_io_write: 0x4166c, 0xd00802c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4166e, value : 32'h8008050}, //phyinit_io_write: 0x4166d, 0x100001
                          '{ step_type : REG_WRITE, reg_addr : 32'h4166f, value : 32'h100000}, //phyinit_io_write: 0x4166e, 0x8008050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41670, value : 32'h0}, //phyinit_io_write: 0x4166f, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41671, value : 32'h0}, //phyinit_io_write: 0x41670, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41672, value : 32'h8038050}, //phyinit_io_write: 0x41671, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41673, value : 32'h100000}, //phyinit_io_write: 0x41672, 0x8038050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41674, value : 32'h0}, //phyinit_io_write: 0x41673, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41675, value : 32'h0}, //phyinit_io_write: 0x41674, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41676, value : 32'h8038050}, //phyinit_io_write: 0x41675, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41677, value : 32'h100000}, //phyinit_io_write: 0x41676, 0x8038050
                          '{ step_type : REG_WRITE, reg_addr : 32'h41678, value : 32'h0}, //phyinit_io_write: 0x41677, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41679, value : 32'h0}, //phyinit_io_write: 0x41678, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4167a, value : 32'h8008050}, //phyinit_io_write: 0x41679, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4167b, value : 32'h100000}, //phyinit_io_write: 0x4167a, 0x8008050
                          '{ step_type : REG_WRITE, reg_addr : 32'h4167c, value : 32'h0}, //phyinit_io_write: 0x4167b, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4167d, value : 32'h4b000000}, //phyinit_io_write: 0x4167c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4167e, value : 32'h0}, //phyinit_io_write: 0x4167d, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4167f, value : 32'h8000000}, //phyinit_io_write: 0x4167e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41680, value : 32'h807c}, //phyinit_io_write: 0x4167f, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41681, value : 32'h100000}, //phyinit_io_write: 0x41680, 0x807c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41682, value : 32'h0}, //phyinit_io_write: 0x41681, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41683, value : 32'h0}, //phyinit_io_write: 0x41682, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41684, value : 32'h0}, //phyinit_io_write: 0x41683, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41685, value : 32'h1b000000}, //phyinit_io_write: 0x41684, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41686, value : 32'h0}, //phyinit_io_write: 0x41685, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41687, value : 32'h0}, //phyinit_io_write: 0x41686, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41688, value : 32'h0}, //phyinit_io_write: 0x41687, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41689, value : 32'h1}, //phyinit_io_write: 0x41688, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4168a, value : 32'h0}, //phyinit_io_write: 0x41689, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4168b, value : 32'h0}, //phyinit_io_write: 0x4168a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4168c, value : 32'h0}, //phyinit_io_write: 0x4168b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4168d, value : 32'h2b000000}, //phyinit_io_write: 0x4168c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4168e, value : 32'h0}, //phyinit_io_write: 0x4168d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4168f, value : 32'h28000000}, //phyinit_io_write: 0x4168e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41690, value : 32'hd00402c}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 68
                          '{ step_type : REG_WRITE, reg_addr : 32'h41691, value : 32'h1}, //phyinit_io_write: 0x41690, 0xd00402c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41692, value : 32'h8035198}, //phyinit_io_write: 0x41691, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h41693, value : 32'h0}, //phyinit_io_write: 0x41692, 0x8035198
                          '{ step_type : REG_WRITE, reg_addr : 32'h41694, value : 32'h0}, //phyinit_io_write: 0x41693, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41695, value : 32'h0}, //phyinit_io_write: 0x41694, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41696, value : 32'h0}, //phyinit_io_write: 0x41695, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41697, value : 32'h0}, //phyinit_io_write: 0x41696, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41698, value : 32'h0}, //phyinit_io_write: 0x41697, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41699, value : 32'h0}, //phyinit_io_write: 0x41698, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4169a, value : 32'h8035218}, //phyinit_io_write: 0x41699, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4169b, value : 32'h0}, //phyinit_io_write: 0x4169a, 0x8035218
                          '{ step_type : REG_WRITE, reg_addr : 32'h4169c, value : 32'h0}, //phyinit_io_write: 0x4169b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4169d, value : 32'h4b000000}, //phyinit_io_write: 0x4169c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4169e, value : 32'h0}, //phyinit_io_write: 0x4169d, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4169f, value : 32'h8000000}, //phyinit_io_write: 0x4169e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a0, value : 32'h407c}, //phyinit_io_write: 0x4169f, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a1, value : 32'h0}, //phyinit_io_write: 0x416a0, 0x407c
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a2, value : 32'h0}, //phyinit_io_write: 0x416a1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a3, value : 32'h0}, //phyinit_io_write: 0x416a2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a4, value : 32'h0}, //phyinit_io_write: 0x416a3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a5, value : 32'h1b000000}, //phyinit_io_write: 0x416a4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a6, value : 32'h0}, //phyinit_io_write: 0x416a5, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a7, value : 32'h0}, //phyinit_io_write: 0x416a6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a8, value : 32'h0}, //phyinit_io_write: 0x416a7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416a9, value : 32'h1}, //phyinit_io_write: 0x416a8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416aa, value : 32'h0}, //phyinit_io_write: 0x416a9, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ab, value : 32'h0}, //phyinit_io_write: 0x416aa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ac, value : 32'h0}, //phyinit_io_write: 0x416ab, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ad, value : 32'h0}, //phyinit_io_write: 0x416ac, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ae, value : 32'h0}, //phyinit_io_write: 0x416ad, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416af, value : 32'h0}, //phyinit_io_write: 0x416ae, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b0, value : 32'hd00802c}, //phyinit_io_write: 0x416af, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b1, value : 32'h100001}, //phyinit_io_write: 0x416b0, 0xd00802c
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b2, value : 32'h8039198}, //phyinit_io_write: 0x416b1, 0x100001
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b3, value : 32'h100000}, //phyinit_io_write: 0x416b2, 0x8039198
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b4, value : 32'h0}, //phyinit_io_write: 0x416b3, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b5, value : 32'h0}, //phyinit_io_write: 0x416b4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b6, value : 32'h0}, //phyinit_io_write: 0x416b5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b7, value : 32'h0}, //phyinit_io_write: 0x416b6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b8, value : 32'h0}, //phyinit_io_write: 0x416b7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416b9, value : 32'h0}, //phyinit_io_write: 0x416b8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ba, value : 32'h8039218}, //phyinit_io_write: 0x416b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416bb, value : 32'h100000}, //phyinit_io_write: 0x416ba, 0x8039218
                          '{ step_type : REG_WRITE, reg_addr : 32'h416bc, value : 32'h0}, //phyinit_io_write: 0x416bb, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416bd, value : 32'h4b000000}, //phyinit_io_write: 0x416bc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416be, value : 32'h0}, //phyinit_io_write: 0x416bd, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416bf, value : 32'h8000000}, //phyinit_io_write: 0x416be, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c0, value : 32'h807c}, //phyinit_io_write: 0x416bf, 0x8000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c1, value : 32'h100000}, //phyinit_io_write: 0x416c0, 0x807c
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c2, value : 32'h0}, //phyinit_io_write: 0x416c1, 0x100000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c3, value : 32'h0}, //phyinit_io_write: 0x416c2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c4, value : 32'h0}, //phyinit_io_write: 0x416c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c5, value : 32'h1b000000}, //phyinit_io_write: 0x416c4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c6, value : 32'h0}, //phyinit_io_write: 0x416c5, 0x1b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c7, value : 32'h0}, //phyinit_io_write: 0x416c6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c8, value : 32'h0}, //phyinit_io_write: 0x416c7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416c9, value : 32'h1}, //phyinit_io_write: 0x416c8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ca, value : 32'h0}, //phyinit_io_write: 0x416c9, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h416cb, value : 32'h0}, //phyinit_io_write: 0x416ca, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416cc, value : 32'h0}, //phyinit_io_write: 0x416cb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416cd, value : 32'h6b000000}, //phyinit_io_write: 0x416cc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416ce, value : 32'h0}, //phyinit_io_write: 0x416cd, 0x6b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h416cf, value : 32'h0}, //phyinit_io_write: 0x416ce, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d0, value : 32'h0}, //phyinit_io_write: 0x416cf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d1, value : 32'h0}, //phyinit_io_write: 0x416d0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d2, value : 32'h0}, //phyinit_io_write: 0x416d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d3, value : 32'h0}, //phyinit_io_write: 0x416d2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d4, value : 32'h0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d5, value : 32'h0}, //phyinit_io_write: 0x416d4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d6, value : 32'h0}, //phyinit_io_write: 0x416d5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h416d7, value : 32'h0}, //phyinit_io_write: 0x416d6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44000, value : 32'h3f7ab480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44001, value : 32'h16420}, //phyinit_io_write: 0x44000, 0x3f7ab480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44002, value : 32'h400}, //phyinit_io_write: 0x44001, 0x16420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44003, value : 32'h0}, //phyinit_io_write: 0x44002, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44004, value : 32'h80000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 12
                          '{ step_type : REG_WRITE, reg_addr : 32'h44005, value : 32'hfc0}, //phyinit_io_write: 0x44004, 0x80000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44006, value : 32'h4000c00}, //phyinit_io_write: 0x44005, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44007, value : 32'h0}, //phyinit_io_write: 0x44006, 0x4000c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44008, value : 32'h84000480}, //phyinit_io_write: 0x44007, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44009, value : 32'hc00}, //phyinit_io_write: 0x44008, 0x84000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4400a, value : 32'h4000800}, //phyinit_io_write: 0x44009, 0xc00
                          '{ step_type : REG_WRITE, reg_addr : 32'h4400b, value : 32'h0}, //phyinit_io_write: 0x4400a, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4400c, value : 32'h84000080}, //phyinit_io_write: 0x4400b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4400d, value : 32'hc00}, //phyinit_io_write: 0x4400c, 0x84000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4400e, value : 32'h1e0}, //phyinit_io_write: 0x4400d, 0xc00
                          '{ step_type : REG_WRITE, reg_addr : 32'h4400f, value : 32'h0}, //phyinit_io_write: 0x4400e, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44010, value : 32'h80068200}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44011, value : 32'h400f}, //phyinit_io_write: 0x44010, 0x80068200
                          '{ step_type : REG_WRITE, reg_addr : 32'h44012, value : 32'h8940}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 50
                          '{ step_type : REG_WRITE, reg_addr : 32'h44013, value : 32'h0}, //phyinit_io_write: 0x44012, 0x8940
                          '{ step_type : REG_WRITE, reg_addr : 32'h44014, value : 32'ha0000480}, //phyinit_io_write: 0x44013, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44015, value : 32'h2420}, //phyinit_io_write: 0x44014, 0xa0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44016, value : 32'h4000400}, //phyinit_io_write: 0x44015, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44017, value : 32'h0}, //phyinit_io_write: 0x44016, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44018, value : 32'h9c001ca0}, //phyinit_io_write: 0x44017, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44019, value : 32'h1c04}, //phyinit_io_write: 0x44018, 0x9c001ca0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4401a, value : 32'ha8000880}, //phyinit_io_write: 0x44019, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4401b, value : 32'h1c06}, //phyinit_io_write: 0x4401a, 0xa8000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4401c, value : 32'h80010080}, //phyinit_io_write: 0x4401b, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h4401d, value : 32'h1c04}, //phyinit_io_write: 0x4401c, 0x80010080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4401e, value : 32'h4000400}, //phyinit_io_write: 0x4401d, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4401f, value : 32'h0}, //phyinit_io_write: 0x4401e, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44020, value : 32'h80010480}, //phyinit_io_write: 0x4401f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44021, value : 32'h1c04}, //phyinit_io_write: 0x44020, 0x80010480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44022, value : 32'h4000800}, //phyinit_io_write: 0x44021, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44023, value : 32'h0}, //phyinit_io_write: 0x44022, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44024, value : 32'h40}, //phyinit_io_write: 0x44023, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44025, value : 32'h6000}, //phyinit_io_write: 0x44024, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h44026, value : 32'ha0000080}, //phyinit_io_write: 0x44025, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44027, value : 32'h2420}, //phyinit_io_write: 0x44026, 0xa0000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44028, value : 32'h1020}, //phyinit_io_write: 0x44027, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44029, value : 32'h0}, //phyinit_io_write: 0x44028, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h4402a, value : 32'h1020}, //phyinit_io_write: 0x44029, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4402b, value : 32'h0}, //phyinit_io_write: 0x4402a, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h4402c, value : 32'h3020}, //phyinit_io_write: 0x4402b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4402d, value : 32'h0}, //phyinit_io_write: 0x4402c, 0x3020
                          '{ step_type : REG_WRITE, reg_addr : 32'h4402e, value : 32'h80000080}, //phyinit_io_write: 0x4402d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4402f, value : 32'h1c04}, //phyinit_io_write: 0x4402e, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44030, value : 32'ha8000880}, //phyinit_io_write: 0x4402f, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44031, value : 32'h1c06}, //phyinit_io_write: 0x44030, 0xa8000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44032, value : 32'h80010880}, //phyinit_io_write: 0x44031, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44033, value : 32'h1c04}, //phyinit_io_write: 0x44032, 0x80010880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44034, value : 32'h4000400}, //phyinit_io_write: 0x44033, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44035, value : 32'h0}, //phyinit_io_write: 0x44034, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44036, value : 32'h80010c80}, //phyinit_io_write: 0x44035, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44037, value : 32'h1c04}, //phyinit_io_write: 0x44036, 0x80010c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44038, value : 32'h4000800}, //phyinit_io_write: 0x44037, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44039, value : 32'h0}, //phyinit_io_write: 0x44038, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4403a, value : 32'h1020}, //phyinit_io_write: 0x44039, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4403b, value : 32'h0}, //phyinit_io_write: 0x4403a, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h4403c, value : 32'h2c20}, //phyinit_io_write: 0x4403b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4403d, value : 32'h0}, //phyinit_io_write: 0x4403c, 0x2c20
                          '{ step_type : REG_WRITE, reg_addr : 32'h4403e, value : 32'h2c20}, //phyinit_io_write: 0x4403d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4403f, value : 32'h0}, //phyinit_io_write: 0x4403e, 0x2c20
                          '{ step_type : REG_WRITE, reg_addr : 32'h44040, value : 32'h2c20}, //phyinit_io_write: 0x4403f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44041, value : 32'h0}, //phyinit_io_write: 0x44040, 0x2c20
                          '{ step_type : REG_WRITE, reg_addr : 32'h44042, value : 32'h80000080}, //phyinit_io_write: 0x44041, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44043, value : 32'h1c04}, //phyinit_io_write: 0x44042, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44044, value : 32'h1e0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44045, value : 32'h0}, //phyinit_io_write: 0x44044, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44046, value : 32'ha8000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h44047, value : 32'h1c04}, //phyinit_io_write: 0x44046, 0xa8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44048, value : 32'h4000400}, //phyinit_io_write: 0x44047, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44049, value : 32'h0}, //phyinit_io_write: 0x44048, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4404a, value : 32'h40004200}, //phyinit_io_write: 0x44049, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4404b, value : 32'h4000}, //phyinit_io_write: 0x4404a, 0x40004200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4404c, value : 32'h10d40}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4404d, value : 32'h0}, //phyinit_io_write: 0x4404c, 0x10d40
                          '{ step_type : REG_WRITE, reg_addr : 32'h4404e, value : 32'hc80038a0}, //phyinit_io_write: 0x4404d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4404f, value : 32'h1c01}, //phyinit_io_write: 0x4404e, 0xc80038a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44050, value : 32'hcc003ca0}, //phyinit_io_write: 0x4404f, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44051, value : 32'h1c01}, //phyinit_io_write: 0x44050, 0xcc003ca0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44052, value : 32'ha40000a0}, //phyinit_io_write: 0x44051, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44053, value : 32'h1c06}, //phyinit_io_write: 0x44052, 0xa40000a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44054, value : 32'ha8001c80}, //phyinit_io_write: 0x44053, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44055, value : 32'h1c06}, //phyinit_io_write: 0x44054, 0xa8001c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44056, value : 32'h80051080}, //phyinit_io_write: 0x44055, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44057, value : 32'h1c04}, //phyinit_io_write: 0x44056, 0x80051080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44058, value : 32'h4000400}, //phyinit_io_write: 0x44057, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44059, value : 32'h0}, //phyinit_io_write: 0x44058, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4405a, value : 32'h80051480}, //phyinit_io_write: 0x44059, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4405b, value : 32'h1c04}, //phyinit_io_write: 0x4405a, 0x80051480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4405c, value : 32'h4000800}, //phyinit_io_write: 0x4405b, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4405d, value : 32'h0}, //phyinit_io_write: 0x4405c, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4405e, value : 32'h840}, //phyinit_io_write: 0x4405d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4405f, value : 32'h6000}, //phyinit_io_write: 0x4405e, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h44060, value : 32'h80000080}, //phyinit_io_write: 0x4405f, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44061, value : 32'h1c04}, //phyinit_io_write: 0x44060, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44062, value : 32'hcc000080}, //phyinit_io_write: 0x44061, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44063, value : 32'h1c01}, //phyinit_io_write: 0x44062, 0xcc000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44064, value : 32'ha8001c80}, //phyinit_io_write: 0x44063, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44065, value : 32'h1c06}, //phyinit_io_write: 0x44064, 0xa8001c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44066, value : 32'h80051880}, //phyinit_io_write: 0x44065, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44067, value : 32'h1c04}, //phyinit_io_write: 0x44066, 0x80051880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44068, value : 32'h4000400}, //phyinit_io_write: 0x44067, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44069, value : 32'h0}, //phyinit_io_write: 0x44068, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4406a, value : 32'h80051c80}, //phyinit_io_write: 0x44069, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4406b, value : 32'h1c04}, //phyinit_io_write: 0x4406a, 0x80051c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h4406c, value : 32'h4000800}, //phyinit_io_write: 0x4406b, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4406d, value : 32'h0}, //phyinit_io_write: 0x4406c, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4406e, value : 32'h840}, //phyinit_io_write: 0x4406d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4406f, value : 32'h6000}, //phyinit_io_write: 0x4406e, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h44070, value : 32'h80000080}, //phyinit_io_write: 0x4406f, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44071, value : 32'h1c04}, //phyinit_io_write: 0x44070, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44072, value : 32'hc8000080}, //phyinit_io_write: 0x44071, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44073, value : 32'h1c01}, //phyinit_io_write: 0x44072, 0xc8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44074, value : 32'hcc003ca0}, //phyinit_io_write: 0x44073, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44075, value : 32'h1c01}, //phyinit_io_write: 0x44074, 0xcc003ca0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44076, value : 32'ha8001c80}, //phyinit_io_write: 0x44075, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44077, value : 32'h1c06}, //phyinit_io_write: 0x44076, 0xa8001c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44078, value : 32'h80052080}, //phyinit_io_write: 0x44077, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44079, value : 32'h1c04}, //phyinit_io_write: 0x44078, 0x80052080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4407a, value : 32'h4000400}, //phyinit_io_write: 0x44079, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4407b, value : 32'h0}, //phyinit_io_write: 0x4407a, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4407c, value : 32'h80052480}, //phyinit_io_write: 0x4407b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4407d, value : 32'h1c04}, //phyinit_io_write: 0x4407c, 0x80052480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4407e, value : 32'h4000800}, //phyinit_io_write: 0x4407d, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4407f, value : 32'h0}, //phyinit_io_write: 0x4407e, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44080, value : 32'h840}, //phyinit_io_write: 0x4407f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44081, value : 32'h6000}, //phyinit_io_write: 0x44080, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h44082, value : 32'h80000080}, //phyinit_io_write: 0x44081, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44083, value : 32'h1c04}, //phyinit_io_write: 0x44082, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44084, value : 32'hc80038a0}, //phyinit_io_write: 0x44083, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44085, value : 32'h1c01}, //phyinit_io_write: 0x44084, 0xc80038a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44086, value : 32'h54000091}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h44087, value : 32'h18fc0}, //phyinit_io_write: 0x44086, 0x54000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h44088, value : 32'h54000091}, //phyinit_io_write: 0x44087, 0x18fc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44089, value : 32'h14fc0}, //phyinit_io_write: 0x44088, 0x54000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h4408a, value : 32'hf0000091}, //phyinit_io_write: 0x44089, 0x14fc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4408b, value : 32'h187c1}, //phyinit_io_write: 0x4408a, 0xf0000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h4408c, value : 32'hf0000091}, //phyinit_io_write: 0x4408b, 0x187c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4408d, value : 32'h147c1}, //phyinit_io_write: 0x4408c, 0xf0000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h4408e, value : 32'h8000611}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4408f, value : 32'h1800}, //phyinit_io_write: 0x4408e, 0x8000611
                          '{ step_type : REG_WRITE, reg_addr : 32'h44090, value : 32'h13971}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h44091, value : 32'h0}, //phyinit_io_write: 0x44090, 0x13971
                          '{ step_type : REG_WRITE, reg_addr : 32'h44092, value : 32'h4000911}, //phyinit_io_write: 0x44091, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44093, value : 32'h1a420}, //phyinit_io_write: 0x44092, 0x4000911
                          '{ step_type : REG_WRITE, reg_addr : 32'h44094, value : 32'h4001000}, //phyinit_io_write: 0x44093, 0x1a420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44095, value : 32'h0}, //phyinit_io_write: 0x44094, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44096, value : 32'ha11}, //phyinit_io_write: 0x44095, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44097, value : 32'h1800}, //phyinit_io_write: 0x44096, 0xa11
                          '{ step_type : REG_WRITE, reg_addr : 32'h44098, value : 32'h17151}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44099, value : 32'h0}, //phyinit_io_write: 0x44098, 0x17151
                          '{ step_type : REG_WRITE, reg_addr : 32'h4409a, value : 32'h14171}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4409b, value : 32'h0}, //phyinit_io_write: 0x4409a, 0x14171
                          '{ step_type : REG_WRITE, reg_addr : 32'h4409c, value : 32'h611}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4409d, value : 32'h1800}, //phyinit_io_write: 0x4409c, 0x611
                          '{ step_type : REG_WRITE, reg_addr : 32'h4409e, value : 32'h17171}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4409f, value : 32'h0}, //phyinit_io_write: 0x4409e, 0x17171
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a0, value : 32'h24000491}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a1, value : 32'h1e420}, //phyinit_io_write: 0x440a0, 0x24000491
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a2, value : 32'h21d1}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 22
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a3, value : 32'h0}, //phyinit_io_write: 0x440a2, 0x21d1
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a4, value : 32'h1031}, //phyinit_io_write: 0x440a3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a5, value : 32'h0}, //phyinit_io_write: 0x440a4, 0x1031
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a6, value : 32'h1031}, //phyinit_io_write: 0x440a5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a7, value : 32'h0}, //phyinit_io_write: 0x440a6, 0x1031
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a8, value : 32'h2c31}, //phyinit_io_write: 0x440a7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440a9, value : 32'h0}, //phyinit_io_write: 0x440a8, 0x2c31
                          '{ step_type : REG_WRITE, reg_addr : 32'h440aa, value : 32'ha8000091}, //phyinit_io_write: 0x440a9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ab, value : 32'h1c06}, //phyinit_io_write: 0x440aa, 0xa8000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ac, value : 32'h80016891}, //phyinit_io_write: 0x440ab, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ad, value : 32'h1c04}, //phyinit_io_write: 0x440ac, 0x80016891
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ae, value : 32'h4000400}, //phyinit_io_write: 0x440ad, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h440af, value : 32'h0}, //phyinit_io_write: 0x440ae, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b0, value : 32'h80016c91}, //phyinit_io_write: 0x440af, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b1, value : 32'h1c04}, //phyinit_io_write: 0x440b0, 0x80016c91
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b2, value : 32'h4000800}, //phyinit_io_write: 0x440b1, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b3, value : 32'h0}, //phyinit_io_write: 0x440b2, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b4, value : 32'h851}, //phyinit_io_write: 0x440b3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b5, value : 32'h6000}, //phyinit_io_write: 0x440b4, 0x851
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b6, value : 32'h80000091}, //phyinit_io_write: 0x440b5, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b7, value : 32'h1c04}, //phyinit_io_write: 0x440b6, 0x80000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b8, value : 32'ha8000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440b9, value : 32'h1c04}, //phyinit_io_write: 0x440b8, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ba, value : 32'h4000800}, //phyinit_io_write: 0x440b9, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h440bb, value : 32'h0}, //phyinit_io_write: 0x440ba, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h440bc, value : 32'h1e0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h440bd, value : 32'h0}, //phyinit_io_write: 0x440bc, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440be, value : 32'ha8000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h440bf, value : 32'h1c06}, //phyinit_io_write: 0x440be, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c0, value : 32'h80012880}, //phyinit_io_write: 0x440bf, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c1, value : 32'h1c04}, //phyinit_io_write: 0x440c0, 0x80012880
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c2, value : 32'h4000400}, //phyinit_io_write: 0x440c1, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c3, value : 32'h0}, //phyinit_io_write: 0x440c2, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c4, value : 32'h80012c80}, //phyinit_io_write: 0x440c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c5, value : 32'h1c04}, //phyinit_io_write: 0x440c4, 0x80012c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c6, value : 32'h4000800}, //phyinit_io_write: 0x440c5, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c7, value : 32'h0}, //phyinit_io_write: 0x440c6, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c8, value : 32'h840}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h440c9, value : 32'h6000}, //phyinit_io_write: 0x440c8, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ca, value : 32'h80000080}, //phyinit_io_write: 0x440c9, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h440cb, value : 32'h1c04}, //phyinit_io_write: 0x440ca, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h440cc, value : 32'h1e0}, //phyinit_io_write: 0x440cb, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h440cd, value : 32'h0}, //phyinit_io_write: 0x440cc, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ce, value : 32'h80200}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h440cf, value : 32'h400e}, //phyinit_io_write: 0x440ce, 0x80200
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d0, value : 32'h1b140}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d1, value : 32'h0}, //phyinit_io_write: 0x440d0, 0x1b140
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d2, value : 32'h20200}, //phyinit_io_write: 0x440d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d3, value : 32'h400e}, //phyinit_io_write: 0x440d2, 0x20200
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d4, value : 32'h1b140}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d5, value : 32'h0}, //phyinit_io_write: 0x440d4, 0x1b140
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d6, value : 32'h80068200}, //phyinit_io_write: 0x440d5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d7, value : 32'h400f}, //phyinit_io_write: 0x440d6, 0x80068200
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d8, value : 32'h30000cc0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440d9, value : 32'h7c4}, //phyinit_io_write: 0x440d8, 0x30000cc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440da, value : 32'h1e0}, //phyinit_io_write: 0x440d9, 0x7c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440db, value : 32'h0}, //phyinit_io_write: 0x440da, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440dc, value : 32'h100600}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 116
                          '{ step_type : REG_WRITE, reg_addr : 32'h440dd, value : 32'h10}, //phyinit_io_write: 0x440dc, 0x100600
                          '{ step_type : REG_WRITE, reg_addr : 32'h440de, value : 32'h2c0004c0}, //phyinit_io_write: 0x440dd, 0x10
                          '{ step_type : REG_WRITE, reg_addr : 32'h440df, value : 32'h3c0}, //phyinit_io_write: 0x440de, 0x2c0004c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e0, value : 32'h8c0028a0}, //phyinit_io_write: 0x440df, 0x3c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e1, value : 32'h17bc1}, //phyinit_io_write: 0x440e0, 0x8c0028a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e2, value : 32'ha0000480}, //phyinit_io_write: 0x440e1, 0x17bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e3, value : 32'h2420}, //phyinit_io_write: 0x440e2, 0xa0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e4, value : 32'h4000400}, //phyinit_io_write: 0x440e3, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e5, value : 32'h0}, //phyinit_io_write: 0x440e4, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e6, value : 32'h8c0014a0}, //phyinit_io_write: 0x440e5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e7, value : 32'h143c1}, //phyinit_io_write: 0x440e6, 0x8c0014a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e8, value : 32'ha0000080}, //phyinit_io_write: 0x440e7, 0x143c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h440e9, value : 32'h2420}, //phyinit_io_write: 0x440e8, 0xa0000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ea, value : 32'h78000480}, //phyinit_io_write: 0x440e9, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h440eb, value : 32'h3d8}, //phyinit_io_write: 0x440ea, 0x78000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ec, value : 32'h7c000480}, //phyinit_io_write: 0x440eb, 0x3d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ed, value : 32'h7f8}, //phyinit_io_write: 0x440ec, 0x7c000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ee, value : 32'h8000080}, //phyinit_io_write: 0x440ed, 0x7f8
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ef, value : 32'hfe0}, //phyinit_io_write: 0x440ee, 0x8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f0, value : 32'h8000080}, //phyinit_io_write: 0x440ef, 0xfe0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f1, value : 32'h7e0}, //phyinit_io_write: 0x440f0, 0x8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f2, value : 32'h80600}, //phyinit_io_write: 0x440f1, 0x7e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f3, value : 32'h8}, //phyinit_io_write: 0x440f2, 0x80600
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f4, value : 32'h4c0}, //phyinit_io_write: 0x440f3, 0x8
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f5, value : 32'h14fc4}, //phyinit_io_write: 0x440f4, 0x4c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f6, value : 32'h4c0}, //phyinit_io_write: 0x440f5, 0x14fc4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f7, value : 32'h147c4}, //phyinit_io_write: 0x440f6, 0x4c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f8, value : 32'h2420}, //phyinit_io_write: 0x440f7, 0x147c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h440f9, value : 32'h0}, //phyinit_io_write: 0x440f8, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h440fa, value : 32'h8000480}, //phyinit_io_write: 0x440f9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440fb, value : 32'hfe0}, //phyinit_io_write: 0x440fa, 0x8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h440fc, value : 32'h8000480}, //phyinit_io_write: 0x440fb, 0xfe0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440fd, value : 32'h7e0}, //phyinit_io_write: 0x440fc, 0x8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h440fe, value : 32'h80}, //phyinit_io_write: 0x440fd, 0x7e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h440ff, value : 32'h14fc4}, //phyinit_io_write: 0x440fe, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44100, value : 32'h80}, //phyinit_io_write: 0x440ff, 0x14fc4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44101, value : 32'h147c4}, //phyinit_io_write: 0x44100, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44102, value : 32'h78000080}, //phyinit_io_write: 0x44101, 0x147c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44103, value : 32'h3d8}, //phyinit_io_write: 0x44102, 0x78000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44104, value : 32'h7c000080}, //phyinit_io_write: 0x44103, 0x3d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h44105, value : 32'h7f8}, //phyinit_io_write: 0x44104, 0x7c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44106, value : 32'h8c002ca0}, //phyinit_io_write: 0x44105, 0x7f8
                          '{ step_type : REG_WRITE, reg_addr : 32'h44107, value : 32'h17bc1}, //phyinit_io_write: 0x44106, 0x8c002ca0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44108, value : 32'ha0000480}, //phyinit_io_write: 0x44107, 0x17bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44109, value : 32'h2420}, //phyinit_io_write: 0x44108, 0xa0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4410a, value : 32'h4000400}, //phyinit_io_write: 0x44109, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h4410b, value : 32'h0}, //phyinit_io_write: 0x4410a, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4410c, value : 32'h8c0018a0}, //phyinit_io_write: 0x4410b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4410d, value : 32'h143c1}, //phyinit_io_write: 0x4410c, 0x8c0018a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4410e, value : 32'ha0000080}, //phyinit_io_write: 0x4410d, 0x143c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4410f, value : 32'h2420}, //phyinit_io_write: 0x4410e, 0xa0000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44110, value : 32'h2c000080}, //phyinit_io_write: 0x4410f, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44111, value : 32'h0}, //phyinit_io_write: 0x44110, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44112, value : 32'h2c000080}, //phyinit_io_write: 0x44111, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44113, value : 32'h40}, //phyinit_io_write: 0x44112, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44114, value : 32'h2c000080}, //phyinit_io_write: 0x44113, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h44115, value : 32'h80}, //phyinit_io_write: 0x44114, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44116, value : 32'h2c000080}, //phyinit_io_write: 0x44115, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44117, value : 32'hc0}, //phyinit_io_write: 0x44116, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44118, value : 32'h2c000080}, //phyinit_io_write: 0x44117, 0xc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44119, value : 32'h100}, //phyinit_io_write: 0x44118, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4411a, value : 32'h2c000080}, //phyinit_io_write: 0x44119, 0x100
                          '{ step_type : REG_WRITE, reg_addr : 32'h4411b, value : 32'h140}, //phyinit_io_write: 0x4411a, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4411c, value : 32'h200600}, //phyinit_io_write: 0x4411b, 0x140
                          '{ step_type : REG_WRITE, reg_addr : 32'h4411d, value : 32'h20}, //phyinit_io_write: 0x4411c, 0x200600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4411e, value : 32'h2c0000c0}, //phyinit_io_write: 0x4411d, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h4411f, value : 32'h1c0}, //phyinit_io_write: 0x4411e, 0x2c0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44120, value : 32'h2c0000c0}, //phyinit_io_write: 0x4411f, 0x1c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44121, value : 32'h200}, //phyinit_io_write: 0x44120, 0x2c0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44122, value : 32'h2c0000c0}, //phyinit_io_write: 0x44121, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h44123, value : 32'h240}, //phyinit_io_write: 0x44122, 0x2c0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44124, value : 32'h2c0000c0}, //phyinit_io_write: 0x44123, 0x240
                          '{ step_type : REG_WRITE, reg_addr : 32'h44125, value : 32'h280}, //phyinit_io_write: 0x44124, 0x2c0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44126, value : 32'h2c0000c0}, //phyinit_io_write: 0x44125, 0x280
                          '{ step_type : REG_WRITE, reg_addr : 32'h44127, value : 32'h2c0}, //phyinit_io_write: 0x44126, 0x2c0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44128, value : 32'h2c0000c0}, //phyinit_io_write: 0x44127, 0x2c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44129, value : 32'h300}, //phyinit_io_write: 0x44128, 0x2c0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4412a, value : 32'hc4000880}, //phyinit_io_write: 0x44129, 0x300
                          '{ step_type : REG_WRITE, reg_addr : 32'h4412b, value : 32'h7c0}, //phyinit_io_write: 0x4412a, 0xc4000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4412c, value : 32'h4000400}, //phyinit_io_write: 0x4412b, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4412d, value : 32'h0}, //phyinit_io_write: 0x4412c, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4412e, value : 32'hc000480}, //phyinit_io_write: 0x4412d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4412f, value : 32'hfc4}, //phyinit_io_write: 0x4412e, 0xc000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44130, value : 32'h4002000}, //phyinit_io_write: 0x4412f, 0xfc4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44131, value : 32'h0}, //phyinit_io_write: 0x44130, 0x4002000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44132, value : 32'hc000480}, //phyinit_io_write: 0x44131, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44133, value : 32'h7c4}, //phyinit_io_write: 0x44132, 0xc000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44134, value : 32'h4002000}, //phyinit_io_write: 0x44133, 0x7c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44135, value : 32'h0}, //phyinit_io_write: 0x44134, 0x4002000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44136, value : 32'hc000080}, //phyinit_io_write: 0x44135, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44137, value : 32'hfc4}, //phyinit_io_write: 0x44136, 0xc000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44138, value : 32'hc000080}, //phyinit_io_write: 0x44137, 0xfc4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44139, value : 32'h7c4}, //phyinit_io_write: 0x44138, 0xc000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4413a, value : 32'hc4000080}, //phyinit_io_write: 0x44139, 0x7c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4413b, value : 32'h7c0}, //phyinit_io_write: 0x4413a, 0xc4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4413c, value : 32'h4000400}, //phyinit_io_write: 0x4413b, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4413d, value : 32'h0}, //phyinit_io_write: 0x4413c, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4413e, value : 32'he0000480}, //phyinit_io_write: 0x4413d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4413f, value : 32'h803}, //phyinit_io_write: 0x4413e, 0xe0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44140, value : 32'h4002000}, //phyinit_io_write: 0x4413f, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h44141, value : 32'h0}, //phyinit_io_write: 0x44140, 0x4002000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44142, value : 32'h4000600}, //phyinit_io_write: 0x44141, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44143, value : 32'h400}, //phyinit_io_write: 0x44142, 0x4000600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44144, value : 32'h265a58c0}, //phyinit_io_write: 0x44143, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44145, value : 32'h187c8}, //phyinit_io_write: 0x44144, 0x265a58c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44146, value : 32'h58000080}, //phyinit_io_write: 0x44145, 0x187c8
                          '{ step_type : REG_WRITE, reg_addr : 32'h44147, value : 32'h7c0}, //phyinit_io_write: 0x44146, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44148, value : 32'h4000400}, //phyinit_io_write: 0x44147, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44149, value : 32'h0}, //phyinit_io_write: 0x44148, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4414a, value : 32'he0000080}, //phyinit_io_write: 0x44149, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4414b, value : 32'h803}, //phyinit_io_write: 0x4414a, 0xe0000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4414c, value : 32'h4002000}, //phyinit_io_write: 0x4414b, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h4414d, value : 32'h0}, //phyinit_io_write: 0x4414c, 0x4002000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4414e, value : 32'h1e0}, //phyinit_io_write: 0x4414d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4414f, value : 32'h0}, //phyinit_io_write: 0x4414e, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44150, value : 32'h50000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 38
                          '{ step_type : REG_WRITE, reg_addr : 32'h44151, value : 32'h1c01}, //phyinit_io_write: 0x44150, 0x50000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44152, value : 32'h40000480}, //phyinit_io_write: 0x44151, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44153, value : 32'h2c0c}, //phyinit_io_write: 0x44152, 0x40000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44154, value : 32'hc4000080}, //phyinit_io_write: 0x44153, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44155, value : 32'h7c0}, //phyinit_io_write: 0x44154, 0xc4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44156, value : 32'h2c000080}, //phyinit_io_write: 0x44155, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44157, value : 32'h7c2}, //phyinit_io_write: 0x44156, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44158, value : 32'h8c200080}, //phyinit_io_write: 0x44157, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44159, value : 32'hfc2}, //phyinit_io_write: 0x44158, 0x8c200080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4415a, value : 32'h200600}, //phyinit_io_write: 0x44159, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4415b, value : 32'h20}, //phyinit_io_write: 0x4415a, 0x200600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4415c, value : 32'h880c0080}, //phyinit_io_write: 0x4415b, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h4415d, value : 32'hc02}, //phyinit_io_write: 0x4415c, 0x880c0080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4415e, value : 32'h880c00c0}, //phyinit_io_write: 0x4415d, 0xc02
                          '{ step_type : REG_WRITE, reg_addr : 32'h4415f, value : 32'hc42}, //phyinit_io_write: 0x4415e, 0x880c00c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44160, value : 32'h247ffc80}, //phyinit_io_write: 0x4415f, 0xc42
                          '{ step_type : REG_WRITE, reg_addr : 32'h44161, value : 32'h7c2}, //phyinit_io_write: 0x44160, 0x247ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44162, value : 32'h281ffc80}, //phyinit_io_write: 0x44161, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44163, value : 32'h7c2}, //phyinit_io_write: 0x44162, 0x281ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44164, value : 32'h4000400}, //phyinit_io_write: 0x44163, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44165, value : 32'h0}, //phyinit_io_write: 0x44164, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44166, value : 32'h800c0080}, //phyinit_io_write: 0x44165, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44167, value : 32'hfc2}, //phyinit_io_write: 0x44166, 0x800c0080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44168, value : 32'h4000800}, //phyinit_io_write: 0x44167, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44169, value : 32'h0}, //phyinit_io_write: 0x44168, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4416a, value : 32'h98000480}, //phyinit_io_write: 0x44169, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4416b, value : 32'hfc2}, //phyinit_io_write: 0x4416a, 0x98000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4416c, value : 32'h28000480}, //phyinit_io_write: 0x4416b, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4416d, value : 32'hfc0}, //phyinit_io_write: 0x4416c, 0x28000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4416e, value : 32'h4001000}, //phyinit_io_write: 0x4416d, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4416f, value : 32'h0}, //phyinit_io_write: 0x4416e, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44170, value : 32'h80fffc80}, //phyinit_io_write: 0x4416f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44171, value : 32'hfc2}, //phyinit_io_write: 0x44170, 0x80fffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44172, value : 32'h30000080}, //phyinit_io_write: 0x44171, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44173, value : 32'h7c4}, //phyinit_io_write: 0x44172, 0x30000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44174, value : 32'h10600}, //phyinit_io_write: 0x44173, 0x7c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44175, value : 32'h1}, //phyinit_io_write: 0x44174, 0x10600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44176, value : 32'h2f940}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44177, value : 32'h0}, //phyinit_io_write: 0x44176, 0x2f940
                          '{ step_type : REG_WRITE, reg_addr : 32'h44178, value : 32'h80068200}, //phyinit_io_write: 0x44177, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44179, value : 32'h400f}, //phyinit_io_write: 0x44178, 0x80068200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4417a, value : 32'h2fd60}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4417b, value : 32'h0}, //phyinit_io_write: 0x4417a, 0x2fd60
                          '{ step_type : REG_WRITE, reg_addr : 32'h4417c, value : 32'h19dc0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4417d, value : 32'h0}, //phyinit_io_write: 0x4417c, 0x19dc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4417e, value : 32'he0000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 30
                          '{ step_type : REG_WRITE, reg_addr : 32'h4417f, value : 32'h803}, //phyinit_io_write: 0x4417e, 0xe0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44180, value : 32'h4001c00}, //phyinit_io_write: 0x4417f, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h44181, value : 32'h0}, //phyinit_io_write: 0x44180, 0x4001c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44182, value : 32'h28000080}, //phyinit_io_write: 0x44181, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44183, value : 32'hfc0}, //phyinit_io_write: 0x44182, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44184, value : 32'h88000480}, //phyinit_io_write: 0x44183, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44185, value : 32'h802}, //phyinit_io_write: 0x44184, 0x88000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44186, value : 32'h4000400}, //phyinit_io_write: 0x44185, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h44187, value : 32'h0}, //phyinit_io_write: 0x44186, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44188, value : 32'h5c000080}, //phyinit_io_write: 0x44187, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44189, value : 32'h7c2}, //phyinit_io_write: 0x44188, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4418a, value : 32'h2000600}, //phyinit_io_write: 0x44189, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4418b, value : 32'h200}, //phyinit_io_write: 0x4418a, 0x2000600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4418c, value : 32'h2c0010c0}, //phyinit_io_write: 0x4418b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4418d, value : 32'h3bc1}, //phyinit_io_write: 0x4418c, 0x2c0010c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4418e, value : 32'h2c001880}, //phyinit_io_write: 0x4418d, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4418f, value : 32'h3bc1}, //phyinit_io_write: 0x4418e, 0x2c001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44190, value : 32'h18001880}, //phyinit_io_write: 0x4418f, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44191, value : 32'h3bc1}, //phyinit_io_write: 0x44190, 0x18001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44192, value : 32'h1c001880}, //phyinit_io_write: 0x44191, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44193, value : 32'h3bc1}, //phyinit_io_write: 0x44192, 0x1c001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44194, value : 32'h20001880}, //phyinit_io_write: 0x44193, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44195, value : 32'h3bc1}, //phyinit_io_write: 0x44194, 0x20001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44196, value : 32'h24001880}, //phyinit_io_write: 0x44195, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44197, value : 32'h3bc1}, //phyinit_io_write: 0x44196, 0x24001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44198, value : 32'h28001880}, //phyinit_io_write: 0x44197, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44199, value : 32'h3bc1}, //phyinit_io_write: 0x44198, 0x28001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4419a, value : 32'h20200}, //phyinit_io_write: 0x44199, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4419b, value : 32'h400e}, //phyinit_io_write: 0x4419a, 0x20200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4419c, value : 32'h36940}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4419d, value : 32'h0}, //phyinit_io_write: 0x4419c, 0x36940
                          '{ step_type : REG_WRITE, reg_addr : 32'h4419e, value : 32'h40004600}, //phyinit_io_write: 0x4419d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4419f, value : 32'h0}, //phyinit_io_write: 0x4419e, 0x40004600
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a0, value : 32'h35540}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a1, value : 32'h0}, //phyinit_io_write: 0x441a0, 0x35540
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a2, value : 32'h4000900}, //phyinit_io_write: 0x441a1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a3, value : 32'h1a420}, //phyinit_io_write: 0x441a2, 0x4000900
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a4, value : 32'h4001000}, //phyinit_io_write: 0x441a3, 0x1a420
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a5, value : 32'h0}, //phyinit_io_write: 0x441a4, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a6, value : 32'h40004a00}, //phyinit_io_write: 0x441a5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a7, value : 32'h0}, //phyinit_io_write: 0x441a6, 0x40004a00
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a8, value : 32'hc0010e0}, //phyinit_io_write: 0x441a7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441a9, value : 32'h1800}, //phyinit_io_write: 0x441a8, 0xc0010e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441aa, value : 32'hc0000c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ab, value : 32'h1800}, //phyinit_io_write: 0x441aa, 0xc0000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ac, value : 32'h4000480}, //phyinit_io_write: 0x441ab, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ad, value : 32'h1800}, //phyinit_io_write: 0x441ac, 0x4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ae, value : 32'h4000800}, //phyinit_io_write: 0x441ad, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441af, value : 32'h0}, //phyinit_io_write: 0x441ae, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b0, value : 32'h8000480}, //phyinit_io_write: 0x441af, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b1, value : 32'h1800}, //phyinit_io_write: 0x441b0, 0x8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b2, value : 32'h4000800}, //phyinit_io_write: 0x441b1, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b3, value : 32'h0}, //phyinit_io_write: 0x441b2, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b4, value : 32'h1e0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b5, value : 32'h0}, //phyinit_io_write: 0x441b4, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b6, value : 32'h9c000cb1}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b7, value : 32'h1c01}, //phyinit_io_write: 0x441b6, 0x9c000cb1
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b8, value : 32'h9c0010b1}, //phyinit_io_write: 0x441b7, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h441b9, value : 32'h1c03}, //phyinit_io_write: 0x441b8, 0x9c0010b1
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ba, value : 32'h24000091}, //phyinit_io_write: 0x441b9, 0x1c03
                          '{ step_type : REG_WRITE, reg_addr : 32'h441bb, value : 32'h1c01}, //phyinit_io_write: 0x441ba, 0x24000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h441bc, value : 32'h51}, //phyinit_io_write: 0x441bb, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h441bd, value : 32'h4000}, //phyinit_io_write: 0x441bc, 0x51
                          '{ step_type : REG_WRITE, reg_addr : 32'h441be, value : 32'h39131}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h441bf, value : 32'h0}, //phyinit_io_write: 0x441be, 0x39131
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c0, value : 32'h40001a01}, //phyinit_io_write: 0x441bf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c1, value : 32'h0}, //phyinit_io_write: 0x441c0, 0x40001a01
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c2, value : 32'h39161}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c3, value : 32'h0}, //phyinit_io_write: 0x441c2, 0x39161
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c4, value : 32'h24000081}, //phyinit_io_write: 0x441c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c5, value : 32'h1c01}, //phyinit_io_write: 0x441c4, 0x24000081
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c6, value : 32'h41}, //phyinit_io_write: 0x441c5, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c7, value : 32'h4000}, //phyinit_io_write: 0x441c6, 0x41
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c8, value : 32'h1e0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h441c9, value : 32'h0}, //phyinit_io_write: 0x441c8, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ca, value : 32'h84000900}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h441cb, value : 32'h241c}, //phyinit_io_write: 0x441ca, 0x84000900
                          '{ step_type : REG_WRITE, reg_addr : 32'h441cc, value : 32'hc0014200}, //phyinit_io_write: 0x441cb, 0x241c
                          '{ step_type : REG_WRITE, reg_addr : 32'h441cd, value : 32'hc001}, //phyinit_io_write: 0x441cc, 0xc0014200
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ce, value : 32'h3a940}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h441cf, value : 32'h0}, //phyinit_io_write: 0x441ce, 0x3a940
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d0, value : 32'h4001000}, //phyinit_io_write: 0x441cf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d1, value : 32'h0}, //phyinit_io_write: 0x441d0, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d2, value : 32'h2c0008a0}, //phyinit_io_write: 0x441d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d3, value : 32'h802}, //phyinit_io_write: 0x441d2, 0x2c0008a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d4, value : 32'h1e0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d5, value : 32'h0}, //phyinit_io_write: 0x441d4, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d6, value : 32'h40000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d7, value : 32'h2c0c}, //phyinit_io_write: 0x441d6, 0x40000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d8, value : 32'h4000400}, //phyinit_io_write: 0x441d7, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h441d9, value : 32'h0}, //phyinit_io_write: 0x441d8, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h441da, value : 32'h4000080}, //phyinit_io_write: 0x441d9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441db, value : 32'h2c00}, //phyinit_io_write: 0x441da, 0x4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h441dc, value : 32'h4000400}, //phyinit_io_write: 0x441db, 0x2c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h441dd, value : 32'h0}, //phyinit_io_write: 0x441dc, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h441de, value : 32'h20200}, //phyinit_io_write: 0x441dd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441df, value : 32'h400e}, //phyinit_io_write: 0x441de, 0x20200
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e0, value : 32'h44140}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e1, value : 32'h0}, //phyinit_io_write: 0x441e0, 0x44140
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e2, value : 32'h40004600}, //phyinit_io_write: 0x441e1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e3, value : 32'h0}, //phyinit_io_write: 0x441e2, 0x40004600
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e4, value : 32'h40004c0}, //phyinit_io_write: 0x441e3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e5, value : 32'h1800}, //phyinit_io_write: 0x441e4, 0x40004c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e6, value : 32'h80004c0}, //phyinit_io_write: 0x441e5, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e7, value : 32'h1800}, //phyinit_io_write: 0x441e6, 0x80004c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e8, value : 32'h44140}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 22
                          '{ step_type : REG_WRITE, reg_addr : 32'h441e9, value : 32'h0}, //phyinit_io_write: 0x441e8, 0x44140
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ea, value : 32'h8000080}, //phyinit_io_write: 0x441e9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441eb, value : 32'h1800}, //phyinit_io_write: 0x441ea, 0x8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ec, value : 32'h4000400}, //phyinit_io_write: 0x441eb, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ed, value : 32'h0}, //phyinit_io_write: 0x441ec, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ee, value : 32'h4000080}, //phyinit_io_write: 0x441ed, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ef, value : 32'h1800}, //phyinit_io_write: 0x441ee, 0x4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f0, value : 32'h81}, //phyinit_io_write: 0x441ef, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f1, value : 32'h1800}, //phyinit_io_write: 0x441f0, 0x81
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f2, value : 32'h4000400}, //phyinit_io_write: 0x441f1, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f3, value : 32'h0}, //phyinit_io_write: 0x441f2, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f4, value : 32'h88000480}, //phyinit_io_write: 0x441f3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f5, value : 32'h802}, //phyinit_io_write: 0x441f4, 0x88000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f6, value : 32'h4000800}, //phyinit_io_write: 0x441f5, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f7, value : 32'h0}, //phyinit_io_write: 0x441f6, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f8, value : 32'hc000900}, //phyinit_io_write: 0x441f7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441f9, value : 32'h1800}, //phyinit_io_write: 0x441f8, 0xc000900
                          '{ step_type : REG_WRITE, reg_addr : 32'h441fa, value : 32'h4001000}, //phyinit_io_write: 0x441f9, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h441fb, value : 32'h0}, //phyinit_io_write: 0x441fa, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h441fc, value : 32'h10a00}, //phyinit_io_write: 0x441fb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h441fd, value : 32'h1}, //phyinit_io_write: 0x441fc, 0x10a00
                          '{ step_type : REG_WRITE, reg_addr : 32'h441fe, value : 32'h41d40}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 14
                          '{ step_type : REG_WRITE, reg_addr : 32'h441ff, value : 32'h0}, //phyinit_io_write: 0x441fe, 0x41d40
                          '{ step_type : REG_WRITE, reg_addr : 32'h44200, value : 32'hc000c80}, //phyinit_io_write: 0x441ff, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44201, value : 32'h1800}, //phyinit_io_write: 0x44200, 0xc000c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44202, value : 32'h20}, //phyinit_io_write: 0x44201, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44203, value : 32'h0}, //phyinit_io_write: 0x44202, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h44204, value : 32'h20}, //phyinit_io_write: 0x44203, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44205, value : 32'h0}, //phyinit_io_write: 0x44204, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h44206, value : 32'hc000880}, //phyinit_io_write: 0x44205, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44207, value : 32'h1800}, //phyinit_io_write: 0x44206, 0xc000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44208, value : 32'h20}, //phyinit_io_write: 0x44207, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44209, value : 32'h0}, //phyinit_io_write: 0x44208, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h4420a, value : 32'hc000080}, //phyinit_io_write: 0x44209, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4420b, value : 32'h1800}, //phyinit_io_write: 0x4420a, 0xc000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4420c, value : 32'h44520}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4420d, value : 32'h0}, //phyinit_io_write: 0x4420c, 0x44520
                          '{ step_type : REG_WRITE, reg_addr : 32'h4420e, value : 32'hc001c80}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 16
                          '{ step_type : REG_WRITE, reg_addr : 32'h4420f, value : 32'h1800}, //phyinit_io_write: 0x4420e, 0xc001c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44210, value : 32'h1020}, //phyinit_io_write: 0x4420f, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44211, value : 32'h0}, //phyinit_io_write: 0x44210, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h44212, value : 32'h1020}, //phyinit_io_write: 0x44211, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44213, value : 32'h0}, //phyinit_io_write: 0x44212, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h44214, value : 32'hc001880}, //phyinit_io_write: 0x44213, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44215, value : 32'h1800}, //phyinit_io_write: 0x44214, 0xc001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44216, value : 32'h1020}, //phyinit_io_write: 0x44215, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44217, value : 32'h0}, //phyinit_io_write: 0x44216, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h44218, value : 32'h1020}, //phyinit_io_write: 0x44217, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44219, value : 32'h0}, //phyinit_io_write: 0x44218, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h4421a, value : 32'h1020}, //phyinit_io_write: 0x44219, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4421b, value : 32'h0}, //phyinit_io_write: 0x4421a, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h4421c, value : 32'hc001080}, //phyinit_io_write: 0x4421b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4421d, value : 32'h1800}, //phyinit_io_write: 0x4421c, 0xc001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4421e, value : 32'h44520}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4421f, value : 32'h0}, //phyinit_io_write: 0x4421e, 0x44520
                          '{ step_type : REG_WRITE, reg_addr : 32'h44220, value : 32'h80}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44221, value : 32'h1800}, //phyinit_io_write: 0x44220, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44222, value : 32'h200600}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44223, value : 32'h20}, //phyinit_io_write: 0x44222, 0x200600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44224, value : 32'h49d60}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 40
                          '{ step_type : REG_WRITE, reg_addr : 32'h44225, value : 32'h0}, //phyinit_io_write: 0x44224, 0x49d60
                          '{ step_type : REG_WRITE, reg_addr : 32'h44226, value : 32'h18000080}, //phyinit_io_write: 0x44225, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44227, value : 32'h3bc1}, //phyinit_io_write: 0x44226, 0x18000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44228, value : 32'h1c000080}, //phyinit_io_write: 0x44227, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44229, value : 32'h3bc1}, //phyinit_io_write: 0x44228, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4422a, value : 32'h20000080}, //phyinit_io_write: 0x44229, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4422b, value : 32'h3bc1}, //phyinit_io_write: 0x4422a, 0x20000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4422c, value : 32'h24000080}, //phyinit_io_write: 0x4422b, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4422d, value : 32'h3bc1}, //phyinit_io_write: 0x4422c, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4422e, value : 32'h28000080}, //phyinit_io_write: 0x4422d, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4422f, value : 32'h3bc1}, //phyinit_io_write: 0x4422e, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44230, value : 32'h2c000880}, //phyinit_io_write: 0x4422f, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44231, value : 32'h3801}, //phyinit_io_write: 0x44230, 0x2c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44232, value : 32'h2c001080}, //phyinit_io_write: 0x44231, 0x3801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44233, value : 32'h3841}, //phyinit_io_write: 0x44232, 0x2c001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44234, value : 32'h2c000880}, //phyinit_io_write: 0x44233, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h44235, value : 32'h3881}, //phyinit_io_write: 0x44234, 0x2c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44236, value : 32'h2c001080}, //phyinit_io_write: 0x44235, 0x3881
                          '{ step_type : REG_WRITE, reg_addr : 32'h44237, value : 32'h38c1}, //phyinit_io_write: 0x44236, 0x2c001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44238, value : 32'h2c000880}, //phyinit_io_write: 0x44237, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44239, value : 32'h3901}, //phyinit_io_write: 0x44238, 0x2c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4423a, value : 32'h2c001080}, //phyinit_io_write: 0x44239, 0x3901
                          '{ step_type : REG_WRITE, reg_addr : 32'h4423b, value : 32'h3941}, //phyinit_io_write: 0x4423a, 0x2c001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4423c, value : 32'h2c000880}, //phyinit_io_write: 0x4423b, 0x3941
                          '{ step_type : REG_WRITE, reg_addr : 32'h4423d, value : 32'h3981}, //phyinit_io_write: 0x4423c, 0x2c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4423e, value : 32'h2c001080}, //phyinit_io_write: 0x4423d, 0x3981
                          '{ step_type : REG_WRITE, reg_addr : 32'h4423f, value : 32'h39c1}, //phyinit_io_write: 0x4423e, 0x2c001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44240, value : 32'h2000600}, //phyinit_io_write: 0x4423f, 0x39c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44241, value : 32'h200}, //phyinit_io_write: 0x44240, 0x2000600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44242, value : 32'h2c0010c0}, //phyinit_io_write: 0x44241, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h44243, value : 32'h3bc1}, //phyinit_io_write: 0x44242, 0x2c0010c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44244, value : 32'h58000080}, //phyinit_io_write: 0x44243, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44245, value : 32'h3cf}, //phyinit_io_write: 0x44244, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44246, value : 32'h5c000080}, //phyinit_io_write: 0x44245, 0x3cf
                          '{ step_type : REG_WRITE, reg_addr : 32'h44247, value : 32'h3cf}, //phyinit_io_write: 0x44246, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44248, value : 32'h5c000880}, //phyinit_io_write: 0x44247, 0x3cf
                          '{ step_type : REG_WRITE, reg_addr : 32'h44249, value : 32'hcf}, //phyinit_io_write: 0x44248, 0x5c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4424a, value : 32'h5c000880}, //phyinit_io_write: 0x44249, 0xcf
                          '{ step_type : REG_WRITE, reg_addr : 32'h4424b, value : 32'h28f}, //phyinit_io_write: 0x4424a, 0x5c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4424c, value : 32'h52920}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4424d, value : 32'h0}, //phyinit_io_write: 0x4424c, 0x52920
                          '{ step_type : REG_WRITE, reg_addr : 32'h4424e, value : 32'h18000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 70
                          '{ step_type : REG_WRITE, reg_addr : 32'h4424f, value : 32'h3801}, //phyinit_io_write: 0x4424e, 0x18000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44250, value : 32'h18000080}, //phyinit_io_write: 0x4424f, 0x3801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44251, value : 32'h3841}, //phyinit_io_write: 0x44250, 0x18000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44252, value : 32'h18000080}, //phyinit_io_write: 0x44251, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h44253, value : 32'h3881}, //phyinit_io_write: 0x44252, 0x18000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44254, value : 32'h18000080}, //phyinit_io_write: 0x44253, 0x3881
                          '{ step_type : REG_WRITE, reg_addr : 32'h44255, value : 32'h38c1}, //phyinit_io_write: 0x44254, 0x18000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44256, value : 32'h1c000080}, //phyinit_io_write: 0x44255, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44257, value : 32'h3801}, //phyinit_io_write: 0x44256, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44258, value : 32'h1c000080}, //phyinit_io_write: 0x44257, 0x3801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44259, value : 32'h3841}, //phyinit_io_write: 0x44258, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4425a, value : 32'h1c000080}, //phyinit_io_write: 0x44259, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h4425b, value : 32'h3881}, //phyinit_io_write: 0x4425a, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4425c, value : 32'h1c000080}, //phyinit_io_write: 0x4425b, 0x3881
                          '{ step_type : REG_WRITE, reg_addr : 32'h4425d, value : 32'h38c1}, //phyinit_io_write: 0x4425c, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4425e, value : 32'h20000080}, //phyinit_io_write: 0x4425d, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4425f, value : 32'h3801}, //phyinit_io_write: 0x4425e, 0x20000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44260, value : 32'h20000080}, //phyinit_io_write: 0x4425f, 0x3801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44261, value : 32'h3841}, //phyinit_io_write: 0x44260, 0x20000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44262, value : 32'h20000080}, //phyinit_io_write: 0x44261, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h44263, value : 32'h3881}, //phyinit_io_write: 0x44262, 0x20000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44264, value : 32'h20000080}, //phyinit_io_write: 0x44263, 0x3881
                          '{ step_type : REG_WRITE, reg_addr : 32'h44265, value : 32'h38c1}, //phyinit_io_write: 0x44264, 0x20000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44266, value : 32'h24000080}, //phyinit_io_write: 0x44265, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44267, value : 32'h3801}, //phyinit_io_write: 0x44266, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44268, value : 32'h24000080}, //phyinit_io_write: 0x44267, 0x3801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44269, value : 32'h3841}, //phyinit_io_write: 0x44268, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4426a, value : 32'h24000080}, //phyinit_io_write: 0x44269, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h4426b, value : 32'h3881}, //phyinit_io_write: 0x4426a, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4426c, value : 32'h24000080}, //phyinit_io_write: 0x4426b, 0x3881
                          '{ step_type : REG_WRITE, reg_addr : 32'h4426d, value : 32'h38c1}, //phyinit_io_write: 0x4426c, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4426e, value : 32'h28000080}, //phyinit_io_write: 0x4426d, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4426f, value : 32'h3841}, //phyinit_io_write: 0x4426e, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44270, value : 32'h28000080}, //phyinit_io_write: 0x4426f, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h44271, value : 32'h38c1}, //phyinit_io_write: 0x44270, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44272, value : 32'h2c000880}, //phyinit_io_write: 0x44271, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44273, value : 32'h3801}, //phyinit_io_write: 0x44272, 0x2c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44274, value : 32'h2c001080}, //phyinit_io_write: 0x44273, 0x3801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44275, value : 32'h3841}, //phyinit_io_write: 0x44274, 0x2c001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44276, value : 32'h2c000880}, //phyinit_io_write: 0x44275, 0x3841
                          '{ step_type : REG_WRITE, reg_addr : 32'h44277, value : 32'h3881}, //phyinit_io_write: 0x44276, 0x2c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44278, value : 32'h2c001080}, //phyinit_io_write: 0x44277, 0x3881
                          '{ step_type : REG_WRITE, reg_addr : 32'h44279, value : 32'h38c1}, //phyinit_io_write: 0x44278, 0x2c001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4427a, value : 32'h2000600}, //phyinit_io_write: 0x44279, 0x38c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4427b, value : 32'h200}, //phyinit_io_write: 0x4427a, 0x2000600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4427c, value : 32'h2c0010c0}, //phyinit_io_write: 0x4427b, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4427d, value : 32'h3bc1}, //phyinit_io_write: 0x4427c, 0x2c0010c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4427e, value : 32'h58000080}, //phyinit_io_write: 0x4427d, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4427f, value : 32'hf}, //phyinit_io_write: 0x4427e, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44280, value : 32'h5c000080}, //phyinit_io_write: 0x4427f, 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h44281, value : 32'hf}, //phyinit_io_write: 0x44280, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44282, value : 32'h58000080}, //phyinit_io_write: 0x44281, 0xf
                          '{ step_type : REG_WRITE, reg_addr : 32'h44283, value : 32'h4f}, //phyinit_io_write: 0x44282, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44284, value : 32'h5c000080}, //phyinit_io_write: 0x44283, 0x4f
                          '{ step_type : REG_WRITE, reg_addr : 32'h44285, value : 32'h4f}, //phyinit_io_write: 0x44284, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44286, value : 32'h58000080}, //phyinit_io_write: 0x44285, 0x4f
                          '{ step_type : REG_WRITE, reg_addr : 32'h44287, value : 32'h8f}, //phyinit_io_write: 0x44286, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44288, value : 32'h5c000080}, //phyinit_io_write: 0x44287, 0x8f
                          '{ step_type : REG_WRITE, reg_addr : 32'h44289, value : 32'h8f}, //phyinit_io_write: 0x44288, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4428a, value : 32'h58000080}, //phyinit_io_write: 0x44289, 0x8f
                          '{ step_type : REG_WRITE, reg_addr : 32'h4428b, value : 32'hcf}, //phyinit_io_write: 0x4428a, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4428c, value : 32'h58000080}, //phyinit_io_write: 0x4428b, 0xcf
                          '{ step_type : REG_WRITE, reg_addr : 32'h4428d, value : 32'h10f}, //phyinit_io_write: 0x4428c, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4428e, value : 32'h5c000080}, //phyinit_io_write: 0x4428d, 0x10f
                          '{ step_type : REG_WRITE, reg_addr : 32'h4428f, value : 32'h10f}, //phyinit_io_write: 0x4428e, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44290, value : 32'h58000080}, //phyinit_io_write: 0x4428f, 0x10f
                          '{ step_type : REG_WRITE, reg_addr : 32'h44291, value : 32'h14f}, //phyinit_io_write: 0x44290, 0x58000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44292, value : 32'h5c000080}, //phyinit_io_write: 0x44291, 0x14f
                          '{ step_type : REG_WRITE, reg_addr : 32'h44293, value : 32'h14f}, //phyinit_io_write: 0x44292, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44294, value : 32'h20000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44295, value : 32'h2bcc}, //phyinit_io_write: 0x44294, 0x20000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44296, value : 32'h53931}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44297, value : 32'h0}, //phyinit_io_write: 0x44296, 0x53931
                          '{ step_type : REG_WRITE, reg_addr : 32'h44298, value : 32'h40001a00}, //phyinit_io_write: 0x44297, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44299, value : 32'h0}, //phyinit_io_write: 0x44298, 0x40001a00
                          '{ step_type : REG_WRITE, reg_addr : 32'h4429a, value : 32'h53960}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4429b, value : 32'h0}, //phyinit_io_write: 0x4429a, 0x53960
                          '{ step_type : REG_WRITE, reg_addr : 32'h4429c, value : 32'h40030a0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 34
                          '{ step_type : REG_WRITE, reg_addr : 32'h4429d, value : 32'h2c00}, //phyinit_io_write: 0x4429c, 0x40030a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4429e, value : 32'h88000080}, //phyinit_io_write: 0x4429d, 0x2c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h4429f, value : 32'h802}, //phyinit_io_write: 0x4429e, 0x88000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a0, value : 32'h5c1ffc80}, //phyinit_io_write: 0x4429f, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a1, value : 32'h7c2}, //phyinit_io_write: 0x442a0, 0x5c1ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a2, value : 32'h800600}, //phyinit_io_write: 0x442a1, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a3, value : 32'h80}, //phyinit_io_write: 0x442a2, 0x800600
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a4, value : 32'hbc000900}, //phyinit_io_write: 0x442a3, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a5, value : 32'h16c0c}, //phyinit_io_write: 0x442a4, 0xbc000900
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a6, value : 32'h40000c0}, //phyinit_io_write: 0x442a5, 0x16c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a7, value : 32'h2424}, //phyinit_io_write: 0x442a6, 0x40000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a8, value : 32'h40080e0}, //phyinit_io_write: 0x442a7, 0x2424
                          '{ step_type : REG_WRITE, reg_addr : 32'h442a9, value : 32'h2424}, //phyinit_io_write: 0x442a8, 0x40080e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442aa, value : 32'h4000000}, //phyinit_io_write: 0x442a9, 0x2424
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ab, value : 32'h0}, //phyinit_io_write: 0x442aa, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ac, value : 32'h98001cb5}, //phyinit_io_write: 0x442ab, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ad, value : 32'h2c0c}, //phyinit_io_write: 0x442ac, 0x98001cb5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ae, value : 32'h9c0020b5}, //phyinit_io_write: 0x442ad, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442af, value : 32'h2c0c}, //phyinit_io_write: 0x442ae, 0x9c0020b5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b0, value : 32'h98000095}, //phyinit_io_write: 0x442af, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b1, value : 32'h2c0c}, //phyinit_io_write: 0x442b0, 0x98000095
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b2, value : 32'h9c000095}, //phyinit_io_write: 0x442b1, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b3, value : 32'h2c0c}, //phyinit_io_write: 0x442b2, 0x9c000095
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b4, value : 32'h40000095}, //phyinit_io_write: 0x442b3, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b5, value : 32'h2c0c}, //phyinit_io_write: 0x442b4, 0x40000095
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b6, value : 32'h605}, //phyinit_io_write: 0x442b5, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b7, value : 32'h2000}, //phyinit_io_write: 0x442b6, 0x605
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b8, value : 32'h400000c5}, //phyinit_io_write: 0x442b7, 0x2000
                          '{ step_type : REG_WRITE, reg_addr : 32'h442b9, value : 32'h2c0c}, //phyinit_io_write: 0x442b8, 0x400000c5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ba, value : 32'h800004c5}, //phyinit_io_write: 0x442b9, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442bb, value : 32'h2c0c}, //phyinit_io_write: 0x442ba, 0x800004c5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442bc, value : 32'h800000c5}, //phyinit_io_write: 0x442bb, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442bd, value : 32'h2c0c}, //phyinit_io_write: 0x442bc, 0x800000c5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442be, value : 32'h40000e5}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 18
                          '{ step_type : REG_WRITE, reg_addr : 32'h442bf, value : 32'h2c00}, //phyinit_io_write: 0x442be, 0x40000e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c0, value : 32'hbc0000e5}, //phyinit_io_write: 0x442bf, 0x2c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c1, value : 32'h16c0c}, //phyinit_io_write: 0x442c0, 0xbc0000e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c2, value : 32'h4000000}, //phyinit_io_write: 0x442c1, 0x16c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c3, value : 32'h0}, //phyinit_io_write: 0x442c2, 0x4000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c4, value : 32'h9bfe04e5}, //phyinit_io_write: 0x442c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c5, value : 32'h2c0c}, //phyinit_io_write: 0x442c4, 0x9bfe04e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c6, value : 32'h9ffe04e5}, //phyinit_io_write: 0x442c5, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c7, value : 32'h2c0c}, //phyinit_io_write: 0x442c6, 0x9ffe04e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c8, value : 32'h9bfe00e5}, //phyinit_io_write: 0x442c7, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442c9, value : 32'h2c0c}, //phyinit_io_write: 0x442c8, 0x9bfe00e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ca, value : 32'h9ffe00e5}, //phyinit_io_write: 0x442c9, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442cb, value : 32'h2c0c}, //phyinit_io_write: 0x442ca, 0x9ffe00e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442cc, value : 32'h400004e5}, //phyinit_io_write: 0x442cb, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442cd, value : 32'h2c0c}, //phyinit_io_write: 0x442cc, 0x400004e5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ce, value : 32'h4000400}, //phyinit_io_write: 0x442cd, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442cf, value : 32'h0}, //phyinit_io_write: 0x442ce, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d0, value : 32'hbc0008a5}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d1, value : 32'h16c0c}, //phyinit_io_write: 0x442d0, 0xbc0008a5
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d2, value : 32'h1e0}, //phyinit_io_write: 0x442d1, 0x16c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d3, value : 32'h0}, //phyinit_io_write: 0x442d2, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d4, value : 32'he8030c80}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d5, value : 32'h1c01}, //phyinit_io_write: 0x442d4, 0xe8030c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d6, value : 32'h4000400}, //phyinit_io_write: 0x442d5, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d7, value : 32'h0}, //phyinit_io_write: 0x442d6, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d8, value : 32'he8000080}, //phyinit_io_write: 0x442d7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442d9, value : 32'h1c01}, //phyinit_io_write: 0x442d8, 0xe8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442da, value : 32'h1e0}, //phyinit_io_write: 0x442d9, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h442db, value : 32'h0}, //phyinit_io_write: 0x442da, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442dc, value : 32'h88000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 40
                          '{ step_type : REG_WRITE, reg_addr : 32'h442dd, value : 32'h802}, //phyinit_io_write: 0x442dc, 0x88000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442de, value : 32'h4000c00}, //phyinit_io_write: 0x442dd, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h442df, value : 32'h0}, //phyinit_io_write: 0x442de, 0x4000c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e0, value : 32'hcc80}, //phyinit_io_write: 0x442df, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e1, value : 32'h808}, //phyinit_io_write: 0x442e0, 0xcc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e2, value : 32'h1c000480}, //phyinit_io_write: 0x442e1, 0x808
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e3, value : 32'hfc1}, //phyinit_io_write: 0x442e2, 0x1c000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e4, value : 32'h1c000080}, //phyinit_io_write: 0x442e3, 0xfc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e5, value : 32'hfc1}, //phyinit_io_write: 0x442e4, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e6, value : 32'h1c000480}, //phyinit_io_write: 0x442e5, 0xfc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e7, value : 32'h7c1}, //phyinit_io_write: 0x442e6, 0x1c000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e8, value : 32'h1c000080}, //phyinit_io_write: 0x442e7, 0x7c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h442e9, value : 32'h7c1}, //phyinit_io_write: 0x442e8, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ea, value : 32'h80}, //phyinit_io_write: 0x442e9, 0x7c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h442eb, value : 32'h808}, //phyinit_io_write: 0x442ea, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ec, value : 32'h50000080}, //phyinit_io_write: 0x442eb, 0x808
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ed, value : 32'h1c01}, //phyinit_io_write: 0x442ec, 0x50000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ee, value : 32'hb8000480}, //phyinit_io_write: 0x442ed, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ef, value : 32'h801}, //phyinit_io_write: 0x442ee, 0xb8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f0, value : 32'h4000400}, //phyinit_io_write: 0x442ef, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f1, value : 32'h0}, //phyinit_io_write: 0x442f0, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f2, value : 32'h40600}, //phyinit_io_write: 0x442f1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f3, value : 32'h4}, //phyinit_io_write: 0x442f2, 0x40600
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f4, value : 32'h598000e0}, //phyinit_io_write: 0x442f3, 0x4
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f5, value : 32'h7c0}, //phyinit_io_write: 0x442f4, 0x598000e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f6, value : 32'h28000480}, //phyinit_io_write: 0x442f5, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f7, value : 32'hfc0}, //phyinit_io_write: 0x442f6, 0x28000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f8, value : 32'h4001000}, //phyinit_io_write: 0x442f7, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442f9, value : 32'h0}, //phyinit_io_write: 0x442f8, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h442fa, value : 32'he0000080}, //phyinit_io_write: 0x442f9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442fb, value : 32'h803}, //phyinit_io_write: 0x442fa, 0xe0000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h442fc, value : 32'h4001400}, //phyinit_io_write: 0x442fb, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h442fd, value : 32'h0}, //phyinit_io_write: 0x442fc, 0x4001400
                          '{ step_type : REG_WRITE, reg_addr : 32'h442fe, value : 32'h88000880}, //phyinit_io_write: 0x442fd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h442ff, value : 32'h802}, //phyinit_io_write: 0x442fe, 0x88000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44300, value : 32'hc20}, //phyinit_io_write: 0x442ff, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h44301, value : 32'h0}, //phyinit_io_write: 0x44300, 0xc20
                          '{ step_type : REG_WRITE, reg_addr : 32'h44302, value : 32'h40004600}, //phyinit_io_write: 0x44301, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44303, value : 32'h0}, //phyinit_io_write: 0x44302, 0x40004600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44304, value : 32'h60d60}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44305, value : 32'h0}, //phyinit_io_write: 0x44304, 0x60d60
                          '{ step_type : REG_WRITE, reg_addr : 32'h44306, value : 32'h1c000880}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 12
                          '{ step_type : REG_WRITE, reg_addr : 32'h44307, value : 32'hfc1}, //phyinit_io_write: 0x44306, 0x1c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44308, value : 32'h1c000080}, //phyinit_io_write: 0x44307, 0xfc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44309, value : 32'hfc1}, //phyinit_io_write: 0x44308, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4430a, value : 32'h1c000880}, //phyinit_io_write: 0x44309, 0xfc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4430b, value : 32'h7c1}, //phyinit_io_write: 0x4430a, 0x1c000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4430c, value : 32'h1c000080}, //phyinit_io_write: 0x4430b, 0x7c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4430d, value : 32'h7c1}, //phyinit_io_write: 0x4430c, 0x1c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4430e, value : 32'h4003c00}, //phyinit_io_write: 0x4430d, 0x7c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4430f, value : 32'h0}, //phyinit_io_write: 0x4430e, 0x4003c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44310, value : 32'h40600}, //phyinit_io_write: 0x4430f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44311, value : 32'h4}, //phyinit_io_write: 0x44310, 0x40600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44312, value : 32'h62d40}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44313, value : 32'h0}, //phyinit_io_write: 0x44312, 0x62d40
                          '{ step_type : REG_WRITE, reg_addr : 32'h44314, value : 32'h1b9c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44315, value : 32'h0}, //phyinit_io_write: 0x44314, 0x1b9c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44316, value : 32'h28000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 14
                          '{ step_type : REG_WRITE, reg_addr : 32'h44317, value : 32'hfc0}, //phyinit_io_write: 0x44316, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44318, value : 32'h80000080}, //phyinit_io_write: 0x44317, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44319, value : 32'hfc2}, //phyinit_io_write: 0x44318, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4431a, value : 32'h98000080}, //phyinit_io_write: 0x44319, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4431b, value : 32'hfc2}, //phyinit_io_write: 0x4431a, 0x98000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4431c, value : 32'h24000080}, //phyinit_io_write: 0x4431b, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4431d, value : 32'h7c2}, //phyinit_io_write: 0x4431c, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4431e, value : 32'h28000080}, //phyinit_io_write: 0x4431d, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4431f, value : 32'h7c2}, //phyinit_io_write: 0x4431e, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44320, value : 32'h883c0080}, //phyinit_io_write: 0x4431f, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44321, value : 32'hfc2}, //phyinit_io_write: 0x44320, 0x883c0080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44322, value : 32'h80040200}, //phyinit_io_write: 0x44321, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44323, value : 32'h400f}, //phyinit_io_write: 0x44322, 0x80040200
                          '{ step_type : REG_WRITE, reg_addr : 32'h44324, value : 32'h66540}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44325, value : 32'h0}, //phyinit_io_write: 0x44324, 0x66540
                          '{ step_type : REG_WRITE, reg_addr : 32'h44326, value : 32'h80200}, //phyinit_io_write: 0x44325, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44327, value : 32'h400e}, //phyinit_io_write: 0x44326, 0x80200
                          '{ step_type : REG_WRITE, reg_addr : 32'h44328, value : 32'h66540}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h44329, value : 32'h0}, //phyinit_io_write: 0x44328, 0x66540
                          '{ step_type : REG_WRITE, reg_addr : 32'h4432a, value : 32'he4000480}, //phyinit_io_write: 0x44329, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4432b, value : 32'h801}, //phyinit_io_write: 0x4432a, 0xe4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4432c, value : 32'h4000800}, //phyinit_io_write: 0x4432b, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h4432d, value : 32'h0}, //phyinit_io_write: 0x4432c, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4432e, value : 32'he4000080}, //phyinit_io_write: 0x4432d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4432f, value : 32'h801}, //phyinit_io_write: 0x4432e, 0xe4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44330, value : 32'h4000800}, //phyinit_io_write: 0x4432f, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44331, value : 32'h0}, //phyinit_io_write: 0x44330, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44332, value : 32'he8030c81}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h44333, value : 32'h1c01}, //phyinit_io_write: 0x44332, 0xe8030c81
                          '{ step_type : REG_WRITE, reg_addr : 32'h44334, value : 32'h4000800}, //phyinit_io_write: 0x44333, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44335, value : 32'h0}, //phyinit_io_write: 0x44334, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44336, value : 32'he8000081}, //phyinit_io_write: 0x44335, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44337, value : 32'h1c01}, //phyinit_io_write: 0x44336, 0xe8000081
                          '{ step_type : REG_WRITE, reg_addr : 32'h44338, value : 32'h4000400}, //phyinit_io_write: 0x44337, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44339, value : 32'h0}, //phyinit_io_write: 0x44338, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4433a, value : 32'h40001a01}, //phyinit_io_write: 0x44339, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4433b, value : 32'h0}, //phyinit_io_write: 0x4433a, 0x40001a01
                          '{ step_type : REG_WRITE, reg_addr : 32'h4433c, value : 32'h69141}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4433d, value : 32'h0}, //phyinit_io_write: 0x4433c, 0x69141
                          '{ step_type : REG_WRITE, reg_addr : 32'h4433e, value : 32'ha0000481}, //phyinit_io_write: 0x4433d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4433f, value : 32'h2420}, //phyinit_io_write: 0x4433e, 0xa0000481
                          '{ step_type : REG_WRITE, reg_addr : 32'h44340, value : 32'h4000400}, //phyinit_io_write: 0x4433f, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44341, value : 32'h0}, //phyinit_io_write: 0x44340, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44342, value : 32'h40003201}, //phyinit_io_write: 0x44341, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44343, value : 32'h0}, //phyinit_io_write: 0x44342, 0x40003201
                          '{ step_type : REG_WRITE, reg_addr : 32'h44344, value : 32'h6b141}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44345, value : 32'h0}, //phyinit_io_write: 0x44344, 0x6b141
                          '{ step_type : REG_WRITE, reg_addr : 32'h44346, value : 32'h69161}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44347, value : 32'h0}, //phyinit_io_write: 0x44346, 0x69161
                          '{ step_type : REG_WRITE, reg_addr : 32'h44348, value : 32'h1c21}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 16
                          '{ step_type : REG_WRITE, reg_addr : 32'h44349, value : 32'h0}, //phyinit_io_write: 0x44348, 0x1c21
                          '{ step_type : REG_WRITE, reg_addr : 32'h4434a, value : 32'ha0000081}, //phyinit_io_write: 0x44349, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4434b, value : 32'h2420}, //phyinit_io_write: 0x4434a, 0xa0000081
                          '{ step_type : REG_WRITE, reg_addr : 32'h4434c, value : 32'h4000400}, //phyinit_io_write: 0x4434b, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h4434d, value : 32'h0}, //phyinit_io_write: 0x4434c, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4434e, value : 32'h20601}, //phyinit_io_write: 0x4434d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4434f, value : 32'h2}, //phyinit_io_write: 0x4434e, 0x20601
                          '{ step_type : REG_WRITE, reg_addr : 32'h44350, value : 32'he8030cc1}, //phyinit_io_write: 0x4434f, 0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44351, value : 32'h1c01}, //phyinit_io_write: 0x44350, 0xe8030cc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44352, value : 32'h4000800}, //phyinit_io_write: 0x44351, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44353, value : 32'h0}, //phyinit_io_write: 0x44352, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44354, value : 32'he80000c1}, //phyinit_io_write: 0x44353, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44355, value : 32'h1c01}, //phyinit_io_write: 0x44354, 0xe80000c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44356, value : 32'h4000400}, //phyinit_io_write: 0x44355, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44357, value : 32'h0}, //phyinit_io_write: 0x44356, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44358, value : 32'ha0000081}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 16
                          '{ step_type : REG_WRITE, reg_addr : 32'h44359, value : 32'h2420}, //phyinit_io_write: 0x44358, 0xa0000081
                          '{ step_type : REG_WRITE, reg_addr : 32'h4435a, value : 32'h4000400}, //phyinit_io_write: 0x44359, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h4435b, value : 32'h0}, //phyinit_io_write: 0x4435a, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4435c, value : 32'he8030c91}, //phyinit_io_write: 0x4435b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4435d, value : 32'h1c01}, //phyinit_io_write: 0x4435c, 0xe8030c91
                          '{ step_type : REG_WRITE, reg_addr : 32'h4435e, value : 32'h4000800}, //phyinit_io_write: 0x4435d, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h4435f, value : 32'h0}, //phyinit_io_write: 0x4435e, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44360, value : 32'he8000091}, //phyinit_io_write: 0x4435f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44361, value : 32'h1c01}, //phyinit_io_write: 0x44360, 0xe8000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h44362, value : 32'h4000400}, //phyinit_io_write: 0x44361, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44363, value : 32'h0}, //phyinit_io_write: 0x44362, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44364, value : 32'ha8000480}, //phyinit_io_write: 0x44363, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44365, value : 32'h1c04}, //phyinit_io_write: 0x44364, 0xa8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44366, value : 32'h4000400}, //phyinit_io_write: 0x44365, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44367, value : 32'h0}, //phyinit_io_write: 0x44366, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44368, value : 32'h18000081}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44369, value : 32'h1e420}, //phyinit_io_write: 0x44368, 0x18000081
                          '{ step_type : REG_WRITE, reg_addr : 32'h4436a, value : 32'h40006611}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4436b, value : 32'h0}, //phyinit_io_write: 0x4436a, 0x40006611
                          '{ step_type : REG_WRITE, reg_addr : 32'h4436c, value : 32'h6e151}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4436d, value : 32'h0}, //phyinit_io_write: 0x4436c, 0x6e151
                          '{ step_type : REG_WRITE, reg_addr : 32'h4436e, value : 32'h21d1}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4436f, value : 32'h0}, //phyinit_io_write: 0x4436e, 0x21d1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44370, value : 32'ha0000491}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 12
                          '{ step_type : REG_WRITE, reg_addr : 32'h44371, value : 32'h2420}, //phyinit_io_write: 0x44370, 0xa0000491
                          '{ step_type : REG_WRITE, reg_addr : 32'h44372, value : 32'h4000400}, //phyinit_io_write: 0x44371, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h44373, value : 32'h0}, //phyinit_io_write: 0x44372, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44374, value : 32'h540020b1}, //phyinit_io_write: 0x44373, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44375, value : 32'h14fc0}, //phyinit_io_write: 0x44374, 0x540020b1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44376, value : 32'hf00024b1}, //phyinit_io_write: 0x44375, 0x14fc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44377, value : 32'h147c1}, //phyinit_io_write: 0x44376, 0xf00024b1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44378, value : 32'ha0000091}, //phyinit_io_write: 0x44377, 0x147c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44379, value : 32'h2420}, //phyinit_io_write: 0x44378, 0xa0000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h4437a, value : 32'h1e0}, //phyinit_io_write: 0x44379, 0x2420
                          '{ step_type : REG_WRITE, reg_addr : 32'h4437b, value : 32'h0}, //phyinit_io_write: 0x4437a, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4437c, value : 32'ha8000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 30
                          '{ step_type : REG_WRITE, reg_addr : 32'h4437d, value : 32'h1c06}, //phyinit_io_write: 0x4437c, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4437e, value : 32'h80013080}, //phyinit_io_write: 0x4437d, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h4437f, value : 32'h1c04}, //phyinit_io_write: 0x4437e, 0x80013080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44380, value : 32'h4000400}, //phyinit_io_write: 0x4437f, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44381, value : 32'h0}, //phyinit_io_write: 0x44380, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44382, value : 32'h80013480}, //phyinit_io_write: 0x44381, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44383, value : 32'h1c04}, //phyinit_io_write: 0x44382, 0x80013480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44384, value : 32'h4000800}, //phyinit_io_write: 0x44383, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44385, value : 32'h0}, //phyinit_io_write: 0x44384, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44386, value : 32'h4001c00}, //phyinit_io_write: 0x44385, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44387, value : 32'h0}, //phyinit_io_write: 0x44386, 0x4001c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44388, value : 32'h80000080}, //phyinit_io_write: 0x44387, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44389, value : 32'h1c04}, //phyinit_io_write: 0x44388, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4438a, value : 32'h420}, //phyinit_io_write: 0x44389, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4438b, value : 32'h0}, //phyinit_io_write: 0x4438a, 0x420
                          '{ step_type : REG_WRITE, reg_addr : 32'h4438c, value : 32'ha8000080}, //phyinit_io_write: 0x4438b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4438d, value : 32'h1c06}, //phyinit_io_write: 0x4438c, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4438e, value : 32'h80013880}, //phyinit_io_write: 0x4438d, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h4438f, value : 32'h1c04}, //phyinit_io_write: 0x4438e, 0x80013880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44390, value : 32'h4000400}, //phyinit_io_write: 0x4438f, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44391, value : 32'h0}, //phyinit_io_write: 0x44390, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44392, value : 32'h80013c80}, //phyinit_io_write: 0x44391, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44393, value : 32'h1c04}, //phyinit_io_write: 0x44392, 0x80013c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44394, value : 32'h4000800}, //phyinit_io_write: 0x44393, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44395, value : 32'h0}, //phyinit_io_write: 0x44394, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44396, value : 32'h4001c00}, //phyinit_io_write: 0x44395, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44397, value : 32'h0}, //phyinit_io_write: 0x44396, 0x4001c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44398, value : 32'h80000080}, //phyinit_io_write: 0x44397, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44399, value : 32'h1c04}, //phyinit_io_write: 0x44398, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4439a, value : 32'h1e0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4439b, value : 32'h0}, //phyinit_io_write: 0x4439a, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4439c, value : 32'h20000086}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 176
                          '{ step_type : REG_WRITE, reg_addr : 32'h4439d, value : 32'h1c7c4}, //phyinit_io_write: 0x4439c, 0x20000086
                          '{ step_type : REG_WRITE, reg_addr : 32'h4439e, value : 32'h9e000480}, //phyinit_io_write: 0x4439d, 0x1c7c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4439f, value : 32'h7c2}, //phyinit_io_write: 0x4439e, 0x9e000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a0, value : 32'hc4060080}, //phyinit_io_write: 0x4439f, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a1, value : 32'h7c2}, //phyinit_io_write: 0x443a0, 0xc4060080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a2, value : 32'hd4000480}, //phyinit_io_write: 0x443a1, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a3, value : 32'h7c2}, //phyinit_io_write: 0x443a2, 0xd4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a4, value : 32'he4000480}, //phyinit_io_write: 0x443a3, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a5, value : 32'h7c2}, //phyinit_io_write: 0x443a4, 0xe4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a6, value : 32'h9c003080}, //phyinit_io_write: 0x443a5, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a7, value : 32'h1c04}, //phyinit_io_write: 0x443a6, 0x9c003080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a8, value : 32'h7c000080}, //phyinit_io_write: 0x443a7, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443a9, value : 32'h1c7c1}, //phyinit_io_write: 0x443a8, 0x7c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443aa, value : 32'h88000c80}, //phyinit_io_write: 0x443a9, 0x1c7c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ab, value : 32'h7c2}, //phyinit_io_write: 0x443aa, 0x88000c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ac, value : 32'h64000c80}, //phyinit_io_write: 0x443ab, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ad, value : 32'h801}, //phyinit_io_write: 0x443ac, 0x64000c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ae, value : 32'h90000880}, //phyinit_io_write: 0x443ad, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h443af, value : 32'h7c2}, //phyinit_io_write: 0x443ae, 0x90000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b0, value : 32'hec0ffc80}, //phyinit_io_write: 0x443af, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b1, value : 32'h7c2}, //phyinit_io_write: 0x443b0, 0xec0ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b2, value : 32'hec000080}, //phyinit_io_write: 0x443b1, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b3, value : 32'h7c2}, //phyinit_io_write: 0x443b2, 0xec000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b4, value : 32'hf8000080}, //phyinit_io_write: 0x443b3, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b5, value : 32'h7fe}, //phyinit_io_write: 0x443b4, 0xf8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b6, value : 32'hf8000480}, //phyinit_io_write: 0x443b5, 0x7fe
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b7, value : 32'h7c2}, //phyinit_io_write: 0x443b6, 0xf8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b8, value : 32'hf8000480}, //phyinit_io_write: 0x443b7, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443b9, value : 32'h7d2}, //phyinit_io_write: 0x443b8, 0xf8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ba, value : 32'ha8001080}, //phyinit_io_write: 0x443b9, 0x7d2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443bb, value : 32'h1c06}, //phyinit_io_write: 0x443ba, 0xa8001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443bc, value : 32'h80014880}, //phyinit_io_write: 0x443bb, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h443bd, value : 32'h1c04}, //phyinit_io_write: 0x443bc, 0x80014880
                          '{ step_type : REG_WRITE, reg_addr : 32'h443be, value : 32'h4000400}, //phyinit_io_write: 0x443bd, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443bf, value : 32'h0}, //phyinit_io_write: 0x443be, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c0, value : 32'h80014c80}, //phyinit_io_write: 0x443bf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c1, value : 32'h1c04}, //phyinit_io_write: 0x443c0, 0x80014c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c2, value : 32'h4000800}, //phyinit_io_write: 0x443c1, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c3, value : 32'h0}, //phyinit_io_write: 0x443c2, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c4, value : 32'h840}, //phyinit_io_write: 0x443c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c5, value : 32'h6000}, //phyinit_io_write: 0x443c4, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c6, value : 32'h80000080}, //phyinit_io_write: 0x443c5, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c7, value : 32'h1c04}, //phyinit_io_write: 0x443c6, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c8, value : 32'hf8000080}, //phyinit_io_write: 0x443c7, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443c9, value : 32'h7c2}, //phyinit_io_write: 0x443c8, 0xf8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ca, value : 32'hf8000080}, //phyinit_io_write: 0x443c9, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443cb, value : 32'h7d2}, //phyinit_io_write: 0x443ca, 0xf8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443cc, value : 32'hec0ffc80}, //phyinit_io_write: 0x443cb, 0x7d2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443cd, value : 32'h7c2}, //phyinit_io_write: 0x443cc, 0xec0ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ce, value : 32'hec000080}, //phyinit_io_write: 0x443cd, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443cf, value : 32'h7c2}, //phyinit_io_write: 0x443ce, 0xec000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d0, value : 32'hf8000480}, //phyinit_io_write: 0x443cf, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d1, value : 32'h7c6}, //phyinit_io_write: 0x443d0, 0xf8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d2, value : 32'hf8000480}, //phyinit_io_write: 0x443d1, 0x7c6
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d3, value : 32'h7d6}, //phyinit_io_write: 0x443d2, 0xf8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d4, value : 32'ha8001080}, //phyinit_io_write: 0x443d3, 0x7d6
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d5, value : 32'h1c06}, //phyinit_io_write: 0x443d4, 0xa8001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d6, value : 32'h80015080}, //phyinit_io_write: 0x443d5, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d7, value : 32'h1c04}, //phyinit_io_write: 0x443d6, 0x80015080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d8, value : 32'h4000400}, //phyinit_io_write: 0x443d7, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443d9, value : 32'h0}, //phyinit_io_write: 0x443d8, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h443da, value : 32'h80015480}, //phyinit_io_write: 0x443d9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443db, value : 32'h1c04}, //phyinit_io_write: 0x443da, 0x80015480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443dc, value : 32'h4000800}, //phyinit_io_write: 0x443db, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443dd, value : 32'h0}, //phyinit_io_write: 0x443dc, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h443de, value : 32'h840}, //phyinit_io_write: 0x443dd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443df, value : 32'h6000}, //phyinit_io_write: 0x443de, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e0, value : 32'h80000080}, //phyinit_io_write: 0x443df, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e1, value : 32'h1c04}, //phyinit_io_write: 0x443e0, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e2, value : 32'hf8000080}, //phyinit_io_write: 0x443e1, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e3, value : 32'h7c6}, //phyinit_io_write: 0x443e2, 0xf8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e4, value : 32'hf8000080}, //phyinit_io_write: 0x443e3, 0x7c6
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e5, value : 32'h7d6}, //phyinit_io_write: 0x443e4, 0xf8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e6, value : 32'h64000880}, //phyinit_io_write: 0x443e5, 0x7d6
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e7, value : 32'h801}, //phyinit_io_write: 0x443e6, 0x64000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e8, value : 32'h1420}, //phyinit_io_write: 0x443e7, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h443e9, value : 32'h0}, //phyinit_io_write: 0x443e8, 0x1420
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ea, value : 32'hc4000480}, //phyinit_io_write: 0x443e9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443eb, value : 32'h7c0}, //phyinit_io_write: 0x443ea, 0xc4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ec, value : 32'h4001000}, //phyinit_io_write: 0x443eb, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ed, value : 32'h0}, //phyinit_io_write: 0x443ec, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ee, value : 32'hc4000080}, //phyinit_io_write: 0x443ed, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ef, value : 32'h7c0}, //phyinit_io_write: 0x443ee, 0xc4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f0, value : 32'h4000600}, //phyinit_io_write: 0x443ef, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f1, value : 32'h400}, //phyinit_io_write: 0x443f0, 0x4000600
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f2, value : 32'h24c8c8c0}, //phyinit_io_write: 0x443f1, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f3, value : 32'h147c8}, //phyinit_io_write: 0x443f2, 0x24c8c8c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f4, value : 32'h80000480}, //phyinit_io_write: 0x443f3, 0x147c8
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f5, value : 32'h802}, //phyinit_io_write: 0x443f4, 0x80000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f6, value : 32'h4000400}, //phyinit_io_write: 0x443f5, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f7, value : 32'h0}, //phyinit_io_write: 0x443f6, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f8, value : 32'h80000080}, //phyinit_io_write: 0x443f7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h443f9, value : 32'h802}, //phyinit_io_write: 0x443f8, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443fa, value : 32'h90000080}, //phyinit_io_write: 0x443f9, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h443fb, value : 32'h7c2}, //phyinit_io_write: 0x443fa, 0x90000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h443fc, value : 32'h98000c80}, //phyinit_io_write: 0x443fb, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443fd, value : 32'h7c2}, //phyinit_io_write: 0x443fc, 0x98000c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h443fe, value : 32'ha8001080}, //phyinit_io_write: 0x443fd, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h443ff, value : 32'h1c06}, //phyinit_io_write: 0x443fe, 0xa8001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44400, value : 32'h80015880}, //phyinit_io_write: 0x443ff, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44401, value : 32'h1c04}, //phyinit_io_write: 0x44400, 0x80015880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44402, value : 32'h4000400}, //phyinit_io_write: 0x44401, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44403, value : 32'h0}, //phyinit_io_write: 0x44402, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44404, value : 32'h80015c80}, //phyinit_io_write: 0x44403, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44405, value : 32'h1c04}, //phyinit_io_write: 0x44404, 0x80015c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44406, value : 32'h4000800}, //phyinit_io_write: 0x44405, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44407, value : 32'h0}, //phyinit_io_write: 0x44406, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44408, value : 32'h840}, //phyinit_io_write: 0x44407, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44409, value : 32'h6000}, //phyinit_io_write: 0x44408, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h4440a, value : 32'h80000080}, //phyinit_io_write: 0x44409, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4440b, value : 32'h1c04}, //phyinit_io_write: 0x4440a, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4440c, value : 32'h4000800}, //phyinit_io_write: 0x4440b, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4440d, value : 32'h0}, //phyinit_io_write: 0x4440c, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4440e, value : 32'h98000080}, //phyinit_io_write: 0x4440d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4440f, value : 32'h7c2}, //phyinit_io_write: 0x4440e, 0x98000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44410, value : 32'h88000080}, //phyinit_io_write: 0x4440f, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44411, value : 32'h7c2}, //phyinit_io_write: 0x44410, 0x88000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44412, value : 32'h64000080}, //phyinit_io_write: 0x44411, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44413, value : 32'h801}, //phyinit_io_write: 0x44412, 0x64000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44414, value : 32'h7c000480}, //phyinit_io_write: 0x44413, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44415, value : 32'h1c7c1}, //phyinit_io_write: 0x44414, 0x7c000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44416, value : 32'he4000480}, //phyinit_io_write: 0x44415, 0x1c7c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h44417, value : 32'h801}, //phyinit_io_write: 0x44416, 0xe4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44418, value : 32'h4000800}, //phyinit_io_write: 0x44417, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44419, value : 32'h0}, //phyinit_io_write: 0x44418, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4441a, value : 32'he4000080}, //phyinit_io_write: 0x44419, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4441b, value : 32'h801}, //phyinit_io_write: 0x4441a, 0xe4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4441c, value : 32'h4000800}, //phyinit_io_write: 0x4441b, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h4441d, value : 32'h0}, //phyinit_io_write: 0x4441c, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4441e, value : 32'h1820}, //phyinit_io_write: 0x4441d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4441f, value : 32'h0}, //phyinit_io_write: 0x4441e, 0x1820
                          '{ step_type : REG_WRITE, reg_addr : 32'h44420, value : 32'h90000480}, //phyinit_io_write: 0x4441f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44421, value : 32'h7c2}, //phyinit_io_write: 0x44420, 0x90000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44422, value : 32'ha8001080}, //phyinit_io_write: 0x44421, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44423, value : 32'h1c06}, //phyinit_io_write: 0x44422, 0xa8001080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44424, value : 32'h80016080}, //phyinit_io_write: 0x44423, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h44425, value : 32'h1c04}, //phyinit_io_write: 0x44424, 0x80016080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44426, value : 32'h4000400}, //phyinit_io_write: 0x44425, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44427, value : 32'h0}, //phyinit_io_write: 0x44426, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44428, value : 32'h80016480}, //phyinit_io_write: 0x44427, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44429, value : 32'h1c04}, //phyinit_io_write: 0x44428, 0x80016480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4442a, value : 32'h4000800}, //phyinit_io_write: 0x44429, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4442b, value : 32'h0}, //phyinit_io_write: 0x4442a, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4442c, value : 32'h840}, //phyinit_io_write: 0x4442b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4442d, value : 32'h6000}, //phyinit_io_write: 0x4442c, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h4442e, value : 32'h80000080}, //phyinit_io_write: 0x4442d, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4442f, value : 32'h1c04}, //phyinit_io_write: 0x4442e, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44430, value : 32'h4000800}, //phyinit_io_write: 0x4442f, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44431, value : 32'h0}, //phyinit_io_write: 0x44430, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44432, value : 32'h80000480}, //phyinit_io_write: 0x44431, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44433, value : 32'h802}, //phyinit_io_write: 0x44432, 0x80000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44434, value : 32'h4000400}, //phyinit_io_write: 0x44433, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h44435, value : 32'h0}, //phyinit_io_write: 0x44434, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44436, value : 32'h80000080}, //phyinit_io_write: 0x44435, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44437, value : 32'h802}, //phyinit_io_write: 0x44436, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44438, value : 32'h90000080}, //phyinit_io_write: 0x44437, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h44439, value : 32'h7c2}, //phyinit_io_write: 0x44438, 0x90000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4443a, value : 32'h4000800}, //phyinit_io_write: 0x44439, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4443b, value : 32'h0}, //phyinit_io_write: 0x4443a, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4443c, value : 32'he4000480}, //phyinit_io_write: 0x4443b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4443d, value : 32'h801}, //phyinit_io_write: 0x4443c, 0xe4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4443e, value : 32'h4000800}, //phyinit_io_write: 0x4443d, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h4443f, value : 32'h0}, //phyinit_io_write: 0x4443e, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44440, value : 32'he4000080}, //phyinit_io_write: 0x4443f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44441, value : 32'h801}, //phyinit_io_write: 0x44440, 0xe4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44442, value : 32'h4000800}, //phyinit_io_write: 0x44441, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44443, value : 32'h0}, //phyinit_io_write: 0x44442, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44444, value : 32'ha8000080}, //phyinit_io_write: 0x44443, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44445, value : 32'h1c04}, //phyinit_io_write: 0x44444, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44446, value : 32'h50000480}, //phyinit_io_write: 0x44445, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44447, value : 32'h1c01}, //phyinit_io_write: 0x44446, 0x50000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44448, value : 32'h20000486}, //phyinit_io_write: 0x44447, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44449, value : 32'h1c7c4}, //phyinit_io_write: 0x44448, 0x20000486
                          '{ step_type : REG_WRITE, reg_addr : 32'h4444a, value : 32'h1e0}, //phyinit_io_write: 0x44449, 0x1c7c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4444b, value : 32'h0}, //phyinit_io_write: 0x4444a, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4444c, value : 32'h80008600}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4444d, value : 32'h0}, //phyinit_io_write: 0x4444c, 0x80008600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4444e, value : 32'h8c160}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 18
                          '{ step_type : REG_WRITE, reg_addr : 32'h4444f, value : 32'h0}, //phyinit_io_write: 0x4444e, 0x8c160
                          '{ step_type : REG_WRITE, reg_addr : 32'h44450, value : 32'h80000480}, //phyinit_io_write: 0x4444f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44451, value : 32'h802}, //phyinit_io_write: 0x44450, 0x80000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44452, value : 32'h4000400}, //phyinit_io_write: 0x44451, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h44453, value : 32'h0}, //phyinit_io_write: 0x44452, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44454, value : 32'h80000080}, //phyinit_io_write: 0x44453, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44455, value : 32'h802}, //phyinit_io_write: 0x44454, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44456, value : 32'h4000400}, //phyinit_io_write: 0x44455, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h44457, value : 32'h0}, //phyinit_io_write: 0x44456, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44458, value : 32'he4000480}, //phyinit_io_write: 0x44457, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44459, value : 32'h801}, //phyinit_io_write: 0x44458, 0xe4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4445a, value : 32'h4000800}, //phyinit_io_write: 0x44459, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h4445b, value : 32'h0}, //phyinit_io_write: 0x4445a, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4445c, value : 32'he4000080}, //phyinit_io_write: 0x4445b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4445d, value : 32'h801}, //phyinit_io_write: 0x4445c, 0xe4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4445e, value : 32'ha8000080}, //phyinit_io_write: 0x4445d, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h4445f, value : 32'h1c04}, //phyinit_io_write: 0x4445e, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44460, value : 32'hb8000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 12
                          '{ step_type : REG_WRITE, reg_addr : 32'h44461, value : 32'h801}, //phyinit_io_write: 0x44460, 0xb8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44462, value : 32'h4000800}, //phyinit_io_write: 0x44461, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44463, value : 32'h0}, //phyinit_io_write: 0x44462, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44464, value : 32'h1080}, //phyinit_io_write: 0x44463, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44465, value : 32'h33c2}, //phyinit_io_write: 0x44464, 0x1080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44466, value : 32'h50000480}, //phyinit_io_write: 0x44465, 0x33c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44467, value : 32'h1c01}, //phyinit_io_write: 0x44466, 0x50000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44468, value : 32'hb4000080}, //phyinit_io_write: 0x44467, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44469, value : 32'h2400}, //phyinit_io_write: 0x44468, 0xb4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4446a, value : 32'h88000481}, //phyinit_io_write: 0x44469, 0x2400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4446b, value : 32'hc00}, //phyinit_io_write: 0x4446a, 0x88000481
                          '{ step_type : REG_WRITE, reg_addr : 32'h4446c, value : 32'h24000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4446d, value : 32'h1c01}, //phyinit_io_write: 0x4446c, 0x24000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4446e, value : 32'h1e0}, //phyinit_io_write: 0x4446d, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h4446f, value : 32'h0}, //phyinit_io_write: 0x4446e, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44470, value : 32'h40000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 84
                          '{ step_type : REG_WRITE, reg_addr : 32'h44471, value : 32'h2c0c}, //phyinit_io_write: 0x44470, 0x40000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44472, value : 32'h2c000080}, //phyinit_io_write: 0x44471, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44473, value : 32'h7c2}, //phyinit_io_write: 0x44472, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44474, value : 32'h8c000080}, //phyinit_io_write: 0x44473, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44475, value : 32'hfc2}, //phyinit_io_write: 0x44474, 0x8c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44476, value : 32'h200600}, //phyinit_io_write: 0x44475, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44477, value : 32'h20}, //phyinit_io_write: 0x44476, 0x200600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44478, value : 32'h880c0080}, //phyinit_io_write: 0x44477, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h44479, value : 32'hc02}, //phyinit_io_write: 0x44478, 0x880c0080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4447a, value : 32'h880c00c0}, //phyinit_io_write: 0x44479, 0xc02
                          '{ step_type : REG_WRITE, reg_addr : 32'h4447b, value : 32'hc42}, //phyinit_io_write: 0x4447a, 0x880c00c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4447c, value : 32'h247ffc80}, //phyinit_io_write: 0x4447b, 0xc42
                          '{ step_type : REG_WRITE, reg_addr : 32'h4447d, value : 32'h7c2}, //phyinit_io_write: 0x4447c, 0x247ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h4447e, value : 32'h281ffc80}, //phyinit_io_write: 0x4447d, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4447f, value : 32'h7c2}, //phyinit_io_write: 0x4447e, 0x281ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44480, value : 32'h4000400}, //phyinit_io_write: 0x4447f, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44481, value : 32'h0}, //phyinit_io_write: 0x44480, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44482, value : 32'h98000480}, //phyinit_io_write: 0x44481, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44483, value : 32'hfc2}, //phyinit_io_write: 0x44482, 0x98000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44484, value : 32'h28000480}, //phyinit_io_write: 0x44483, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44485, value : 32'hfc0}, //phyinit_io_write: 0x44484, 0x28000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44486, value : 32'h4001000}, //phyinit_io_write: 0x44485, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44487, value : 32'h0}, //phyinit_io_write: 0x44486, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44488, value : 32'h80fffc80}, //phyinit_io_write: 0x44487, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44489, value : 32'hfc2}, //phyinit_io_write: 0x44488, 0x80fffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h4448a, value : 32'h4000400}, //phyinit_io_write: 0x44489, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4448b, value : 32'h0}, //phyinit_io_write: 0x4448a, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h4448c, value : 32'he0000480}, //phyinit_io_write: 0x4448b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4448d, value : 32'h803}, //phyinit_io_write: 0x4448c, 0xe0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h4448e, value : 32'h4002000}, //phyinit_io_write: 0x4448d, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h4448f, value : 32'h0}, //phyinit_io_write: 0x4448e, 0x4002000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44490, value : 32'h28000080}, //phyinit_io_write: 0x4448f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44491, value : 32'hfc0}, //phyinit_io_write: 0x44490, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44492, value : 32'h50000080}, //phyinit_io_write: 0x44491, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44493, value : 32'h1c01}, //phyinit_io_write: 0x44492, 0x50000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44494, value : 32'h480}, //phyinit_io_write: 0x44493, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44495, value : 32'h1800}, //phyinit_io_write: 0x44494, 0x480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44496, value : 32'hc000080}, //phyinit_io_write: 0x44495, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44497, value : 32'h1800}, //phyinit_io_write: 0x44496, 0xc000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44498, value : 32'h5c000080}, //phyinit_io_write: 0x44497, 0x1800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44499, value : 32'h7c2}, //phyinit_io_write: 0x44498, 0x5c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4449a, value : 32'h4000080}, //phyinit_io_write: 0x44499, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4449b, value : 32'h2c00}, //phyinit_io_write: 0x4449a, 0x4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4449c, value : 32'h2000600}, //phyinit_io_write: 0x4449b, 0x2c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h4449d, value : 32'h200}, //phyinit_io_write: 0x4449c, 0x2000600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4449e, value : 32'h2c0010c0}, //phyinit_io_write: 0x4449d, 0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4449f, value : 32'h3bc1}, //phyinit_io_write: 0x4449e, 0x2c0010c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a0, value : 32'h2c001880}, //phyinit_io_write: 0x4449f, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a1, value : 32'h3bc1}, //phyinit_io_write: 0x444a0, 0x2c001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a2, value : 32'h18001880}, //phyinit_io_write: 0x444a1, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a3, value : 32'h3bc1}, //phyinit_io_write: 0x444a2, 0x18001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a4, value : 32'h1c001880}, //phyinit_io_write: 0x444a3, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a5, value : 32'h3bc1}, //phyinit_io_write: 0x444a4, 0x1c001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a6, value : 32'h20001880}, //phyinit_io_write: 0x444a5, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a7, value : 32'h3bc1}, //phyinit_io_write: 0x444a6, 0x20001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a8, value : 32'h24001880}, //phyinit_io_write: 0x444a7, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444a9, value : 32'h3bc1}, //phyinit_io_write: 0x444a8, 0x24001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444aa, value : 32'h28001880}, //phyinit_io_write: 0x444a9, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ab, value : 32'h3bc1}, //phyinit_io_write: 0x444aa, 0x28001880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ac, value : 32'h20000880}, //phyinit_io_write: 0x444ab, 0x3bc1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ad, value : 32'h2bcc}, //phyinit_io_write: 0x444ac, 0x20000880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ae, value : 32'h40030a0}, //phyinit_io_write: 0x444ad, 0x2bcc
                          '{ step_type : REG_WRITE, reg_addr : 32'h444af, value : 32'h2c00}, //phyinit_io_write: 0x444ae, 0x40030a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b0, value : 32'h24000080}, //phyinit_io_write: 0x444af, 0x2c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b1, value : 32'h1c01}, //phyinit_io_write: 0x444b0, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b2, value : 32'hb4000480}, //phyinit_io_write: 0x444b1, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b3, value : 32'h2400}, //phyinit_io_write: 0x444b2, 0xb4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b4, value : 32'h40}, //phyinit_io_write: 0x444b3, 0x2400
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b5, value : 32'h4000}, //phyinit_io_write: 0x444b4, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b6, value : 32'h20}, //phyinit_io_write: 0x444b5, 0x4000
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b7, value : 32'h0}, //phyinit_io_write: 0x444b6, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b8, value : 32'h20}, //phyinit_io_write: 0x444b7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444b9, value : 32'h0}, //phyinit_io_write: 0x444b8, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ba, value : 32'h88000c80}, //phyinit_io_write: 0x444b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444bb, value : 32'hc00}, //phyinit_io_write: 0x444ba, 0x88000c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h444bc, value : 32'h80000080}, //phyinit_io_write: 0x444bb, 0xc00
                          '{ step_type : REG_WRITE, reg_addr : 32'h444bd, value : 32'hfc0}, //phyinit_io_write: 0x444bc, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h444be, value : 32'h4000c00}, //phyinit_io_write: 0x444bd, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444bf, value : 32'h0}, //phyinit_io_write: 0x444be, 0x4000c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c0, value : 32'h88000480}, //phyinit_io_write: 0x444bf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c1, value : 32'h802}, //phyinit_io_write: 0x444c0, 0x88000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c2, value : 32'h1e0}, //phyinit_io_write: 0x444c1, 0x802
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c3, value : 32'h0}, //phyinit_io_write: 0x444c2, 0x1e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c4, value : 32'h1880}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c5, value : 32'h33c2}, //phyinit_io_write: 0x444c4, 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c6, value : 32'h9c1}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 14
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c7, value : 32'h0}, //phyinit_io_write: 0x444c6, 0x9c1
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c8, value : 32'h9c000d11}, //phyinit_io_write: 0x444c7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444c9, value : 32'h1c01}, //phyinit_io_write: 0x444c8, 0x9c000d11
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ca, value : 32'h4001011}, //phyinit_io_write: 0x444c9, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h444cb, value : 32'h0}, //phyinit_io_write: 0x444ca, 0x4001011
                          '{ step_type : REG_WRITE, reg_addr : 32'h444cc, value : 32'h9c001111}, //phyinit_io_write: 0x444cb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444cd, value : 32'h1c03}, //phyinit_io_write: 0x444cc, 0x9c001111
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ce, value : 32'h4001011}, //phyinit_io_write: 0x444cd, 0x1c03
                          '{ step_type : REG_WRITE, reg_addr : 32'h444cf, value : 32'h0}, //phyinit_io_write: 0x444ce, 0x4001011
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d0, value : 32'h9c000091}, //phyinit_io_write: 0x444cf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d1, value : 32'h1c01}, //phyinit_io_write: 0x444d0, 0x9c000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d2, value : 32'h9c000091}, //phyinit_io_write: 0x444d1, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d3, value : 32'h1c03}, //phyinit_io_write: 0x444d2, 0x9c000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d4, value : 32'h9c921}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d5, value : 32'h0}, //phyinit_io_write: 0x444d4, 0x9c921
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d6, value : 32'hb8000480}, //phyinit_io_write: 0x444d5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d7, value : 32'h801}, //phyinit_io_write: 0x444d6, 0xb8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d8, value : 32'h4000800}, //phyinit_io_write: 0x444d7, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h444d9, value : 32'h0}, //phyinit_io_write: 0x444d8, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h444da, value : 32'h80068200}, //phyinit_io_write: 0x444d9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444db, value : 32'h400f}, //phyinit_io_write: 0x444da, 0x80068200
                          '{ step_type : REG_WRITE, reg_addr : 32'h444dc, value : 32'h9c140}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444dd, value : 32'h0}, //phyinit_io_write: 0x444dc, 0x9c140
                          '{ step_type : REG_WRITE, reg_addr : 32'h444de, value : 32'h8dc0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444df, value : 32'h0}, //phyinit_io_write: 0x444de, 0x8dc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e0, value : 32'h17dc0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e1, value : 32'h0}, //phyinit_io_write: 0x444e0, 0x17dc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e2, value : 32'h2a1c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e3, value : 32'h0}, //phyinit_io_write: 0x444e2, 0x2a1c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e4, value : 32'h36dc0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e5, value : 32'h0}, //phyinit_io_write: 0x444e4, 0x36dc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e6, value : 32'h395c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e7, value : 32'h0}, //phyinit_io_write: 0x444e6, 0x395c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e8, value : 32'h3adc0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444e9, value : 32'h0}, //phyinit_io_write: 0x444e8, 0x3adc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ea, value : 32'h5b9c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h444eb, value : 32'h0}, //phyinit_io_write: 0x444ea, 0x5b9c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ec, value : 32'h6001c080}, //phyinit_io_write: 0x444eb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ed, value : 32'h2425}, //phyinit_io_write: 0x444ec, 0x6001c080
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ee, value : 32'h80200}, //phyinit_io_write: 0x444ed, 0x2425
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ef, value : 32'h400e}, //phyinit_io_write: 0x444ee, 0x80200
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f0, value : 32'ha0940}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f1, value : 32'h0}, //phyinit_io_write: 0x444f0, 0xa0940
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f2, value : 32'h9ed31}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f3, value : 32'h0}, //phyinit_io_write: 0x444f2, 0x9ed31
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f4, value : 32'h6f9c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f5, value : 32'h0}, //phyinit_io_write: 0x444f4, 0x6f9c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f6, value : 32'h80008600}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f7, value : 32'h0}, //phyinit_io_write: 0x444f6, 0x80008600
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f8, value : 32'ha0940}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444f9, value : 32'h0}, //phyinit_io_write: 0x444f8, 0xa0940
                          '{ step_type : REG_WRITE, reg_addr : 32'h444fa, value : 32'h739c2}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444fb, value : 32'h0}, //phyinit_io_write: 0x444fa, 0x739c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h444fc, value : 32'h80068200}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h444fd, value : 32'h400f}, //phyinit_io_write: 0x444fc, 0x80068200
                          '{ step_type : REG_WRITE, reg_addr : 32'h444fe, value : 32'hc40004c0}, //phyinit_io_write: 0x444fd, 0x400f
                          '{ step_type : REG_WRITE, reg_addr : 32'h444ff, value : 32'h7c0}, //phyinit_io_write: 0x444fe, 0xc40004c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44500, value : 32'h4001000}, //phyinit_io_write: 0x444ff, 0x7c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44501, value : 32'h0}, //phyinit_io_write: 0x44500, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44502, value : 32'hc40000c0}, //phyinit_io_write: 0x44501, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44503, value : 32'h7c0}, //phyinit_io_write: 0x44502, 0xc40000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44504, value : 32'h40006611}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44505, value : 32'h0}, //phyinit_io_write: 0x44504, 0x40006611
                          '{ step_type : REG_WRITE, reg_addr : 32'h44506, value : 32'ha5151}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h44507, value : 32'h0}, //phyinit_io_write: 0x44506, 0xa5151
                          '{ step_type : REG_WRITE, reg_addr : 32'h44508, value : 32'h80068211}, //phyinit_io_write: 0x44507, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44509, value : 32'h400f}, //phyinit_io_write: 0x44508, 0x80068211
                          '{ step_type : REG_WRITE, reg_addr : 32'h4450a, value : 32'ha5151}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4450b, value : 32'h0}, //phyinit_io_write: 0x4450a, 0xa5151
                          '{ step_type : REG_WRITE, reg_addr : 32'h4450c, value : 32'h80211}, //phyinit_io_write: 0x4450b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4450d, value : 32'h400e}, //phyinit_io_write: 0x4450c, 0x80211
                          '{ step_type : REG_WRITE, reg_addr : 32'h4450e, value : 32'ha2951}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4450f, value : 32'h0}, //phyinit_io_write: 0x4450e, 0xa2951
                          '{ step_type : REG_WRITE, reg_addr : 32'h44510, value : 32'h80008611}, //phyinit_io_write: 0x4450f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44511, value : 32'h0}, //phyinit_io_write: 0x44510, 0x80008611
                          '{ step_type : REG_WRITE, reg_addr : 32'h44512, value : 32'ha3571}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44513, value : 32'h0}, //phyinit_io_write: 0x44512, 0xa3571
                          '{ step_type : REG_WRITE, reg_addr : 32'h44514, value : 32'h1031}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h44515, value : 32'h0}, //phyinit_io_write: 0x44514, 0x1031
                          '{ step_type : REG_WRITE, reg_addr : 32'h44516, value : 32'h1031}, //phyinit_io_write: 0x44515, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44517, value : 32'h0}, //phyinit_io_write: 0x44516, 0x1031
                          '{ step_type : REG_WRITE, reg_addr : 32'h44518, value : 32'h2c31}, //phyinit_io_write: 0x44517, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44519, value : 32'h0}, //phyinit_io_write: 0x44518, 0x2c31
                          '{ step_type : REG_WRITE, reg_addr : 32'h4451a, value : 32'ha8000091}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 14
                          '{ step_type : REG_WRITE, reg_addr : 32'h4451b, value : 32'h1c06}, //phyinit_io_write: 0x4451a, 0xa8000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h4451c, value : 32'h80016891}, //phyinit_io_write: 0x4451b, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h4451d, value : 32'h1c04}, //phyinit_io_write: 0x4451c, 0x80016891
                          '{ step_type : REG_WRITE, reg_addr : 32'h4451e, value : 32'h4000400}, //phyinit_io_write: 0x4451d, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4451f, value : 32'h0}, //phyinit_io_write: 0x4451e, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44520, value : 32'h80016c91}, //phyinit_io_write: 0x4451f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44521, value : 32'h1c04}, //phyinit_io_write: 0x44520, 0x80016c91
                          '{ step_type : REG_WRITE, reg_addr : 32'h44522, value : 32'h4000800}, //phyinit_io_write: 0x44521, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44523, value : 32'h0}, //phyinit_io_write: 0x44522, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44524, value : 32'h851}, //phyinit_io_write: 0x44523, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44525, value : 32'h6000}, //phyinit_io_write: 0x44524, 0x851
                          '{ step_type : REG_WRITE, reg_addr : 32'h44526, value : 32'h80000091}, //phyinit_io_write: 0x44525, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44527, value : 32'h1c04}, //phyinit_io_write: 0x44526, 0x80000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h44528, value : 32'h24000091}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44529, value : 32'h1e420}, //phyinit_io_write: 0x44528, 0x24000091
                          '{ step_type : REG_WRITE, reg_addr : 32'h4452a, value : 32'h899c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4452b, value : 32'h0}, //phyinit_io_write: 0x4452a, 0x899c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4452c, value : 32'h0}, //phyinit_io_write: 0x4452b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4452d, value : 32'h0}, //phyinit_io_write: 0x4452c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4452e, value : 32'h8e1c0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 6
                          '{ step_type : REG_WRITE, reg_addr : 32'h4452f, value : 32'h0}, //phyinit_io_write: 0x4452e, 0x8e1c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44530, value : 32'h24000480}, //phyinit_io_write: 0x4452f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44531, value : 32'h1c01}, //phyinit_io_write: 0x44530, 0x24000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44532, value : 32'h400}, //phyinit_io_write: 0x44531, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44533, value : 32'h0}, //phyinit_io_write: 0x44532, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44534, value : 32'h50000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 22
                          '{ step_type : REG_WRITE, reg_addr : 32'h44535, value : 32'h1c01}, //phyinit_io_write: 0x44534, 0x50000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44536, value : 32'h9c000d00}, //phyinit_io_write: 0x44535, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44537, value : 32'h1c01}, //phyinit_io_write: 0x44536, 0x9c000d00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44538, value : 32'h4001000}, //phyinit_io_write: 0x44537, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44539, value : 32'h0}, //phyinit_io_write: 0x44538, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4453a, value : 32'h9c001100}, //phyinit_io_write: 0x44539, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4453b, value : 32'h1c03}, //phyinit_io_write: 0x4453a, 0x9c001100
                          '{ step_type : REG_WRITE, reg_addr : 32'h4453c, value : 32'h4001000}, //phyinit_io_write: 0x4453b, 0x1c03
                          '{ step_type : REG_WRITE, reg_addr : 32'h4453d, value : 32'h0}, //phyinit_io_write: 0x4453c, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4453e, value : 32'h9c000080}, //phyinit_io_write: 0x4453d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4453f, value : 32'h1c01}, //phyinit_io_write: 0x4453e, 0x9c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44540, value : 32'h9c000080}, //phyinit_io_write: 0x4453f, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44541, value : 32'h1c03}, //phyinit_io_write: 0x44540, 0x9c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44542, value : 32'h1880}, //phyinit_io_write: 0x44541, 0x1c03
                          '{ step_type : REG_WRITE, reg_addr : 32'h44543, value : 32'h33c2}, //phyinit_io_write: 0x44542, 0x1880
                          '{ step_type : REG_WRITE, reg_addr : 32'h44544, value : 32'hb8000480}, //phyinit_io_write: 0x44543, 0x33c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44545, value : 32'h801}, //phyinit_io_write: 0x44544, 0xb8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44546, value : 32'h4000c00}, //phyinit_io_write: 0x44545, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h44547, value : 32'h0}, //phyinit_io_write: 0x44546, 0x4000c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44548, value : 32'h24000491}, //phyinit_io_write: 0x44547, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44549, value : 32'h1e420}, //phyinit_io_write: 0x44548, 0x24000491
                          '{ step_type : REG_WRITE, reg_addr : 32'h4454a, value : 32'ha8000080}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 10
                          '{ step_type : REG_WRITE, reg_addr : 32'h4454b, value : 32'h1c06}, //phyinit_io_write: 0x4454a, 0xa8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4454c, value : 32'h80012880}, //phyinit_io_write: 0x4454b, 0x1c06
                          '{ step_type : REG_WRITE, reg_addr : 32'h4454d, value : 32'h1c04}, //phyinit_io_write: 0x4454c, 0x80012880
                          '{ step_type : REG_WRITE, reg_addr : 32'h4454e, value : 32'h4000400}, //phyinit_io_write: 0x4454d, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h4454f, value : 32'h0}, //phyinit_io_write: 0x4454e, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44550, value : 32'h80012c80}, //phyinit_io_write: 0x4454f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44551, value : 32'h1c04}, //phyinit_io_write: 0x44550, 0x80012c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44552, value : 32'h4000800}, //phyinit_io_write: 0x44551, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44553, value : 32'h0}, //phyinit_io_write: 0x44552, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44554, value : 32'h840}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 70
                          '{ step_type : REG_WRITE, reg_addr : 32'h44555, value : 32'h6000}, //phyinit_io_write: 0x44554, 0x840
                          '{ step_type : REG_WRITE, reg_addr : 32'h44556, value : 32'h80000080}, //phyinit_io_write: 0x44555, 0x6000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44557, value : 32'h1c04}, //phyinit_io_write: 0x44556, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44558, value : 32'h2c000080}, //phyinit_io_write: 0x44557, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h44559, value : 32'h7c2}, //phyinit_io_write: 0x44558, 0x2c000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4455a, value : 32'h8c200080}, //phyinit_io_write: 0x44559, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4455b, value : 32'hfc2}, //phyinit_io_write: 0x4455a, 0x8c200080
                          '{ step_type : REG_WRITE, reg_addr : 32'h4455c, value : 32'h200600}, //phyinit_io_write: 0x4455b, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4455d, value : 32'h20}, //phyinit_io_write: 0x4455c, 0x200600
                          '{ step_type : REG_WRITE, reg_addr : 32'h4455e, value : 32'h883c0080}, //phyinit_io_write: 0x4455d, 0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h4455f, value : 32'hc02}, //phyinit_io_write: 0x4455e, 0x883c0080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44560, value : 32'h883c00c0}, //phyinit_io_write: 0x4455f, 0xc02
                          '{ step_type : REG_WRITE, reg_addr : 32'h44561, value : 32'hc42}, //phyinit_io_write: 0x44560, 0x883c00c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44562, value : 32'h98000480}, //phyinit_io_write: 0x44561, 0xc42
                          '{ step_type : REG_WRITE, reg_addr : 32'h44563, value : 32'hfc2}, //phyinit_io_write: 0x44562, 0x98000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44564, value : 32'h28000480}, //phyinit_io_write: 0x44563, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44565, value : 32'hfc0}, //phyinit_io_write: 0x44564, 0x28000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44566, value : 32'h4001000}, //phyinit_io_write: 0x44565, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44567, value : 32'h0}, //phyinit_io_write: 0x44566, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44568, value : 32'h80fffc80}, //phyinit_io_write: 0x44567, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44569, value : 32'hfc2}, //phyinit_io_write: 0x44568, 0x80fffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h4456a, value : 32'h247ffc80}, //phyinit_io_write: 0x44569, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4456b, value : 32'h7c2}, //phyinit_io_write: 0x4456a, 0x247ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h4456c, value : 32'h281ffc80}, //phyinit_io_write: 0x4456b, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4456d, value : 32'h7c2}, //phyinit_io_write: 0x4456c, 0x281ffc80
                          '{ step_type : REG_WRITE, reg_addr : 32'h4456e, value : 32'h4000400}, //phyinit_io_write: 0x4456d, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4456f, value : 32'h0}, //phyinit_io_write: 0x4456e, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h44570, value : 32'he0000480}, //phyinit_io_write: 0x4456f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44571, value : 32'h803}, //phyinit_io_write: 0x44570, 0xe0000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h44572, value : 32'h28000080}, //phyinit_io_write: 0x44571, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h44573, value : 32'hfc0}, //phyinit_io_write: 0x44572, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44574, value : 32'h800600}, //phyinit_io_write: 0x44573, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44575, value : 32'h80}, //phyinit_io_write: 0x44574, 0x800600
                          '{ step_type : REG_WRITE, reg_addr : 32'h44576, value : 32'h40000c0}, //phyinit_io_write: 0x44575, 0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h44577, value : 32'h2424}, //phyinit_io_write: 0x44576, 0x40000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44578, value : 32'h40080e0}, //phyinit_io_write: 0x44577, 0x2424
                          '{ step_type : REG_WRITE, reg_addr : 32'h44579, value : 32'h2424}, //phyinit_io_write: 0x44578, 0x40080e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4457a, value : 32'h400004e2}, //phyinit_io_write: 0x44579, 0x2424
                          '{ step_type : REG_WRITE, reg_addr : 32'h4457b, value : 32'h2c0c}, //phyinit_io_write: 0x4457a, 0x400004e2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4457c, value : 32'h4000800}, //phyinit_io_write: 0x4457b, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4457d, value : 32'h0}, //phyinit_io_write: 0x4457c, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4457e, value : 32'h400000e2}, //phyinit_io_write: 0x4457d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4457f, value : 32'h2c0c}, //phyinit_io_write: 0x4457e, 0x400000e2
                          '{ step_type : REG_WRITE, reg_addr : 32'h44580, value : 32'h4000800}, //phyinit_io_write: 0x4457f, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44581, value : 32'h0}, //phyinit_io_write: 0x44580, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44582, value : 32'h800004e0}, //phyinit_io_write: 0x44581, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44583, value : 32'h2c0c}, //phyinit_io_write: 0x44582, 0x800004e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44584, value : 32'h800000e0}, //phyinit_io_write: 0x44583, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44585, value : 32'h2c0c}, //phyinit_io_write: 0x44584, 0x800000e0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44586, value : 32'h605}, //phyinit_io_write: 0x44585, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44587, value : 32'h2000}, //phyinit_io_write: 0x44586, 0x605
                          '{ step_type : REG_WRITE, reg_addr : 32'h44588, value : 32'h400004c2}, //phyinit_io_write: 0x44587, 0x2000
                          '{ step_type : REG_WRITE, reg_addr : 32'h44589, value : 32'h2c0c}, //phyinit_io_write: 0x44588, 0x400004c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4458a, value : 32'h4000800}, //phyinit_io_write: 0x44589, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4458b, value : 32'h0}, //phyinit_io_write: 0x4458a, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h4458c, value : 32'h400000c2}, //phyinit_io_write: 0x4458b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4458d, value : 32'h2c0c}, //phyinit_io_write: 0x4458c, 0x400000c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4458e, value : 32'h4000800}, //phyinit_io_write: 0x4458d, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h4458f, value : 32'h0}, //phyinit_io_write: 0x4458e, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h44590, value : 32'h800004c0}, //phyinit_io_write: 0x4458f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44591, value : 32'h2c0c}, //phyinit_io_write: 0x44590, 0x800004c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44592, value : 32'h800000c0}, //phyinit_io_write: 0x44591, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44593, value : 32'h2c0c}, //phyinit_io_write: 0x44592, 0x800000c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44594, value : 32'h4000c00}, //phyinit_io_write: 0x44593, 0x2c0c
                          '{ step_type : REG_WRITE, reg_addr : 32'h44595, value : 32'h0}, //phyinit_io_write: 0x44594, 0x4000c00
                          '{ step_type : REG_WRITE, reg_addr : 32'h44596, value : 32'h24000080}, //phyinit_io_write: 0x44595, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h44597, value : 32'h1c01}, //phyinit_io_write: 0x44596, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h44598, value : 32'h10000200}, //phyinit_io_write: 0x44597, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h44599, value : 32'h5000}, //phyinit_io_write: 0x44598, 0x10000200
                          '{ step_type : REG_WRITE, reg_addr : 32'h4459a, value : 32'hb3d40}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4459b, value : 32'h0}, //phyinit_io_write: 0x4459a, 0xb3d40
                          '{ step_type : REG_WRITE, reg_addr : 32'h4459c, value : 32'h40}, //phyinit_io_write: 0x4459b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4459d, value : 32'h4000}, //phyinit_io_write: 0x4459c, 0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h4459e, value : 32'h28000480}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 36
                          '{ step_type : REG_WRITE, reg_addr : 32'h4459f, value : 32'hfc0}, //phyinit_io_write: 0x4459e, 0x28000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a0, value : 32'h4001000}, //phyinit_io_write: 0x4459f, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a1, value : 32'h0}, //phyinit_io_write: 0x445a0, 0x4001000
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a2, value : 32'he0000080}, //phyinit_io_write: 0x445a1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a3, value : 32'h803}, //phyinit_io_write: 0x445a2, 0xe0000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a4, value : 32'h4000800}, //phyinit_io_write: 0x445a3, 0x803
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a5, value : 32'h0}, //phyinit_io_write: 0x445a4, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a6, value : 32'h28000080}, //phyinit_io_write: 0x445a5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a7, value : 32'hfc0}, //phyinit_io_write: 0x445a6, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a8, value : 32'h80000080}, //phyinit_io_write: 0x445a7, 0xfc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445a9, value : 32'hfc2}, //phyinit_io_write: 0x445a8, 0x80000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445aa, value : 32'h98000080}, //phyinit_io_write: 0x445a9, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ab, value : 32'hfc2}, //phyinit_io_write: 0x445aa, 0x98000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ac, value : 32'h24000080}, //phyinit_io_write: 0x445ab, 0xfc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ad, value : 32'h7c2}, //phyinit_io_write: 0x445ac, 0x24000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ae, value : 32'h28000080}, //phyinit_io_write: 0x445ad, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h445af, value : 32'h7c2}, //phyinit_io_write: 0x445ae, 0x28000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b0, value : 32'he4000480}, //phyinit_io_write: 0x445af, 0x7c2
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b1, value : 32'h801}, //phyinit_io_write: 0x445b0, 0xe4000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b2, value : 32'h4000800}, //phyinit_io_write: 0x445b1, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b3, value : 32'h0}, //phyinit_io_write: 0x445b2, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b4, value : 32'he4000080}, //phyinit_io_write: 0x445b3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b5, value : 32'h801}, //phyinit_io_write: 0x445b4, 0xe4000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b6, value : 32'h4000800}, //phyinit_io_write: 0x445b5, 0x801
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b7, value : 32'h0}, //phyinit_io_write: 0x445b6, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b8, value : 32'ha8000480}, //phyinit_io_write: 0x445b7, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445b9, value : 32'h1c04}, //phyinit_io_write: 0x445b8, 0xa8000480
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ba, value : 32'h1020}, //phyinit_io_write: 0x445b9, 0x1c04
                          '{ step_type : REG_WRITE, reg_addr : 32'h445bb, value : 32'h0}, //phyinit_io_write: 0x445ba, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h445bc, value : 32'h1020}, //phyinit_io_write: 0x445bb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445bd, value : 32'h0}, //phyinit_io_write: 0x445bc, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h445be, value : 32'h1020}, //phyinit_io_write: 0x445bd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445bf, value : 32'h0}, //phyinit_io_write: 0x445be, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c0, value : 32'h1020}, //phyinit_io_write: 0x445bf, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c1, value : 32'h0}, //phyinit_io_write: 0x445c0, 0x1020
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c2, value : 32'he8030c80}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 8
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c3, value : 32'h1c01}, //phyinit_io_write: 0x445c2, 0xe8030c80
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c4, value : 32'h4000800}, //phyinit_io_write: 0x445c3, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c5, value : 32'h0}, //phyinit_io_write: 0x445c4, 0x4000800
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c6, value : 32'he8000080}, //phyinit_io_write: 0x445c5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c7, value : 32'h1c01}, //phyinit_io_write: 0x445c6, 0xe8000080
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c8, value : 32'h4000400}, //phyinit_io_write: 0x445c7, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h445c9, value : 32'h0}, //phyinit_io_write: 0x445c8, 0x4000400
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ca, value : 32'h9c000ca0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h445cb, value : 32'h1c01}, //phyinit_io_write: 0x445ca, 0x9c000ca0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445cc, value : 32'h9c0010a0}, //phyinit_io_write: 0x445cb, 0x1c01
                          '{ step_type : REG_WRITE, reg_addr : 32'h445cd, value : 32'h1c03}, //phyinit_io_write: 0x445cc, 0x9c0010a0
                          '{ step_type : REG_WRITE, reg_addr : 32'h445ce, value : 32'h9ed20}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h445cf, value : 32'h0}, //phyinit_io_write: 0x445ce, 0x9ed20
                          '{ step_type : REG_WRITE, reg_addr : 32'hd00e7, value : 32'h600}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 1
                          '{ step_type : REG_WRITE, reg_addr : 32'h7018a, value : 32'h0}, //[dwc_ddrphy_phyinit_LoadPIECodeSections] Writing code section size = 1
                          '{ step_type : REG_WRITE, reg_addr : 32'h70324, value : 32'h1}, //// The number of StartAddr is 65.
                          '{ step_type : REG_WRITE, reg_addr : 32'h70325, value : 32'h19}, //phyinit_io_write: 0x70324, 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h70326, value : 32'h2e}, //phyinit_io_write: 0x70325, 0x19
                          '{ step_type : REG_WRITE, reg_addr : 32'h70327, value : 32'h43}, //phyinit_io_write: 0x70326, 0x2e
                          '{ step_type : REG_WRITE, reg_addr : 32'h70328, value : 32'h5b}, //phyinit_io_write: 0x70327, 0x43
                          '{ step_type : REG_WRITE, reg_addr : 32'h70329, value : 32'h70}, //phyinit_io_write: 0x70328, 0x5b
                          '{ step_type : REG_WRITE, reg_addr : 32'h7032a, value : 32'h85}, //phyinit_io_write: 0x70329, 0x70
                          '{ step_type : REG_WRITE, reg_addr : 32'h7032b, value : 32'h9d}, //phyinit_io_write: 0x7032a, 0x85
                          '{ step_type : REG_WRITE, reg_addr : 32'h7032c, value : 32'hb2}, //phyinit_io_write: 0x7032b, 0x9d
                          '{ step_type : REG_WRITE, reg_addr : 32'h7032d, value : 32'hc7}, //phyinit_io_write: 0x7032c, 0xb2
                          '{ step_type : REG_WRITE, reg_addr : 32'h7032e, value : 32'hdf}, //phyinit_io_write: 0x7032d, 0xc7
                          '{ step_type : REG_WRITE, reg_addr : 32'h7032f, value : 32'hf4}, //phyinit_io_write: 0x7032e, 0xdf
                          '{ step_type : REG_WRITE, reg_addr : 32'h70330, value : 32'h109}, //phyinit_io_write: 0x7032f, 0xf4
                          '{ step_type : REG_WRITE, reg_addr : 32'h70331, value : 32'h113}, //phyinit_io_write: 0x70330, 0x109
                          '{ step_type : REG_WRITE, reg_addr : 32'h70332, value : 32'h115}, //phyinit_io_write: 0x70331, 0x113
                          '{ step_type : REG_WRITE, reg_addr : 32'h70333, value : 32'h119}, //phyinit_io_write: 0x70332, 0x115
                          '{ step_type : REG_WRITE, reg_addr : 32'h70334, value : 32'h11b}, //phyinit_io_write: 0x70333, 0x119
                          '{ step_type : REG_WRITE, reg_addr : 32'h70335, value : 32'h11f}, //phyinit_io_write: 0x70334, 0x11b
                          '{ step_type : REG_WRITE, reg_addr : 32'h70336, value : 32'h121}, //phyinit_io_write: 0x70335, 0x11f
                          '{ step_type : REG_WRITE, reg_addr : 32'h70337, value : 32'h122}, //phyinit_io_write: 0x70336, 0x121
                          '{ step_type : REG_WRITE, reg_addr : 32'h70339, value : 32'h123}, //phyinit_io_write: 0x70337, 0x122
                          '{ step_type : REG_WRITE, reg_addr : 32'h7033a, value : 32'h125}, //phyinit_io_write: 0x70339, 0x123
                          '{ step_type : REG_WRITE, reg_addr : 32'h7033c, value : 32'h126}, //phyinit_io_write: 0x7033a, 0x125
                          '{ step_type : REG_WRITE, reg_addr : 32'h7033d, value : 32'h13f}, //phyinit_io_write: 0x7033c, 0x126
                          '{ step_type : REG_WRITE, reg_addr : 32'h7033e, value : 32'h149}, //phyinit_io_write: 0x7033d, 0x13f
                          '{ step_type : REG_WRITE, reg_addr : 32'h7033f, value : 32'h161}, //phyinit_io_write: 0x7033e, 0x149
                          '{ step_type : REG_WRITE, reg_addr : 32'h70350, value : 32'h171}, //phyinit_io_write: 0x7033f, 0x161
                          '{ step_type : REG_WRITE, reg_addr : 32'h70351, value : 32'h189}, //phyinit_io_write: 0x70350, 0x171
                          '{ step_type : REG_WRITE, reg_addr : 32'h70352, value : 32'h192}, //phyinit_io_write: 0x70351, 0x189
                          '{ step_type : REG_WRITE, reg_addr : 32'h70353, value : 32'h1a4}, //phyinit_io_write: 0x70352, 0x192
                          '{ step_type : REG_WRITE, reg_addr : 32'h7038b, value : 32'h18}, //phyinit_io_write: 0x70353, 0x1a4
                          '{ step_type : REG_WRITE, reg_addr : 32'h7038c, value : 32'h2d}, //phyinit_io_write: 0x7038b, 0x18
                          '{ step_type : REG_WRITE, reg_addr : 32'h7038d, value : 32'h42}, //phyinit_io_write: 0x7038c, 0x2d
                          '{ step_type : REG_WRITE, reg_addr : 32'h7038e, value : 32'h5a}, //phyinit_io_write: 0x7038d, 0x42
                          '{ step_type : REG_WRITE, reg_addr : 32'h7038f, value : 32'h6f}, //phyinit_io_write: 0x7038e, 0x5a
                          '{ step_type : REG_WRITE, reg_addr : 32'h70390, value : 32'h84}, //phyinit_io_write: 0x7038f, 0x6f
                          '{ step_type : REG_WRITE, reg_addr : 32'h70391, value : 32'h9c}, //phyinit_io_write: 0x70390, 0x84
                          '{ step_type : REG_WRITE, reg_addr : 32'h70392, value : 32'hb1}, //phyinit_io_write: 0x70391, 0x9c
                          '{ step_type : REG_WRITE, reg_addr : 32'h70393, value : 32'hc6}, //phyinit_io_write: 0x70392, 0xb1
                          '{ step_type : REG_WRITE, reg_addr : 32'h70394, value : 32'hde}, //phyinit_io_write: 0x70393, 0xc6
                          '{ step_type : REG_WRITE, reg_addr : 32'h70395, value : 32'hf3}, //phyinit_io_write: 0x70394, 0xde
                          '{ step_type : REG_WRITE, reg_addr : 32'h70396, value : 32'h108}, //phyinit_io_write: 0x70395, 0xf3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70397, value : 32'h112}, //phyinit_io_write: 0x70396, 0x108
                          '{ step_type : REG_WRITE, reg_addr : 32'h70398, value : 32'h114}, //phyinit_io_write: 0x70397, 0x112
                          '{ step_type : REG_WRITE, reg_addr : 32'h70399, value : 32'h118}, //phyinit_io_write: 0x70398, 0x114
                          '{ step_type : REG_WRITE, reg_addr : 32'h7039a, value : 32'h11a}, //phyinit_io_write: 0x70399, 0x118
                          '{ step_type : REG_WRITE, reg_addr : 32'h7039b, value : 32'h11e}, //phyinit_io_write: 0x7039a, 0x11a
                          '{ step_type : REG_WRITE, reg_addr : 32'h7039c, value : 32'h120}, //phyinit_io_write: 0x7039b, 0x11e
                          '{ step_type : REG_WRITE, reg_addr : 32'h7039d, value : 32'h121}, //phyinit_io_write: 0x7039c, 0x120
                          '{ step_type : REG_WRITE, reg_addr : 32'h7039e, value : 32'h122}, //phyinit_io_write: 0x7039d, 0x121
                          '{ step_type : REG_WRITE, reg_addr : 32'h703a0, value : 32'h124}, //phyinit_io_write: 0x7039e, 0x122
                          '{ step_type : REG_WRITE, reg_addr : 32'h703a1, value : 32'h125}, //phyinit_io_write: 0x703a0, 0x124
                          '{ step_type : REG_WRITE, reg_addr : 32'h703a3, value : 32'h13e}, //phyinit_io_write: 0x703a1, 0x125
                          '{ step_type : REG_WRITE, reg_addr : 32'h703a4, value : 32'h148}, //phyinit_io_write: 0x703a3, 0x13e
                          '{ step_type : REG_WRITE, reg_addr : 32'h703a5, value : 32'h160}, //phyinit_io_write: 0x703a4, 0x148
                          '{ step_type : REG_WRITE, reg_addr : 32'h703a6, value : 32'h170}, //phyinit_io_write: 0x703a5, 0x160
                          '{ step_type : REG_WRITE, reg_addr : 32'h703b7, value : 32'h188}, //phyinit_io_write: 0x703a6, 0x170
                          '{ step_type : REG_WRITE, reg_addr : 32'h703b8, value : 32'h191}, //phyinit_io_write: 0x703b7, 0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h703b9, value : 32'h1a3}, //phyinit_io_write: 0x703b8, 0x191
                          '{ step_type : REG_WRITE, reg_addr : 32'h703ba, value : 32'h1b4}, //phyinit_io_write: 0x703b9, 0x1a3
                          '{ step_type : REG_WRITE, reg_addr : 32'h70200, value : 32'h40e}, //phyinit_io_write: 0x703ba, 0x1b4
                          '{ step_type : REG_WRITE, reg_addr : 32'h70202, value : 32'h44f}, //phyinit_io_write: 0x70200, 0x40e
                          '{ step_type : REG_WRITE, reg_addr : 32'h70204, value : 32'hc0}, //phyinit_io_write: 0x70202, 0x44f
                          '{ step_type : REG_WRITE, reg_addr : 32'h70205, value : 32'h246}, //phyinit_io_write: 0x70204, 0xc0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70206, value : 32'h101}, //phyinit_io_write: 0x70205, 0x246
                          '{ step_type : REG_WRITE, reg_addr : 32'h70207, value : 32'h287}, //phyinit_io_write: 0x70206, 0x101
                          '{ step_type : REG_WRITE, reg_addr : 32'h70208, value : 32'h142}, //phyinit_io_write: 0x70207, 0x287
                          '{ step_type : REG_WRITE, reg_addr : 32'h70209, value : 32'h2c8}, //phyinit_io_write: 0x70208, 0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h7020a, value : 32'h12}, //phyinit_io_write: 0x70209, 0x2c8
                          '{ step_type : REG_WRITE, reg_addr : 32'h7020b, value : 32'h34c}, //phyinit_io_write: 0x7020a, 0x12
                          '{ step_type : REG_WRITE, reg_addr : 32'h7020c, value : 32'h15}, //phyinit_io_write: 0x7020b, 0x34c
                          '{ step_type : REG_WRITE, reg_addr : 32'h7020e, value : 32'h16}, //phyinit_io_write: 0x7020c, 0x15
                          '{ step_type : REG_WRITE, reg_addr : 32'h70212, value : 32'h2c}, //phyinit_io_write: 0x7020e, 0x16
                          '{ step_type : REG_WRITE, reg_addr : 32'h70213, value : 32'h18}, //phyinit_io_write: 0x70212, 0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h70214, value : 32'h2d}, //phyinit_io_write: 0x70213, 0x18
                          '{ step_type : REG_WRITE, reg_addr : 32'h70215, value : 32'h19}, //phyinit_io_write: 0x70214, 0x2d
                          '{ step_type : REG_WRITE, reg_addr : 32'h70216, value : 32'h2e}, //phyinit_io_write: 0x70215, 0x19
                          '{ step_type : REG_WRITE, reg_addr : 32'h70217, value : 32'h1a}, //phyinit_io_write: 0x70216, 0x2e
                          '{ step_type : REG_WRITE, reg_addr : 32'h70218, value : 32'h2f}, //phyinit_io_write: 0x70217, 0x1a
                          '{ step_type : REG_WRITE, reg_addr : 32'h70219, value : 32'h1b}, //phyinit_io_write: 0x70218, 0x2f
                          '{ step_type : REG_WRITE, reg_addr : 32'h7021a, value : 32'h13}, //phyinit_io_write: 0x70219, 0x1b
                          '{ step_type : REG_WRITE, reg_addr : 32'h9001c, value : 32'h262}, //phyinit_io_write: 0x7021a, 0x13
                          '{ step_type : REG_WRITE, reg_addr : 32'h9001d, value : 32'h262}, //phyinit_io_write: 0x9001c, 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h9001e, value : 32'h262}, //phyinit_io_write: 0x9001d, 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h9001f, value : 32'h262}, //phyinit_io_write: 0x9001e, 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h90020, value : 32'h29a}, //phyinit_io_write: 0x9001f, 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h90021, value : 32'h262}, //phyinit_io_write: 0x90020, 0x29a
                          '{ step_type : REG_WRITE, reg_addr : 32'h90022, value : 32'h0}, //phyinit_io_write: 0x90021, 0x262
                          '{ step_type : REG_WRITE, reg_addr : 32'h90023, value : 32'h0}, //phyinit_io_write: 0x90022, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90024, value : 32'h0}, //phyinit_io_write: 0x90023, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90025, value : 32'h0}, //phyinit_io_write: 0x90024, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90026, value : 32'h0}, //phyinit_io_write: 0x90025, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90027, value : 32'h0}, //phyinit_io_write: 0x90026, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h9002b, value : 32'h297}, //phyinit_io_write: 0x90027, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70145, value : 32'h2}, //[loadAcsmMRW] Pstate=0, Programming ACSMRptCntOverride to 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41004, value : 32'hc9d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=19 OP=0x0 CS=0xf at row addr=0x2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41005, value : 32'h0}, //phyinit_io_write: 0x41004, 0xc9d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41006, value : 32'hc008}, //phyinit_io_write: 0x41005, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41007, value : 32'h0}, //phyinit_io_write: 0x41006, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41008, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41009, value : 32'h4b000000}, //phyinit_io_write: 0x41008, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4100a, value : 32'h0}, //phyinit_io_write: 0x41009, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4100b, value : 32'h0}, //phyinit_io_write: 0x4100a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4100c, value : 32'hc958}, //[dwc_ddrphy_mr_inst] Storing MRW MA=18 OP=0x0 CS=0xf at row addr=0x6
                          '{ step_type : REG_WRITE, reg_addr : 32'h4100d, value : 32'h0}, //phyinit_io_write: 0x4100c, 0xc958
                          '{ step_type : REG_WRITE, reg_addr : 32'h4100e, value : 32'hc008}, //phyinit_io_write: 0x4100d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4100f, value : 32'h0}, //phyinit_io_write: 0x4100e, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41010, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41011, value : 32'h4b000000}, //phyinit_io_write: 0x41010, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41012, value : 32'h0}, //phyinit_io_write: 0x41011, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41013, value : 32'h0}, //phyinit_io_write: 0x41012, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41014, value : 32'hc0d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=1 OP=0xb0 CS=0xf at row addr=0xa
                          '{ step_type : REG_WRITE, reg_addr : 32'h41015, value : 32'h0}, //phyinit_io_write: 0x41014, 0xc0d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41016, value : 32'hd848}, //phyinit_io_write: 0x41015, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41017, value : 32'h0}, //phyinit_io_write: 0x41016, 0xd848
                          '{ step_type : REG_WRITE, reg_addr : 32'h41018, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41019, value : 32'h4b000000}, //phyinit_io_write: 0x41018, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4101a, value : 32'h0}, //phyinit_io_write: 0x41019, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4101b, value : 32'h0}, //phyinit_io_write: 0x4101a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4101c, value : 32'hc158}, //[dwc_ddrphy_mr_inst] Storing MRW MA=2 OP=0xbb CS=0xf at row addr=0xe
                          '{ step_type : REG_WRITE, reg_addr : 32'h4101d, value : 32'h0}, //phyinit_io_write: 0x4101c, 0xc158
                          '{ step_type : REG_WRITE, reg_addr : 32'h4101e, value : 32'hddc8}, //phyinit_io_write: 0x4101d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4101f, value : 32'h0}, //phyinit_io_write: 0x4101e, 0xddc8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41020, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41021, value : 32'h4b000000}, //phyinit_io_write: 0x41020, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41022, value : 32'h0}, //phyinit_io_write: 0x41021, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41023, value : 32'h0}, //phyinit_io_write: 0x41022, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41024, value : 32'hc1d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=3 OP=0xe CS=0xf at row addr=0x12
                          '{ step_type : REG_WRITE, reg_addr : 32'h41025, value : 32'h0}, //phyinit_io_write: 0x41024, 0xc1d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41026, value : 32'hc708}, //phyinit_io_write: 0x41025, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41027, value : 32'h0}, //phyinit_io_write: 0x41026, 0xc708
                          '{ step_type : REG_WRITE, reg_addr : 32'h41028, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41029, value : 32'h4b000000}, //phyinit_io_write: 0x41028, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4102a, value : 32'h0}, //phyinit_io_write: 0x41029, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4102b, value : 32'h0}, //phyinit_io_write: 0x4102a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4102c, value : 32'hc558}, //[dwc_ddrphy_mr_inst] Storing MRW MA=10 OP=0x54 CS=0xf at row addr=0x16
                          '{ step_type : REG_WRITE, reg_addr : 32'h4102d, value : 32'h0}, //phyinit_io_write: 0x4102c, 0xc558
                          '{ step_type : REG_WRITE, reg_addr : 32'h4102e, value : 32'hea08}, //phyinit_io_write: 0x4102d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4102f, value : 32'h0}, //phyinit_io_write: 0x4102e, 0xea08
                          '{ step_type : REG_WRITE, reg_addr : 32'h41030, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41031, value : 32'h4b000000}, //phyinit_io_write: 0x41030, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41032, value : 32'h0}, //phyinit_io_write: 0x41031, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41033, value : 32'h0}, //phyinit_io_write: 0x41032, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41034, value : 32'hc5d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=11 OP=0x44 CS=0xf at row addr=0x1a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41035, value : 32'h0}, //phyinit_io_write: 0x41034, 0xc5d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41036, value : 32'he208}, //phyinit_io_write: 0x41035, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41037, value : 32'h0}, //phyinit_io_write: 0x41036, 0xe208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41038, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41039, value : 32'h4b000000}, //phyinit_io_write: 0x41038, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4103a, value : 32'h0}, //phyinit_io_write: 0x41039, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4103b, value : 32'h0}, //phyinit_io_write: 0x4103a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4103c, value : 32'h48d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0x84 CS=0x5 at row addr=0x1e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4103d, value : 32'h0}, //phyinit_io_write: 0x4103c, 0x48d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4103e, value : 32'h4248}, //phyinit_io_write: 0x4103d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4103f, value : 32'h0}, //phyinit_io_write: 0x4103e, 0x4248
                          '{ step_type : REG_WRITE, reg_addr : 32'h41040, value : 32'h88d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0xac CS=0xa at row addr=0x20
                          '{ step_type : REG_WRITE, reg_addr : 32'h41041, value : 32'h0}, //phyinit_io_write: 0x41040, 0x88d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41042, value : 32'h9648}, //phyinit_io_write: 0x41041, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41043, value : 32'h0}, //phyinit_io_write: 0x41042, 0x9648
                          '{ step_type : REG_WRITE, reg_addr : 32'h41044, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41045, value : 32'h4b000000}, //phyinit_io_write: 0x41044, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41046, value : 32'h0}, //phyinit_io_write: 0x41045, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41047, value : 32'h0}, //phyinit_io_write: 0x41046, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41048, value : 32'hca58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=20 OP=0x2 CS=0xf at row addr=0x24
                          '{ step_type : REG_WRITE, reg_addr : 32'h41049, value : 32'h0}, //phyinit_io_write: 0x41048, 0xca58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4104a, value : 32'hc108}, //phyinit_io_write: 0x41049, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4104b, value : 32'h0}, //phyinit_io_write: 0x4104a, 0xc108
                          '{ step_type : REG_WRITE, reg_addr : 32'h4104c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4104d, value : 32'h4b000000}, //phyinit_io_write: 0x4104c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4104e, value : 32'h0}, //phyinit_io_write: 0x4104d, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4104f, value : 32'h0}, //phyinit_io_write: 0x4104e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41050, value : 32'hcb58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=22 OP=0x0 CS=0xf at row addr=0x28
                          '{ step_type : REG_WRITE, reg_addr : 32'h41051, value : 32'h0}, //phyinit_io_write: 0x41050, 0xcb58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41052, value : 32'hc008}, //phyinit_io_write: 0x41051, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41053, value : 32'h0}, //phyinit_io_write: 0x41052, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41054, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41055, value : 32'h4b000000}, //phyinit_io_write: 0x41054, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41056, value : 32'h0}, //phyinit_io_write: 0x41055, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41057, value : 32'h0}, //phyinit_io_write: 0x41056, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41058, value : 32'hd4d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=41 OP=0x60 CS=0xf at row addr=0x2c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41059, value : 32'h0}, //phyinit_io_write: 0x41058, 0xd4d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4105a, value : 32'hf008}, //phyinit_io_write: 0x41059, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4105b, value : 32'h0}, //phyinit_io_write: 0x4105a, 0xf008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4105c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4105d, value : 32'h4b000000}, //phyinit_io_write: 0x4105c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4105e, value : 32'h0}, //phyinit_io_write: 0x4105d, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4105f, value : 32'h0}, //phyinit_io_write: 0x4105e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41060, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=58 at row addr=0x30
                          '{ step_type : REG_WRITE, reg_addr : 32'h41061, value : 32'h0}, //phyinit_io_write: 0x41060, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41062, value : 32'h0}, //phyinit_io_write: 0x41061, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41063, value : 32'h0}, //phyinit_io_write: 0x41062, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41064, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x32
                          '{ step_type : REG_WRITE, reg_addr : 32'h41065, value : 32'h0}, //phyinit_io_write: 0x41064, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41066, value : 32'h6808}, //phyinit_io_write: 0x41065, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41067, value : 32'h0}, //phyinit_io_write: 0x41066, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41068, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x34
                          '{ step_type : REG_WRITE, reg_addr : 32'h41069, value : 32'h0}, //phyinit_io_write: 0x41068, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4106a, value : 32'ha808}, //phyinit_io_write: 0x41069, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4106b, value : 32'h0}, //phyinit_io_write: 0x4106a, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4106c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4106d, value : 32'h4b000000}, //phyinit_io_write: 0x4106c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4106e, value : 32'h0}, //phyinit_io_write: 0x4106d, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4106f, value : 32'h0}, //phyinit_io_write: 0x4106e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41070, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x38
                          '{ step_type : REG_WRITE, reg_addr : 32'h41071, value : 32'h0}, //phyinit_io_write: 0x41070, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41072, value : 32'h6808}, //phyinit_io_write: 0x41071, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41073, value : 32'h0}, //phyinit_io_write: 0x41072, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41074, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x3a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41075, value : 32'h0}, //phyinit_io_write: 0x41074, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41076, value : 32'ha808}, //phyinit_io_write: 0x41075, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41077, value : 32'h0}, //phyinit_io_write: 0x41076, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41078, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41079, value : 32'h4b000000}, //phyinit_io_write: 0x41078, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4107a, value : 32'h0}, //phyinit_io_write: 0x41079, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4107b, value : 32'h0}, //phyinit_io_write: 0x4107a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4107c, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0x3e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4107d, value : 32'h0}, //phyinit_io_write: 0x4107c, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h4107e, value : 32'h6808}, //phyinit_io_write: 0x4107d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4107f, value : 32'h0}, //phyinit_io_write: 0x4107e, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41080, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0x40
                          '{ step_type : REG_WRITE, reg_addr : 32'h41081, value : 32'h0}, //phyinit_io_write: 0x41080, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h41082, value : 32'ha808}, //phyinit_io_write: 0x41081, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41083, value : 32'h0}, //phyinit_io_write: 0x41082, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41084, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41085, value : 32'h4b000000}, //phyinit_io_write: 0x41084, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41086, value : 32'h0}, //phyinit_io_write: 0x41085, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41087, value : 32'h0}, //phyinit_io_write: 0x41086, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41088, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0x44
                          '{ step_type : REG_WRITE, reg_addr : 32'h41089, value : 32'h0}, //phyinit_io_write: 0x41088, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4108a, value : 32'h6808}, //phyinit_io_write: 0x41089, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4108b, value : 32'h0}, //phyinit_io_write: 0x4108a, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4108c, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0x46
                          '{ step_type : REG_WRITE, reg_addr : 32'h4108d, value : 32'h0}, //phyinit_io_write: 0x4108c, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4108e, value : 32'ha808}, //phyinit_io_write: 0x4108d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4108f, value : 32'h0}, //phyinit_io_write: 0x4108e, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41090, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41091, value : 32'h4b000000}, //phyinit_io_write: 0x41090, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41092, value : 32'h0}, //phyinit_io_write: 0x41091, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41093, value : 32'h0}, //phyinit_io_write: 0x41092, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41094, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0x4a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41095, value : 32'h0}, //phyinit_io_write: 0x41094, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41096, value : 32'h4008}, //phyinit_io_write: 0x41095, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41097, value : 32'h0}, //phyinit_io_write: 0x41096, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41098, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0x4c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41099, value : 32'h0}, //phyinit_io_write: 0x41098, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4109a, value : 32'h8008}, //phyinit_io_write: 0x41099, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4109b, value : 32'h0}, //phyinit_io_write: 0x4109a, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4109c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h4109d, value : 32'h4b000000}, //phyinit_io_write: 0x4109c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4109e, value : 32'h0}, //phyinit_io_write: 0x4109d, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4109f, value : 32'h0}, //phyinit_io_write: 0x4109e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a0, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0x50
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a1, value : 32'h0}, //phyinit_io_write: 0x410a0, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a2, value : 32'h4008}, //phyinit_io_write: 0x410a1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a3, value : 32'h0}, //phyinit_io_write: 0x410a2, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a4, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x52
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a5, value : 32'h0}, //phyinit_io_write: 0x410a4, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a6, value : 32'h8008}, //phyinit_io_write: 0x410a5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a7, value : 32'h0}, //phyinit_io_write: 0x410a6, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410a9, value : 32'h4b000000}, //phyinit_io_write: 0x410a8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410aa, value : 32'h0}, //phyinit_io_write: 0x410a9, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ab, value : 32'h0}, //phyinit_io_write: 0x410aa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ac, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x56
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ad, value : 32'h0}, //phyinit_io_write: 0x410ac, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ae, value : 32'h0}, //phyinit_io_write: 0x410ad, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410af, value : 32'h0}, //phyinit_io_write: 0x410ae, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b0, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b1, value : 32'h0}, //phyinit_io_write: 0x410b0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b2, value : 32'h0}, //phyinit_io_write: 0x410b1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b3, value : 32'h0}, //phyinit_io_write: 0x410b2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b4, value : 32'h0}, //phyinit_io_write: 0x410b3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b5, value : 32'h0}, //phyinit_io_write: 0x410b4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b6, value : 32'h0}, //phyinit_io_write: 0x410b5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b7, value : 32'h0}, //phyinit_io_write: 0x410b6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b8, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x5c
                          '{ step_type : REG_WRITE, reg_addr : 32'h410b9, value : 32'h0}, //phyinit_io_write: 0x410b8, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ba, value : 32'h6808}, //phyinit_io_write: 0x410b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410bb, value : 32'h0}, //phyinit_io_write: 0x410ba, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410bc, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x5e
                          '{ step_type : REG_WRITE, reg_addr : 32'h410bd, value : 32'h0}, //phyinit_io_write: 0x410bc, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h410be, value : 32'ha808}, //phyinit_io_write: 0x410bd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410bf, value : 32'h0}, //phyinit_io_write: 0x410be, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c1, value : 32'h4b000000}, //phyinit_io_write: 0x410c0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c2, value : 32'h0}, //phyinit_io_write: 0x410c1, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c3, value : 32'h0}, //phyinit_io_write: 0x410c2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c4, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x62
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c5, value : 32'h0}, //phyinit_io_write: 0x410c4, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c6, value : 32'h6808}, //phyinit_io_write: 0x410c5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c7, value : 32'h0}, //phyinit_io_write: 0x410c6, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c8, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x64
                          '{ step_type : REG_WRITE, reg_addr : 32'h410c9, value : 32'h0}, //phyinit_io_write: 0x410c8, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ca, value : 32'ha808}, //phyinit_io_write: 0x410c9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410cb, value : 32'h0}, //phyinit_io_write: 0x410ca, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410cc, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410cd, value : 32'h4b000000}, //phyinit_io_write: 0x410cc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ce, value : 32'h0}, //phyinit_io_write: 0x410cd, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410cf, value : 32'h0}, //phyinit_io_write: 0x410ce, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d0, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0x68
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d1, value : 32'h0}, //phyinit_io_write: 0x410d0, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d2, value : 32'h6808}, //phyinit_io_write: 0x410d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d3, value : 32'h0}, //phyinit_io_write: 0x410d2, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d4, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0x6a
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d5, value : 32'h0}, //phyinit_io_write: 0x410d4, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d6, value : 32'ha808}, //phyinit_io_write: 0x410d5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d7, value : 32'h0}, //phyinit_io_write: 0x410d6, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410d9, value : 32'h4b000000}, //phyinit_io_write: 0x410d8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410da, value : 32'h0}, //phyinit_io_write: 0x410d9, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410db, value : 32'h0}, //phyinit_io_write: 0x410da, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410dc, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0x6e
                          '{ step_type : REG_WRITE, reg_addr : 32'h410dd, value : 32'h0}, //phyinit_io_write: 0x410dc, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h410de, value : 32'h6808}, //phyinit_io_write: 0x410dd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410df, value : 32'h0}, //phyinit_io_write: 0x410de, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e0, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0x70
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e1, value : 32'h0}, //phyinit_io_write: 0x410e0, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e2, value : 32'ha808}, //phyinit_io_write: 0x410e1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e3, value : 32'h0}, //phyinit_io_write: 0x410e2, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e4, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e5, value : 32'h4b000000}, //phyinit_io_write: 0x410e4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e6, value : 32'h0}, //phyinit_io_write: 0x410e5, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e7, value : 32'h0}, //phyinit_io_write: 0x410e6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e8, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0x74
                          '{ step_type : REG_WRITE, reg_addr : 32'h410e9, value : 32'h0}, //phyinit_io_write: 0x410e8, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ea, value : 32'h4008}, //phyinit_io_write: 0x410e9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410eb, value : 32'h0}, //phyinit_io_write: 0x410ea, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ec, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0x76
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ed, value : 32'h0}, //phyinit_io_write: 0x410ec, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ee, value : 32'h8008}, //phyinit_io_write: 0x410ed, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ef, value : 32'h0}, //phyinit_io_write: 0x410ee, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f1, value : 32'h4b000000}, //phyinit_io_write: 0x410f0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f2, value : 32'h0}, //phyinit_io_write: 0x410f1, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f3, value : 32'h0}, //phyinit_io_write: 0x410f2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f4, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0x7a
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f5, value : 32'h0}, //phyinit_io_write: 0x410f4, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f6, value : 32'h4008}, //phyinit_io_write: 0x410f5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f7, value : 32'h0}, //phyinit_io_write: 0x410f6, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f8, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x7c
                          '{ step_type : REG_WRITE, reg_addr : 32'h410f9, value : 32'h0}, //phyinit_io_write: 0x410f8, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h410fa, value : 32'h8008}, //phyinit_io_write: 0x410f9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410fb, value : 32'h0}, //phyinit_io_write: 0x410fa, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h410fc, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 8 cnt = 4
                          '{ step_type : REG_WRITE, reg_addr : 32'h410fd, value : 32'h4b000000}, //phyinit_io_write: 0x410fc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h410fe, value : 32'h0}, //phyinit_io_write: 0x410fd, 0x4b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h410ff, value : 32'h0}, //phyinit_io_write: 0x410fe, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41100, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x80
                          '{ step_type : REG_WRITE, reg_addr : 32'h41101, value : 32'h0}, //phyinit_io_write: 0x41100, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41102, value : 32'h0}, //phyinit_io_write: 0x41101, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41103, value : 32'h0}, //phyinit_io_write: 0x41102, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41104, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x82
                          '{ step_type : REG_WRITE, reg_addr : 32'h41105, value : 32'h0}, //phyinit_io_write: 0x41104, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41106, value : 32'h0}, //phyinit_io_write: 0x41105, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41107, value : 32'h0}, //phyinit_io_write: 0x41106, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41108, value : 32'h0}, //phyinit_io_write: 0x41107, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41109, value : 32'h0}, //phyinit_io_write: 0x41108, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110a, value : 32'h0}, //phyinit_io_write: 0x41109, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110b, value : 32'h0}, //phyinit_io_write: 0x4110a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h170145, value : 32'h2}, //[loadAcsmMRW] Pstate=1, Programming ACSMRptCntOverride to 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110c, value : 32'hc9d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=19 OP=0x0 CS=0xf at row addr=0x86
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110d, value : 32'h0}, //phyinit_io_write: 0x4110c, 0xc9d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110e, value : 32'hc008}, //phyinit_io_write: 0x4110d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4110f, value : 32'h0}, //phyinit_io_write: 0x4110e, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41110, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41111, value : 32'h3b000000}, //phyinit_io_write: 0x41110, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41112, value : 32'h0}, //phyinit_io_write: 0x41111, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41113, value : 32'h0}, //phyinit_io_write: 0x41112, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41114, value : 32'hc958}, //[dwc_ddrphy_mr_inst] Storing MRW MA=18 OP=0x0 CS=0xf at row addr=0x8a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41115, value : 32'h0}, //phyinit_io_write: 0x41114, 0xc958
                          '{ step_type : REG_WRITE, reg_addr : 32'h41116, value : 32'hc008}, //phyinit_io_write: 0x41115, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41117, value : 32'h0}, //phyinit_io_write: 0x41116, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41118, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41119, value : 32'h3b000000}, //phyinit_io_write: 0x41118, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4111a, value : 32'h0}, //phyinit_io_write: 0x41119, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4111b, value : 32'h0}, //phyinit_io_write: 0x4111a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4111c, value : 32'hc0d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=1 OP=0x80 CS=0xf at row addr=0x8e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4111d, value : 32'h0}, //phyinit_io_write: 0x4111c, 0xc0d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4111e, value : 32'hc048}, //phyinit_io_write: 0x4111d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4111f, value : 32'h0}, //phyinit_io_write: 0x4111e, 0xc048
                          '{ step_type : REG_WRITE, reg_addr : 32'h41120, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41121, value : 32'h3b000000}, //phyinit_io_write: 0x41120, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41122, value : 32'h0}, //phyinit_io_write: 0x41121, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41123, value : 32'h0}, //phyinit_io_write: 0x41122, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41124, value : 32'hc158}, //[dwc_ddrphy_mr_inst] Storing MRW MA=2 OP=0x88 CS=0xf at row addr=0x92
                          '{ step_type : REG_WRITE, reg_addr : 32'h41125, value : 32'h0}, //phyinit_io_write: 0x41124, 0xc158
                          '{ step_type : REG_WRITE, reg_addr : 32'h41126, value : 32'hc448}, //phyinit_io_write: 0x41125, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41127, value : 32'h0}, //phyinit_io_write: 0x41126, 0xc448
                          '{ step_type : REG_WRITE, reg_addr : 32'h41128, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41129, value : 32'h3b000000}, //phyinit_io_write: 0x41128, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4112a, value : 32'h0}, //phyinit_io_write: 0x41129, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4112b, value : 32'h0}, //phyinit_io_write: 0x4112a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4112c, value : 32'hc1d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=3 OP=0xe CS=0xf at row addr=0x96
                          '{ step_type : REG_WRITE, reg_addr : 32'h4112d, value : 32'h0}, //phyinit_io_write: 0x4112c, 0xc1d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4112e, value : 32'hc708}, //phyinit_io_write: 0x4112d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4112f, value : 32'h0}, //phyinit_io_write: 0x4112e, 0xc708
                          '{ step_type : REG_WRITE, reg_addr : 32'h41130, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41131, value : 32'h3b000000}, //phyinit_io_write: 0x41130, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41132, value : 32'h0}, //phyinit_io_write: 0x41131, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41133, value : 32'h0}, //phyinit_io_write: 0x41132, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41134, value : 32'hc558}, //[dwc_ddrphy_mr_inst] Storing MRW MA=10 OP=0x54 CS=0xf at row addr=0x9a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41135, value : 32'h0}, //phyinit_io_write: 0x41134, 0xc558
                          '{ step_type : REG_WRITE, reg_addr : 32'h41136, value : 32'hea08}, //phyinit_io_write: 0x41135, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41137, value : 32'h0}, //phyinit_io_write: 0x41136, 0xea08
                          '{ step_type : REG_WRITE, reg_addr : 32'h41138, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41139, value : 32'h3b000000}, //phyinit_io_write: 0x41138, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4113a, value : 32'h0}, //phyinit_io_write: 0x41139, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4113b, value : 32'h0}, //phyinit_io_write: 0x4113a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4113c, value : 32'hc5d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=11 OP=0x44 CS=0xf at row addr=0x9e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4113d, value : 32'h0}, //phyinit_io_write: 0x4113c, 0xc5d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4113e, value : 32'he208}, //phyinit_io_write: 0x4113d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4113f, value : 32'h0}, //phyinit_io_write: 0x4113e, 0xe208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41140, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41141, value : 32'h3b000000}, //phyinit_io_write: 0x41140, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41142, value : 32'h0}, //phyinit_io_write: 0x41141, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41143, value : 32'h0}, //phyinit_io_write: 0x41142, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41144, value : 32'h48d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0x84 CS=0x5 at row addr=0xa2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41145, value : 32'h0}, //phyinit_io_write: 0x41144, 0x48d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41146, value : 32'h4248}, //phyinit_io_write: 0x41145, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41147, value : 32'h0}, //phyinit_io_write: 0x41146, 0x4248
                          '{ step_type : REG_WRITE, reg_addr : 32'h41148, value : 32'h88d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0xac CS=0xa at row addr=0xa4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41149, value : 32'h0}, //phyinit_io_write: 0x41148, 0x88d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4114a, value : 32'h9648}, //phyinit_io_write: 0x41149, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4114b, value : 32'h0}, //phyinit_io_write: 0x4114a, 0x9648
                          '{ step_type : REG_WRITE, reg_addr : 32'h4114c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h4114d, value : 32'h3b000000}, //phyinit_io_write: 0x4114c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4114e, value : 32'h0}, //phyinit_io_write: 0x4114d, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4114f, value : 32'h0}, //phyinit_io_write: 0x4114e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41150, value : 32'hca58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=20 OP=0x2 CS=0xf at row addr=0xa8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41151, value : 32'h0}, //phyinit_io_write: 0x41150, 0xca58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41152, value : 32'hc108}, //phyinit_io_write: 0x41151, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41153, value : 32'h0}, //phyinit_io_write: 0x41152, 0xc108
                          '{ step_type : REG_WRITE, reg_addr : 32'h41154, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41155, value : 32'h3b000000}, //phyinit_io_write: 0x41154, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41156, value : 32'h0}, //phyinit_io_write: 0x41155, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41157, value : 32'h0}, //phyinit_io_write: 0x41156, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41158, value : 32'hcb58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=22 OP=0x0 CS=0xf at row addr=0xac
                          '{ step_type : REG_WRITE, reg_addr : 32'h41159, value : 32'h0}, //phyinit_io_write: 0x41158, 0xcb58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4115a, value : 32'hc008}, //phyinit_io_write: 0x41159, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4115b, value : 32'h0}, //phyinit_io_write: 0x4115a, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4115c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h4115d, value : 32'h3b000000}, //phyinit_io_write: 0x4115c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4115e, value : 32'h0}, //phyinit_io_write: 0x4115d, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4115f, value : 32'h0}, //phyinit_io_write: 0x4115e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41160, value : 32'hd4d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=41 OP=0x60 CS=0xf at row addr=0xb0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41161, value : 32'h0}, //phyinit_io_write: 0x41160, 0xd4d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41162, value : 32'hf008}, //phyinit_io_write: 0x41161, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41163, value : 32'h0}, //phyinit_io_write: 0x41162, 0xf008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41164, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41165, value : 32'h3b000000}, //phyinit_io_write: 0x41164, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41166, value : 32'h0}, //phyinit_io_write: 0x41165, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41167, value : 32'h0}, //phyinit_io_write: 0x41166, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41168, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=58 at row addr=0xb4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41169, value : 32'h0}, //phyinit_io_write: 0x41168, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4116a, value : 32'h0}, //phyinit_io_write: 0x41169, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4116b, value : 32'h0}, //phyinit_io_write: 0x4116a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4116c, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0xb6
                          '{ step_type : REG_WRITE, reg_addr : 32'h4116d, value : 32'h0}, //phyinit_io_write: 0x4116c, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4116e, value : 32'h6808}, //phyinit_io_write: 0x4116d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4116f, value : 32'h0}, //phyinit_io_write: 0x4116e, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41170, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0xb8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41171, value : 32'h0}, //phyinit_io_write: 0x41170, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41172, value : 32'ha808}, //phyinit_io_write: 0x41171, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41173, value : 32'h0}, //phyinit_io_write: 0x41172, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41174, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41175, value : 32'h3b000000}, //phyinit_io_write: 0x41174, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41176, value : 32'h0}, //phyinit_io_write: 0x41175, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41177, value : 32'h0}, //phyinit_io_write: 0x41176, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41178, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0xbc
                          '{ step_type : REG_WRITE, reg_addr : 32'h41179, value : 32'h0}, //phyinit_io_write: 0x41178, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4117a, value : 32'h6808}, //phyinit_io_write: 0x41179, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4117b, value : 32'h0}, //phyinit_io_write: 0x4117a, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4117c, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0xbe
                          '{ step_type : REG_WRITE, reg_addr : 32'h4117d, value : 32'h0}, //phyinit_io_write: 0x4117c, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4117e, value : 32'ha808}, //phyinit_io_write: 0x4117d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4117f, value : 32'h0}, //phyinit_io_write: 0x4117e, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41180, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41181, value : 32'h3b000000}, //phyinit_io_write: 0x41180, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41182, value : 32'h0}, //phyinit_io_write: 0x41181, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41183, value : 32'h0}, //phyinit_io_write: 0x41182, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41184, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0xc2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41185, value : 32'h0}, //phyinit_io_write: 0x41184, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h41186, value : 32'h6808}, //phyinit_io_write: 0x41185, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41187, value : 32'h0}, //phyinit_io_write: 0x41186, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41188, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0xc4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41189, value : 32'h0}, //phyinit_io_write: 0x41188, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h4118a, value : 32'ha808}, //phyinit_io_write: 0x41189, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4118b, value : 32'h0}, //phyinit_io_write: 0x4118a, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4118c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h4118d, value : 32'h3b000000}, //phyinit_io_write: 0x4118c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4118e, value : 32'h0}, //phyinit_io_write: 0x4118d, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4118f, value : 32'h0}, //phyinit_io_write: 0x4118e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41190, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0xc8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41191, value : 32'h0}, //phyinit_io_write: 0x41190, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41192, value : 32'h6808}, //phyinit_io_write: 0x41191, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41193, value : 32'h0}, //phyinit_io_write: 0x41192, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41194, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0xca
                          '{ step_type : REG_WRITE, reg_addr : 32'h41195, value : 32'h0}, //phyinit_io_write: 0x41194, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41196, value : 32'ha808}, //phyinit_io_write: 0x41195, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41197, value : 32'h0}, //phyinit_io_write: 0x41196, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41198, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41199, value : 32'h3b000000}, //phyinit_io_write: 0x41198, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4119a, value : 32'h0}, //phyinit_io_write: 0x41199, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4119b, value : 32'h0}, //phyinit_io_write: 0x4119a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4119c, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0xce
                          '{ step_type : REG_WRITE, reg_addr : 32'h4119d, value : 32'h0}, //phyinit_io_write: 0x4119c, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4119e, value : 32'h4008}, //phyinit_io_write: 0x4119d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4119f, value : 32'h0}, //phyinit_io_write: 0x4119e, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a0, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0xd0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a1, value : 32'h0}, //phyinit_io_write: 0x411a0, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a2, value : 32'h8008}, //phyinit_io_write: 0x411a1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a3, value : 32'h0}, //phyinit_io_write: 0x411a2, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a4, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a5, value : 32'h3b000000}, //phyinit_io_write: 0x411a4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a6, value : 32'h0}, //phyinit_io_write: 0x411a5, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a7, value : 32'h0}, //phyinit_io_write: 0x411a6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a8, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0xd4
                          '{ step_type : REG_WRITE, reg_addr : 32'h411a9, value : 32'h0}, //phyinit_io_write: 0x411a8, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h411aa, value : 32'h4008}, //phyinit_io_write: 0x411a9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ab, value : 32'h0}, //phyinit_io_write: 0x411aa, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ac, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0xd6
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ad, value : 32'h0}, //phyinit_io_write: 0x411ac, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ae, value : 32'h8008}, //phyinit_io_write: 0x411ad, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411af, value : 32'h0}, //phyinit_io_write: 0x411ae, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b1, value : 32'h3b000000}, //phyinit_io_write: 0x411b0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b2, value : 32'h0}, //phyinit_io_write: 0x411b1, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b3, value : 32'h0}, //phyinit_io_write: 0x411b2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b4, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0xda
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b5, value : 32'h0}, //phyinit_io_write: 0x411b4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b6, value : 32'h0}, //phyinit_io_write: 0x411b5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b7, value : 32'h0}, //phyinit_io_write: 0x411b6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b8, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0xdc
                          '{ step_type : REG_WRITE, reg_addr : 32'h411b9, value : 32'h0}, //phyinit_io_write: 0x411b8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ba, value : 32'h0}, //phyinit_io_write: 0x411b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411bb, value : 32'h0}, //phyinit_io_write: 0x411ba, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411bc, value : 32'h0}, //phyinit_io_write: 0x411bb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411bd, value : 32'h0}, //phyinit_io_write: 0x411bc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411be, value : 32'h0}, //phyinit_io_write: 0x411bd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411bf, value : 32'h0}, //phyinit_io_write: 0x411be, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c0, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0xe0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c1, value : 32'h0}, //phyinit_io_write: 0x411c0, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c2, value : 32'h6808}, //phyinit_io_write: 0x411c1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c3, value : 32'h0}, //phyinit_io_write: 0x411c2, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c4, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0xe2
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c5, value : 32'h0}, //phyinit_io_write: 0x411c4, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c6, value : 32'ha808}, //phyinit_io_write: 0x411c5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c7, value : 32'h0}, //phyinit_io_write: 0x411c6, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411c9, value : 32'h3b000000}, //phyinit_io_write: 0x411c8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ca, value : 32'h0}, //phyinit_io_write: 0x411c9, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411cb, value : 32'h0}, //phyinit_io_write: 0x411ca, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411cc, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0xe6
                          '{ step_type : REG_WRITE, reg_addr : 32'h411cd, value : 32'h0}, //phyinit_io_write: 0x411cc, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ce, value : 32'h6808}, //phyinit_io_write: 0x411cd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411cf, value : 32'h0}, //phyinit_io_write: 0x411ce, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d0, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0xe8
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d1, value : 32'h0}, //phyinit_io_write: 0x411d0, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d2, value : 32'ha808}, //phyinit_io_write: 0x411d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d3, value : 32'h0}, //phyinit_io_write: 0x411d2, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d4, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d5, value : 32'h3b000000}, //phyinit_io_write: 0x411d4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d6, value : 32'h0}, //phyinit_io_write: 0x411d5, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d7, value : 32'h0}, //phyinit_io_write: 0x411d6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d8, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0xec
                          '{ step_type : REG_WRITE, reg_addr : 32'h411d9, value : 32'h0}, //phyinit_io_write: 0x411d8, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h411da, value : 32'h6808}, //phyinit_io_write: 0x411d9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411db, value : 32'h0}, //phyinit_io_write: 0x411da, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411dc, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0xee
                          '{ step_type : REG_WRITE, reg_addr : 32'h411dd, value : 32'h0}, //phyinit_io_write: 0x411dc, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h411de, value : 32'ha808}, //phyinit_io_write: 0x411dd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411df, value : 32'h0}, //phyinit_io_write: 0x411de, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e1, value : 32'h3b000000}, //phyinit_io_write: 0x411e0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e2, value : 32'h0}, //phyinit_io_write: 0x411e1, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e3, value : 32'h0}, //phyinit_io_write: 0x411e2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e4, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0xf2
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e5, value : 32'h0}, //phyinit_io_write: 0x411e4, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e6, value : 32'h6808}, //phyinit_io_write: 0x411e5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e7, value : 32'h0}, //phyinit_io_write: 0x411e6, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e8, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0xf4
                          '{ step_type : REG_WRITE, reg_addr : 32'h411e9, value : 32'h0}, //phyinit_io_write: 0x411e8, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ea, value : 32'ha808}, //phyinit_io_write: 0x411e9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411eb, value : 32'h0}, //phyinit_io_write: 0x411ea, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ec, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ed, value : 32'h3b000000}, //phyinit_io_write: 0x411ec, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ee, value : 32'h0}, //phyinit_io_write: 0x411ed, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ef, value : 32'h0}, //phyinit_io_write: 0x411ee, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f0, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0xf8
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f1, value : 32'h0}, //phyinit_io_write: 0x411f0, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f2, value : 32'h4008}, //phyinit_io_write: 0x411f1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f3, value : 32'h0}, //phyinit_io_write: 0x411f2, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f4, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0xfa
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f5, value : 32'h0}, //phyinit_io_write: 0x411f4, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f6, value : 32'h8008}, //phyinit_io_write: 0x411f5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f7, value : 32'h0}, //phyinit_io_write: 0x411f6, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h411f9, value : 32'h3b000000}, //phyinit_io_write: 0x411f8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411fa, value : 32'h0}, //phyinit_io_write: 0x411f9, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h411fb, value : 32'h0}, //phyinit_io_write: 0x411fa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411fc, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0xfe
                          '{ step_type : REG_WRITE, reg_addr : 32'h411fd, value : 32'h0}, //phyinit_io_write: 0x411fc, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h411fe, value : 32'h4008}, //phyinit_io_write: 0x411fd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h411ff, value : 32'h0}, //phyinit_io_write: 0x411fe, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41200, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x100
                          '{ step_type : REG_WRITE, reg_addr : 32'h41201, value : 32'h0}, //phyinit_io_write: 0x41200, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41202, value : 32'h8008}, //phyinit_io_write: 0x41201, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41203, value : 32'h0}, //phyinit_io_write: 0x41202, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41204, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 7 cnt = 3
                          '{ step_type : REG_WRITE, reg_addr : 32'h41205, value : 32'h3b000000}, //phyinit_io_write: 0x41204, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41206, value : 32'h0}, //phyinit_io_write: 0x41205, 0x3b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41207, value : 32'h0}, //phyinit_io_write: 0x41206, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41208, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x104
                          '{ step_type : REG_WRITE, reg_addr : 32'h41209, value : 32'h0}, //phyinit_io_write: 0x41208, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4120a, value : 32'h0}, //phyinit_io_write: 0x41209, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4120b, value : 32'h0}, //phyinit_io_write: 0x4120a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4120c, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x106
                          '{ step_type : REG_WRITE, reg_addr : 32'h4120d, value : 32'h0}, //phyinit_io_write: 0x4120c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4120e, value : 32'h0}, //phyinit_io_write: 0x4120d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4120f, value : 32'h0}, //phyinit_io_write: 0x4120e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41210, value : 32'h0}, //phyinit_io_write: 0x4120f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41211, value : 32'h0}, //phyinit_io_write: 0x41210, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41212, value : 32'h0}, //phyinit_io_write: 0x41211, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41213, value : 32'h0}, //phyinit_io_write: 0x41212, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h270145, value : 32'h1}, //[loadAcsmMRW] Pstate=2, Programming ACSMRptCntOverride to 1
                          '{ step_type : REG_WRITE, reg_addr : 32'h41214, value : 32'hc9d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=19 OP=0x0 CS=0xf at row addr=0x10a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41215, value : 32'h0}, //phyinit_io_write: 0x41214, 0xc9d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41216, value : 32'hc008}, //phyinit_io_write: 0x41215, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41217, value : 32'h0}, //phyinit_io_write: 0x41216, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41218, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41219, value : 32'h2b000000}, //phyinit_io_write: 0x41218, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4121a, value : 32'h0}, //phyinit_io_write: 0x41219, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4121b, value : 32'h0}, //phyinit_io_write: 0x4121a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4121c, value : 32'hc958}, //[dwc_ddrphy_mr_inst] Storing MRW MA=18 OP=0x0 CS=0xf at row addr=0x10e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4121d, value : 32'h0}, //phyinit_io_write: 0x4121c, 0xc958
                          '{ step_type : REG_WRITE, reg_addr : 32'h4121e, value : 32'hc008}, //phyinit_io_write: 0x4121d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4121f, value : 32'h0}, //phyinit_io_write: 0x4121e, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41220, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41221, value : 32'h2b000000}, //phyinit_io_write: 0x41220, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41222, value : 32'h0}, //phyinit_io_write: 0x41221, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41223, value : 32'h0}, //phyinit_io_write: 0x41222, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41224, value : 32'hc0d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=1 OP=0x50 CS=0xf at row addr=0x112
                          '{ step_type : REG_WRITE, reg_addr : 32'h41225, value : 32'h0}, //phyinit_io_write: 0x41224, 0xc0d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41226, value : 32'he808}, //phyinit_io_write: 0x41225, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41227, value : 32'h0}, //phyinit_io_write: 0x41226, 0xe808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41228, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41229, value : 32'h2b000000}, //phyinit_io_write: 0x41228, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4122a, value : 32'h0}, //phyinit_io_write: 0x41229, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4122b, value : 32'h0}, //phyinit_io_write: 0x4122a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4122c, value : 32'hc158}, //[dwc_ddrphy_mr_inst] Storing MRW MA=2 OP=0x55 CS=0xf at row addr=0x116
                          '{ step_type : REG_WRITE, reg_addr : 32'h4122d, value : 32'h0}, //phyinit_io_write: 0x4122c, 0xc158
                          '{ step_type : REG_WRITE, reg_addr : 32'h4122e, value : 32'hea88}, //phyinit_io_write: 0x4122d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4122f, value : 32'h0}, //phyinit_io_write: 0x4122e, 0xea88
                          '{ step_type : REG_WRITE, reg_addr : 32'h41230, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41231, value : 32'h2b000000}, //phyinit_io_write: 0x41230, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41232, value : 32'h0}, //phyinit_io_write: 0x41231, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41233, value : 32'h0}, //phyinit_io_write: 0x41232, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41234, value : 32'hc1d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=3 OP=0xe CS=0xf at row addr=0x11a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41235, value : 32'h0}, //phyinit_io_write: 0x41234, 0xc1d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41236, value : 32'hc708}, //phyinit_io_write: 0x41235, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41237, value : 32'h0}, //phyinit_io_write: 0x41236, 0xc708
                          '{ step_type : REG_WRITE, reg_addr : 32'h41238, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41239, value : 32'h2b000000}, //phyinit_io_write: 0x41238, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4123a, value : 32'h0}, //phyinit_io_write: 0x41239, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4123b, value : 32'h0}, //phyinit_io_write: 0x4123a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4123c, value : 32'hc558}, //[dwc_ddrphy_mr_inst] Storing MRW MA=10 OP=0x54 CS=0xf at row addr=0x11e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4123d, value : 32'h0}, //phyinit_io_write: 0x4123c, 0xc558
                          '{ step_type : REG_WRITE, reg_addr : 32'h4123e, value : 32'hea08}, //phyinit_io_write: 0x4123d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4123f, value : 32'h0}, //phyinit_io_write: 0x4123e, 0xea08
                          '{ step_type : REG_WRITE, reg_addr : 32'h41240, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41241, value : 32'h2b000000}, //phyinit_io_write: 0x41240, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41242, value : 32'h0}, //phyinit_io_write: 0x41241, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41243, value : 32'h0}, //phyinit_io_write: 0x41242, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41244, value : 32'hc5d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=11 OP=0x44 CS=0xf at row addr=0x122
                          '{ step_type : REG_WRITE, reg_addr : 32'h41245, value : 32'h0}, //phyinit_io_write: 0x41244, 0xc5d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41246, value : 32'he208}, //phyinit_io_write: 0x41245, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41247, value : 32'h0}, //phyinit_io_write: 0x41246, 0xe208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41248, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41249, value : 32'h2b000000}, //phyinit_io_write: 0x41248, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4124a, value : 32'h0}, //phyinit_io_write: 0x41249, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4124b, value : 32'h0}, //phyinit_io_write: 0x4124a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4124c, value : 32'h48d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0x84 CS=0x5 at row addr=0x126
                          '{ step_type : REG_WRITE, reg_addr : 32'h4124d, value : 32'h0}, //phyinit_io_write: 0x4124c, 0x48d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4124e, value : 32'h4248}, //phyinit_io_write: 0x4124d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4124f, value : 32'h0}, //phyinit_io_write: 0x4124e, 0x4248
                          '{ step_type : REG_WRITE, reg_addr : 32'h41250, value : 32'h88d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0xac CS=0xa at row addr=0x128
                          '{ step_type : REG_WRITE, reg_addr : 32'h41251, value : 32'h0}, //phyinit_io_write: 0x41250, 0x88d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41252, value : 32'h9648}, //phyinit_io_write: 0x41251, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41253, value : 32'h0}, //phyinit_io_write: 0x41252, 0x9648
                          '{ step_type : REG_WRITE, reg_addr : 32'h41254, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41255, value : 32'h2b000000}, //phyinit_io_write: 0x41254, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41256, value : 32'h0}, //phyinit_io_write: 0x41255, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41257, value : 32'h0}, //phyinit_io_write: 0x41256, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41258, value : 32'hca58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=20 OP=0x2 CS=0xf at row addr=0x12c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41259, value : 32'h0}, //phyinit_io_write: 0x41258, 0xca58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4125a, value : 32'hc108}, //phyinit_io_write: 0x41259, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4125b, value : 32'h0}, //phyinit_io_write: 0x4125a, 0xc108
                          '{ step_type : REG_WRITE, reg_addr : 32'h4125c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4125d, value : 32'h2b000000}, //phyinit_io_write: 0x4125c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4125e, value : 32'h0}, //phyinit_io_write: 0x4125d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4125f, value : 32'h0}, //phyinit_io_write: 0x4125e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41260, value : 32'hcb58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=22 OP=0x0 CS=0xf at row addr=0x130
                          '{ step_type : REG_WRITE, reg_addr : 32'h41261, value : 32'h0}, //phyinit_io_write: 0x41260, 0xcb58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41262, value : 32'hc008}, //phyinit_io_write: 0x41261, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41263, value : 32'h0}, //phyinit_io_write: 0x41262, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41264, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41265, value : 32'h2b000000}, //phyinit_io_write: 0x41264, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41266, value : 32'h0}, //phyinit_io_write: 0x41265, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41267, value : 32'h0}, //phyinit_io_write: 0x41266, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41268, value : 32'hd4d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=41 OP=0x60 CS=0xf at row addr=0x134
                          '{ step_type : REG_WRITE, reg_addr : 32'h41269, value : 32'h0}, //phyinit_io_write: 0x41268, 0xd4d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4126a, value : 32'hf008}, //phyinit_io_write: 0x41269, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4126b, value : 32'h0}, //phyinit_io_write: 0x4126a, 0xf008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4126c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4126d, value : 32'h2b000000}, //phyinit_io_write: 0x4126c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4126e, value : 32'h0}, //phyinit_io_write: 0x4126d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4126f, value : 32'h0}, //phyinit_io_write: 0x4126e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41270, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=58 at row addr=0x138
                          '{ step_type : REG_WRITE, reg_addr : 32'h41271, value : 32'h0}, //phyinit_io_write: 0x41270, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41272, value : 32'h0}, //phyinit_io_write: 0x41271, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41273, value : 32'h0}, //phyinit_io_write: 0x41272, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41274, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x13a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41275, value : 32'h0}, //phyinit_io_write: 0x41274, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41276, value : 32'h6808}, //phyinit_io_write: 0x41275, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41277, value : 32'h0}, //phyinit_io_write: 0x41276, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41278, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x13c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41279, value : 32'h0}, //phyinit_io_write: 0x41278, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4127a, value : 32'ha808}, //phyinit_io_write: 0x41279, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4127b, value : 32'h0}, //phyinit_io_write: 0x4127a, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4127c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4127d, value : 32'h2b000000}, //phyinit_io_write: 0x4127c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4127e, value : 32'h0}, //phyinit_io_write: 0x4127d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4127f, value : 32'h0}, //phyinit_io_write: 0x4127e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41280, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x140
                          '{ step_type : REG_WRITE, reg_addr : 32'h41281, value : 32'h0}, //phyinit_io_write: 0x41280, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41282, value : 32'h6808}, //phyinit_io_write: 0x41281, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41283, value : 32'h0}, //phyinit_io_write: 0x41282, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41284, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x142
                          '{ step_type : REG_WRITE, reg_addr : 32'h41285, value : 32'h0}, //phyinit_io_write: 0x41284, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41286, value : 32'ha808}, //phyinit_io_write: 0x41285, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41287, value : 32'h0}, //phyinit_io_write: 0x41286, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41288, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41289, value : 32'h2b000000}, //phyinit_io_write: 0x41288, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4128a, value : 32'h0}, //phyinit_io_write: 0x41289, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4128b, value : 32'h0}, //phyinit_io_write: 0x4128a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4128c, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0x146
                          '{ step_type : REG_WRITE, reg_addr : 32'h4128d, value : 32'h0}, //phyinit_io_write: 0x4128c, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h4128e, value : 32'h6808}, //phyinit_io_write: 0x4128d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4128f, value : 32'h0}, //phyinit_io_write: 0x4128e, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41290, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0x148
                          '{ step_type : REG_WRITE, reg_addr : 32'h41291, value : 32'h0}, //phyinit_io_write: 0x41290, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h41292, value : 32'ha808}, //phyinit_io_write: 0x41291, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41293, value : 32'h0}, //phyinit_io_write: 0x41292, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41294, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41295, value : 32'h2b000000}, //phyinit_io_write: 0x41294, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41296, value : 32'h0}, //phyinit_io_write: 0x41295, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41297, value : 32'h0}, //phyinit_io_write: 0x41296, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41298, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0x14c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41299, value : 32'h0}, //phyinit_io_write: 0x41298, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4129a, value : 32'h6808}, //phyinit_io_write: 0x41299, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4129b, value : 32'h0}, //phyinit_io_write: 0x4129a, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4129c, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0x14e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4129d, value : 32'h0}, //phyinit_io_write: 0x4129c, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4129e, value : 32'ha808}, //phyinit_io_write: 0x4129d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4129f, value : 32'h0}, //phyinit_io_write: 0x4129e, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a1, value : 32'h2b000000}, //phyinit_io_write: 0x412a0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a2, value : 32'h0}, //phyinit_io_write: 0x412a1, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a3, value : 32'h0}, //phyinit_io_write: 0x412a2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a4, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0x152
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a5, value : 32'h0}, //phyinit_io_write: 0x412a4, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a6, value : 32'h4008}, //phyinit_io_write: 0x412a5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a7, value : 32'h0}, //phyinit_io_write: 0x412a6, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a8, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0x154
                          '{ step_type : REG_WRITE, reg_addr : 32'h412a9, value : 32'h0}, //phyinit_io_write: 0x412a8, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h412aa, value : 32'h8008}, //phyinit_io_write: 0x412a9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ab, value : 32'h0}, //phyinit_io_write: 0x412aa, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ac, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ad, value : 32'h2b000000}, //phyinit_io_write: 0x412ac, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ae, value : 32'h0}, //phyinit_io_write: 0x412ad, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412af, value : 32'h0}, //phyinit_io_write: 0x412ae, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b0, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0x158
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b1, value : 32'h0}, //phyinit_io_write: 0x412b0, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b2, value : 32'h4008}, //phyinit_io_write: 0x412b1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b3, value : 32'h0}, //phyinit_io_write: 0x412b2, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b4, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x15a
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b5, value : 32'h0}, //phyinit_io_write: 0x412b4, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b6, value : 32'h8008}, //phyinit_io_write: 0x412b5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b7, value : 32'h0}, //phyinit_io_write: 0x412b6, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412b9, value : 32'h2b000000}, //phyinit_io_write: 0x412b8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ba, value : 32'h0}, //phyinit_io_write: 0x412b9, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412bb, value : 32'h0}, //phyinit_io_write: 0x412ba, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412bc, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x15e
                          '{ step_type : REG_WRITE, reg_addr : 32'h412bd, value : 32'h0}, //phyinit_io_write: 0x412bc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412be, value : 32'h0}, //phyinit_io_write: 0x412bd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412bf, value : 32'h0}, //phyinit_io_write: 0x412be, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c0, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x160
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c1, value : 32'h0}, //phyinit_io_write: 0x412c0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c2, value : 32'h0}, //phyinit_io_write: 0x412c1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c3, value : 32'h0}, //phyinit_io_write: 0x412c2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c4, value : 32'h0}, //phyinit_io_write: 0x412c3, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c5, value : 32'h0}, //phyinit_io_write: 0x412c4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c6, value : 32'h0}, //phyinit_io_write: 0x412c5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c7, value : 32'h0}, //phyinit_io_write: 0x412c6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c8, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x164
                          '{ step_type : REG_WRITE, reg_addr : 32'h412c9, value : 32'h0}, //phyinit_io_write: 0x412c8, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ca, value : 32'h6808}, //phyinit_io_write: 0x412c9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412cb, value : 32'h0}, //phyinit_io_write: 0x412ca, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412cc, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x166
                          '{ step_type : REG_WRITE, reg_addr : 32'h412cd, value : 32'h0}, //phyinit_io_write: 0x412cc, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ce, value : 32'ha808}, //phyinit_io_write: 0x412cd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412cf, value : 32'h0}, //phyinit_io_write: 0x412ce, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d1, value : 32'h2b000000}, //phyinit_io_write: 0x412d0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d2, value : 32'h0}, //phyinit_io_write: 0x412d1, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d3, value : 32'h0}, //phyinit_io_write: 0x412d2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d4, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x16a
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d5, value : 32'h0}, //phyinit_io_write: 0x412d4, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d6, value : 32'h6808}, //phyinit_io_write: 0x412d5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d7, value : 32'h0}, //phyinit_io_write: 0x412d6, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d8, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x16c
                          '{ step_type : REG_WRITE, reg_addr : 32'h412d9, value : 32'h0}, //phyinit_io_write: 0x412d8, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h412da, value : 32'ha808}, //phyinit_io_write: 0x412d9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412db, value : 32'h0}, //phyinit_io_write: 0x412da, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412dc, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412dd, value : 32'h2b000000}, //phyinit_io_write: 0x412dc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412de, value : 32'h0}, //phyinit_io_write: 0x412dd, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412df, value : 32'h0}, //phyinit_io_write: 0x412de, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e0, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0x170
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e1, value : 32'h0}, //phyinit_io_write: 0x412e0, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e2, value : 32'h6808}, //phyinit_io_write: 0x412e1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e3, value : 32'h0}, //phyinit_io_write: 0x412e2, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e4, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0x172
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e5, value : 32'h0}, //phyinit_io_write: 0x412e4, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e6, value : 32'ha808}, //phyinit_io_write: 0x412e5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e7, value : 32'h0}, //phyinit_io_write: 0x412e6, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412e9, value : 32'h2b000000}, //phyinit_io_write: 0x412e8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ea, value : 32'h0}, //phyinit_io_write: 0x412e9, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412eb, value : 32'h0}, //phyinit_io_write: 0x412ea, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ec, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0x176
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ed, value : 32'h0}, //phyinit_io_write: 0x412ec, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ee, value : 32'h6808}, //phyinit_io_write: 0x412ed, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ef, value : 32'h0}, //phyinit_io_write: 0x412ee, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f0, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0x178
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f1, value : 32'h0}, //phyinit_io_write: 0x412f0, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f2, value : 32'ha808}, //phyinit_io_write: 0x412f1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f3, value : 32'h0}, //phyinit_io_write: 0x412f2, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f4, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f5, value : 32'h2b000000}, //phyinit_io_write: 0x412f4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f6, value : 32'h0}, //phyinit_io_write: 0x412f5, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f7, value : 32'h0}, //phyinit_io_write: 0x412f6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f8, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0x17c
                          '{ step_type : REG_WRITE, reg_addr : 32'h412f9, value : 32'h0}, //phyinit_io_write: 0x412f8, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h412fa, value : 32'h4008}, //phyinit_io_write: 0x412f9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412fb, value : 32'h0}, //phyinit_io_write: 0x412fa, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h412fc, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0x17e
                          '{ step_type : REG_WRITE, reg_addr : 32'h412fd, value : 32'h0}, //phyinit_io_write: 0x412fc, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h412fe, value : 32'h8008}, //phyinit_io_write: 0x412fd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h412ff, value : 32'h0}, //phyinit_io_write: 0x412fe, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41300, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41301, value : 32'h2b000000}, //phyinit_io_write: 0x41300, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41302, value : 32'h0}, //phyinit_io_write: 0x41301, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41303, value : 32'h0}, //phyinit_io_write: 0x41302, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41304, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0x182
                          '{ step_type : REG_WRITE, reg_addr : 32'h41305, value : 32'h0}, //phyinit_io_write: 0x41304, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41306, value : 32'h4008}, //phyinit_io_write: 0x41305, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41307, value : 32'h0}, //phyinit_io_write: 0x41306, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41308, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x184
                          '{ step_type : REG_WRITE, reg_addr : 32'h41309, value : 32'h0}, //phyinit_io_write: 0x41308, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4130a, value : 32'h8008}, //phyinit_io_write: 0x41309, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4130b, value : 32'h0}, //phyinit_io_write: 0x4130a, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4130c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4130d, value : 32'h2b000000}, //phyinit_io_write: 0x4130c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4130e, value : 32'h0}, //phyinit_io_write: 0x4130d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4130f, value : 32'h0}, //phyinit_io_write: 0x4130e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41310, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x188
                          '{ step_type : REG_WRITE, reg_addr : 32'h41311, value : 32'h0}, //phyinit_io_write: 0x41310, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41312, value : 32'h0}, //phyinit_io_write: 0x41311, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41313, value : 32'h0}, //phyinit_io_write: 0x41312, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41314, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x18a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41315, value : 32'h0}, //phyinit_io_write: 0x41314, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41316, value : 32'h0}, //phyinit_io_write: 0x41315, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41317, value : 32'h0}, //phyinit_io_write: 0x41316, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41318, value : 32'h0}, //phyinit_io_write: 0x41317, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41319, value : 32'h0}, //phyinit_io_write: 0x41318, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4131a, value : 32'h0}, //phyinit_io_write: 0x41319, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4131b, value : 32'h0}, //phyinit_io_write: 0x4131a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h370145, value : 32'h1}, //[loadAcsmMRW] Pstate=3, Programming ACSMRptCntOverride to 1
                          '{ step_type : REG_WRITE, reg_addr : 32'h4131c, value : 32'hc9d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=19 OP=0x0 CS=0xf at row addr=0x18e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4131d, value : 32'h0}, //phyinit_io_write: 0x4131c, 0xc9d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4131e, value : 32'hc008}, //phyinit_io_write: 0x4131d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4131f, value : 32'h0}, //phyinit_io_write: 0x4131e, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41320, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41321, value : 32'h2b000000}, //phyinit_io_write: 0x41320, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41322, value : 32'h0}, //phyinit_io_write: 0x41321, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41323, value : 32'h0}, //phyinit_io_write: 0x41322, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41324, value : 32'hc958}, //[dwc_ddrphy_mr_inst] Storing MRW MA=18 OP=0x0 CS=0xf at row addr=0x192
                          '{ step_type : REG_WRITE, reg_addr : 32'h41325, value : 32'h0}, //phyinit_io_write: 0x41324, 0xc958
                          '{ step_type : REG_WRITE, reg_addr : 32'h41326, value : 32'hc008}, //phyinit_io_write: 0x41325, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41327, value : 32'h0}, //phyinit_io_write: 0x41326, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41328, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41329, value : 32'h2b000000}, //phyinit_io_write: 0x41328, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4132a, value : 32'h0}, //phyinit_io_write: 0x41329, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4132b, value : 32'h0}, //phyinit_io_write: 0x4132a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4132c, value : 32'hc0d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=1 OP=0x20 CS=0xf at row addr=0x196
                          '{ step_type : REG_WRITE, reg_addr : 32'h4132d, value : 32'h0}, //phyinit_io_write: 0x4132c, 0xc0d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4132e, value : 32'hd008}, //phyinit_io_write: 0x4132d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4132f, value : 32'h0}, //phyinit_io_write: 0x4132e, 0xd008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41330, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41331, value : 32'h2b000000}, //phyinit_io_write: 0x41330, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41332, value : 32'h0}, //phyinit_io_write: 0x41331, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41333, value : 32'h0}, //phyinit_io_write: 0x41332, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41334, value : 32'hc158}, //[dwc_ddrphy_mr_inst] Storing MRW MA=2 OP=0x22 CS=0xf at row addr=0x19a
                          '{ step_type : REG_WRITE, reg_addr : 32'h41335, value : 32'h0}, //phyinit_io_write: 0x41334, 0xc158
                          '{ step_type : REG_WRITE, reg_addr : 32'h41336, value : 32'hd108}, //phyinit_io_write: 0x41335, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41337, value : 32'h0}, //phyinit_io_write: 0x41336, 0xd108
                          '{ step_type : REG_WRITE, reg_addr : 32'h41338, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41339, value : 32'h2b000000}, //phyinit_io_write: 0x41338, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4133a, value : 32'h0}, //phyinit_io_write: 0x41339, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4133b, value : 32'h0}, //phyinit_io_write: 0x4133a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4133c, value : 32'hc1d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=3 OP=0xe CS=0xf at row addr=0x19e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4133d, value : 32'h0}, //phyinit_io_write: 0x4133c, 0xc1d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4133e, value : 32'hc708}, //phyinit_io_write: 0x4133d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4133f, value : 32'h0}, //phyinit_io_write: 0x4133e, 0xc708
                          '{ step_type : REG_WRITE, reg_addr : 32'h41340, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41341, value : 32'h2b000000}, //phyinit_io_write: 0x41340, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41342, value : 32'h0}, //phyinit_io_write: 0x41341, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41343, value : 32'h0}, //phyinit_io_write: 0x41342, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41344, value : 32'hc558}, //[dwc_ddrphy_mr_inst] Storing MRW MA=10 OP=0x54 CS=0xf at row addr=0x1a2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41345, value : 32'h0}, //phyinit_io_write: 0x41344, 0xc558
                          '{ step_type : REG_WRITE, reg_addr : 32'h41346, value : 32'hea08}, //phyinit_io_write: 0x41345, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41347, value : 32'h0}, //phyinit_io_write: 0x41346, 0xea08
                          '{ step_type : REG_WRITE, reg_addr : 32'h41348, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41349, value : 32'h2b000000}, //phyinit_io_write: 0x41348, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4134a, value : 32'h0}, //phyinit_io_write: 0x41349, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4134b, value : 32'h0}, //phyinit_io_write: 0x4134a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4134c, value : 32'hc5d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=11 OP=0x44 CS=0xf at row addr=0x1a6
                          '{ step_type : REG_WRITE, reg_addr : 32'h4134d, value : 32'h0}, //phyinit_io_write: 0x4134c, 0xc5d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4134e, value : 32'he208}, //phyinit_io_write: 0x4134d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4134f, value : 32'h0}, //phyinit_io_write: 0x4134e, 0xe208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41350, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41351, value : 32'h2b000000}, //phyinit_io_write: 0x41350, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41352, value : 32'h0}, //phyinit_io_write: 0x41351, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41353, value : 32'h0}, //phyinit_io_write: 0x41352, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41354, value : 32'h48d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0x84 CS=0x5 at row addr=0x1aa
                          '{ step_type : REG_WRITE, reg_addr : 32'h41355, value : 32'h0}, //phyinit_io_write: 0x41354, 0x48d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41356, value : 32'h4248}, //phyinit_io_write: 0x41355, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41357, value : 32'h0}, //phyinit_io_write: 0x41356, 0x4248
                          '{ step_type : REG_WRITE, reg_addr : 32'h41358, value : 32'h88d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=17 OP=0xac CS=0xa at row addr=0x1ac
                          '{ step_type : REG_WRITE, reg_addr : 32'h41359, value : 32'h0}, //phyinit_io_write: 0x41358, 0x88d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h4135a, value : 32'h9648}, //phyinit_io_write: 0x41359, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4135b, value : 32'h0}, //phyinit_io_write: 0x4135a, 0x9648
                          '{ step_type : REG_WRITE, reg_addr : 32'h4135c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4135d, value : 32'h2b000000}, //phyinit_io_write: 0x4135c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4135e, value : 32'h0}, //phyinit_io_write: 0x4135d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4135f, value : 32'h0}, //phyinit_io_write: 0x4135e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41360, value : 32'hca58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=20 OP=0x2 CS=0xf at row addr=0x1b0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41361, value : 32'h0}, //phyinit_io_write: 0x41360, 0xca58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41362, value : 32'hc108}, //phyinit_io_write: 0x41361, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41363, value : 32'h0}, //phyinit_io_write: 0x41362, 0xc108
                          '{ step_type : REG_WRITE, reg_addr : 32'h41364, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41365, value : 32'h2b000000}, //phyinit_io_write: 0x41364, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41366, value : 32'h0}, //phyinit_io_write: 0x41365, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41367, value : 32'h0}, //phyinit_io_write: 0x41366, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41368, value : 32'hcb58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=22 OP=0x0 CS=0xf at row addr=0x1b4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41369, value : 32'h0}, //phyinit_io_write: 0x41368, 0xcb58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4136a, value : 32'hc008}, //phyinit_io_write: 0x41369, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4136b, value : 32'h0}, //phyinit_io_write: 0x4136a, 0xc008
                          '{ step_type : REG_WRITE, reg_addr : 32'h4136c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4136d, value : 32'h2b000000}, //phyinit_io_write: 0x4136c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4136e, value : 32'h0}, //phyinit_io_write: 0x4136d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4136f, value : 32'h0}, //phyinit_io_write: 0x4136e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41370, value : 32'hd4d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=41 OP=0x60 CS=0xf at row addr=0x1b8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41371, value : 32'h0}, //phyinit_io_write: 0x41370, 0xd4d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h41372, value : 32'hf008}, //phyinit_io_write: 0x41371, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41373, value : 32'h0}, //phyinit_io_write: 0x41372, 0xf008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41374, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41375, value : 32'h2b000000}, //phyinit_io_write: 0x41374, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41376, value : 32'h0}, //phyinit_io_write: 0x41375, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41377, value : 32'h0}, //phyinit_io_write: 0x41376, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41378, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=58 at row addr=0x1bc
                          '{ step_type : REG_WRITE, reg_addr : 32'h41379, value : 32'h0}, //phyinit_io_write: 0x41378, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4137a, value : 32'h0}, //phyinit_io_write: 0x41379, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4137b, value : 32'h0}, //phyinit_io_write: 0x4137a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4137c, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x1be
                          '{ step_type : REG_WRITE, reg_addr : 32'h4137d, value : 32'h0}, //phyinit_io_write: 0x4137c, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4137e, value : 32'h6808}, //phyinit_io_write: 0x4137d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4137f, value : 32'h0}, //phyinit_io_write: 0x4137e, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41380, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x1c0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41381, value : 32'h0}, //phyinit_io_write: 0x41380, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h41382, value : 32'ha808}, //phyinit_io_write: 0x41381, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41383, value : 32'h0}, //phyinit_io_write: 0x41382, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41384, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41385, value : 32'h2b000000}, //phyinit_io_write: 0x41384, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41386, value : 32'h0}, //phyinit_io_write: 0x41385, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41387, value : 32'h0}, //phyinit_io_write: 0x41386, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41388, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x1c4
                          '{ step_type : REG_WRITE, reg_addr : 32'h41389, value : 32'h0}, //phyinit_io_write: 0x41388, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4138a, value : 32'h6808}, //phyinit_io_write: 0x41389, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4138b, value : 32'h0}, //phyinit_io_write: 0x4138a, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4138c, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x1c6
                          '{ step_type : REG_WRITE, reg_addr : 32'h4138d, value : 32'h0}, //phyinit_io_write: 0x4138c, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h4138e, value : 32'ha808}, //phyinit_io_write: 0x4138d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4138f, value : 32'h0}, //phyinit_io_write: 0x4138e, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41390, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41391, value : 32'h2b000000}, //phyinit_io_write: 0x41390, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41392, value : 32'h0}, //phyinit_io_write: 0x41391, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41393, value : 32'h0}, //phyinit_io_write: 0x41392, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41394, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0x1ca
                          '{ step_type : REG_WRITE, reg_addr : 32'h41395, value : 32'h0}, //phyinit_io_write: 0x41394, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h41396, value : 32'h6808}, //phyinit_io_write: 0x41395, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41397, value : 32'h0}, //phyinit_io_write: 0x41396, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h41398, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0x1cc
                          '{ step_type : REG_WRITE, reg_addr : 32'h41399, value : 32'h0}, //phyinit_io_write: 0x41398, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h4139a, value : 32'ha808}, //phyinit_io_write: 0x41399, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4139b, value : 32'h0}, //phyinit_io_write: 0x4139a, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h4139c, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h4139d, value : 32'h2b000000}, //phyinit_io_write: 0x4139c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4139e, value : 32'h0}, //phyinit_io_write: 0x4139d, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4139f, value : 32'h0}, //phyinit_io_write: 0x4139e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a0, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0x1d0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a1, value : 32'h0}, //phyinit_io_write: 0x413a0, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a2, value : 32'h6808}, //phyinit_io_write: 0x413a1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a3, value : 32'h0}, //phyinit_io_write: 0x413a2, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a4, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0x1d2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a5, value : 32'h0}, //phyinit_io_write: 0x413a4, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a6, value : 32'ha808}, //phyinit_io_write: 0x413a5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a7, value : 32'h0}, //phyinit_io_write: 0x413a6, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413a9, value : 32'h2b000000}, //phyinit_io_write: 0x413a8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413aa, value : 32'h0}, //phyinit_io_write: 0x413a9, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ab, value : 32'h0}, //phyinit_io_write: 0x413aa, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ac, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0x1d6
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ad, value : 32'h0}, //phyinit_io_write: 0x413ac, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ae, value : 32'h4008}, //phyinit_io_write: 0x413ad, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413af, value : 32'h0}, //phyinit_io_write: 0x413ae, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b0, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0x1d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b1, value : 32'h0}, //phyinit_io_write: 0x413b0, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b2, value : 32'h8008}, //phyinit_io_write: 0x413b1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b3, value : 32'h0}, //phyinit_io_write: 0x413b2, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b4, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b5, value : 32'h2b000000}, //phyinit_io_write: 0x413b4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b6, value : 32'h0}, //phyinit_io_write: 0x413b5, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b7, value : 32'h0}, //phyinit_io_write: 0x413b6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b8, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0x1dc
                          '{ step_type : REG_WRITE, reg_addr : 32'h413b9, value : 32'h0}, //phyinit_io_write: 0x413b8, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ba, value : 32'h4008}, //phyinit_io_write: 0x413b9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413bb, value : 32'h0}, //phyinit_io_write: 0x413ba, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h413bc, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x1de
                          '{ step_type : REG_WRITE, reg_addr : 32'h413bd, value : 32'h0}, //phyinit_io_write: 0x413bc, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h413be, value : 32'h8008}, //phyinit_io_write: 0x413bd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413bf, value : 32'h0}, //phyinit_io_write: 0x413be, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c1, value : 32'h2b000000}, //phyinit_io_write: 0x413c0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c2, value : 32'h0}, //phyinit_io_write: 0x413c1, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c3, value : 32'h0}, //phyinit_io_write: 0x413c2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c4, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x1e2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c5, value : 32'h0}, //phyinit_io_write: 0x413c4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c6, value : 32'h0}, //phyinit_io_write: 0x413c5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c7, value : 32'h0}, //phyinit_io_write: 0x413c6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c8, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x1e4
                          '{ step_type : REG_WRITE, reg_addr : 32'h413c9, value : 32'h0}, //phyinit_io_write: 0x413c8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ca, value : 32'h0}, //phyinit_io_write: 0x413c9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413cb, value : 32'h0}, //phyinit_io_write: 0x413ca, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413cc, value : 32'h0}, //phyinit_io_write: 0x413cb, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413cd, value : 32'h0}, //phyinit_io_write: 0x413cc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ce, value : 32'h0}, //phyinit_io_write: 0x413cd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413cf, value : 32'h0}, //phyinit_io_write: 0x413ce, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d0, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x1e8
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d1, value : 32'h0}, //phyinit_io_write: 0x413d0, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d2, value : 32'h6808}, //phyinit_io_write: 0x413d1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d3, value : 32'h0}, //phyinit_io_write: 0x413d2, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d4, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x1ea
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d5, value : 32'h0}, //phyinit_io_write: 0x413d4, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d6, value : 32'ha808}, //phyinit_io_write: 0x413d5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d7, value : 32'h0}, //phyinit_io_write: 0x413d6, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d8, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413d9, value : 32'h2b000000}, //phyinit_io_write: 0x413d8, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413da, value : 32'h0}, //phyinit_io_write: 0x413d9, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413db, value : 32'h0}, //phyinit_io_write: 0x413da, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413dc, value : 32'h4658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0x5 at row addr=0x1ee
                          '{ step_type : REG_WRITE, reg_addr : 32'h413dd, value : 32'h0}, //phyinit_io_write: 0x413dc, 0x4658
                          '{ step_type : REG_WRITE, reg_addr : 32'h413de, value : 32'h6808}, //phyinit_io_write: 0x413dd, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413df, value : 32'h0}, //phyinit_io_write: 0x413de, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e0, value : 32'h8658}, //[dwc_ddrphy_mr_inst] Storing MRW MA=12 OP=0x50 CS=0xa at row addr=0x1f0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e1, value : 32'h0}, //phyinit_io_write: 0x413e0, 0x8658
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e2, value : 32'ha808}, //phyinit_io_write: 0x413e1, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e3, value : 32'h0}, //phyinit_io_write: 0x413e2, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e4, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e5, value : 32'h2b000000}, //phyinit_io_write: 0x413e4, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e6, value : 32'h0}, //phyinit_io_write: 0x413e5, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e7, value : 32'h0}, //phyinit_io_write: 0x413e6, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e8, value : 32'h4758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0x5 at row addr=0x1f4
                          '{ step_type : REG_WRITE, reg_addr : 32'h413e9, value : 32'h0}, //phyinit_io_write: 0x413e8, 0x4758
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ea, value : 32'h6808}, //phyinit_io_write: 0x413e9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413eb, value : 32'h0}, //phyinit_io_write: 0x413ea, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ec, value : 32'h8758}, //[dwc_ddrphy_mr_inst] Storing MRW MA=14 OP=0x50 CS=0xa at row addr=0x1f6
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ed, value : 32'h0}, //phyinit_io_write: 0x413ec, 0x8758
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ee, value : 32'ha808}, //phyinit_io_write: 0x413ed, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ef, value : 32'h0}, //phyinit_io_write: 0x413ee, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f0, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f1, value : 32'h2b000000}, //phyinit_io_write: 0x413f0, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f2, value : 32'h0}, //phyinit_io_write: 0x413f1, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f3, value : 32'h0}, //phyinit_io_write: 0x413f2, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f4, value : 32'h47d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0x5 at row addr=0x1fa
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f5, value : 32'h0}, //phyinit_io_write: 0x413f4, 0x47d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f6, value : 32'h6808}, //phyinit_io_write: 0x413f5, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f7, value : 32'h0}, //phyinit_io_write: 0x413f6, 0x6808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f8, value : 32'h87d8}, //[dwc_ddrphy_mr_inst] Storing MRW MA=15 OP=0x50 CS=0xa at row addr=0x1fc
                          '{ step_type : REG_WRITE, reg_addr : 32'h413f9, value : 32'h0}, //phyinit_io_write: 0x413f8, 0x87d8
                          '{ step_type : REG_WRITE, reg_addr : 32'h413fa, value : 32'ha808}, //phyinit_io_write: 0x413f9, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413fb, value : 32'h0}, //phyinit_io_write: 0x413fa, 0xa808
                          '{ step_type : REG_WRITE, reg_addr : 32'h413fc, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h413fd, value : 32'h2b000000}, //phyinit_io_write: 0x413fc, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h413fe, value : 32'h0}, //phyinit_io_write: 0x413fd, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h413ff, value : 32'h0}, //phyinit_io_write: 0x413fe, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41400, value : 32'h4c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0x5 at row addr=0x200
                          '{ step_type : REG_WRITE, reg_addr : 32'h41401, value : 32'h0}, //phyinit_io_write: 0x41400, 0x4c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41402, value : 32'h4008}, //phyinit_io_write: 0x41401, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41403, value : 32'h0}, //phyinit_io_write: 0x41402, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41404, value : 32'h8c58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=24 OP=0x0 CS=0xa at row addr=0x202
                          '{ step_type : REG_WRITE, reg_addr : 32'h41405, value : 32'h0}, //phyinit_io_write: 0x41404, 0x8c58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41406, value : 32'h8008}, //phyinit_io_write: 0x41405, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41407, value : 32'h0}, //phyinit_io_write: 0x41406, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41408, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41409, value : 32'h2b000000}, //phyinit_io_write: 0x41408, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4140a, value : 32'h0}, //phyinit_io_write: 0x41409, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h4140b, value : 32'h0}, //phyinit_io_write: 0x4140a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4140c, value : 32'h4f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0x5 at row addr=0x206
                          '{ step_type : REG_WRITE, reg_addr : 32'h4140d, value : 32'h0}, //phyinit_io_write: 0x4140c, 0x4f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h4140e, value : 32'h4008}, //phyinit_io_write: 0x4140d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4140f, value : 32'h0}, //phyinit_io_write: 0x4140e, 0x4008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41410, value : 32'h8f58}, //[dwc_ddrphy_mr_inst] Storing MRW MA=30 OP=0x0 CS=0xa at row addr=0x208
                          '{ step_type : REG_WRITE, reg_addr : 32'h41411, value : 32'h0}, //phyinit_io_write: 0x41410, 0x8f58
                          '{ step_type : REG_WRITE, reg_addr : 32'h41412, value : 32'h8008}, //phyinit_io_write: 0x41411, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41413, value : 32'h0}, //phyinit_io_write: 0x41412, 0x8008
                          '{ step_type : REG_WRITE, reg_addr : 32'h41414, value : 32'h0}, //[dwc_ddrphy_mr_inst] dly = 5 cnt = 2
                          '{ step_type : REG_WRITE, reg_addr : 32'h41415, value : 32'h2b000000}, //phyinit_io_write: 0x41414, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41416, value : 32'h0}, //phyinit_io_write: 0x41415, 0x2b000000
                          '{ step_type : REG_WRITE, reg_addr : 32'h41417, value : 32'h0}, //phyinit_io_write: 0x41416, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41418, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x20c
                          '{ step_type : REG_WRITE, reg_addr : 32'h41419, value : 32'h0}, //phyinit_io_write: 0x41418, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4141a, value : 32'h0}, //phyinit_io_write: 0x41419, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4141b, value : 32'h0}, //phyinit_io_write: 0x4141a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4141c, value : 32'h0}, //[dwc_ddrphy_mr_clear] Reserving space for MRW MA=69 at row addr=0x20e
                          '{ step_type : REG_WRITE, reg_addr : 32'h4141d, value : 32'h0}, //phyinit_io_write: 0x4141c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4141e, value : 32'h0}, //phyinit_io_write: 0x4141d, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h4141f, value : 32'h0}, //phyinit_io_write: 0x4141e, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41420, value : 32'h0}, //phyinit_io_write: 0x4141f, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41421, value : 32'h0}, //phyinit_io_write: 0x41420, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41422, value : 32'h0}, //phyinit_io_write: 0x41421, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h41423, value : 32'h0}, //phyinit_io_write: 0x41422, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hd00e7, value : 32'h400}, //[loadAcsmMRW] End of loadAcsmMRW() inPsLoop=0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc0001, value : 32'h5821}, //phyinit_io_write: 0xd00e7, 0x400
                          '{ step_type : REG_WRITE, reg_addr : 32'h9070c, value : 32'h0}, //phyinit_io_write: 0xc0001, 0x5821
                          '{ step_type : REG_WRITE, reg_addr : 32'h9070d, value : 32'hfe}, //phyinit_io_write: 0x9070c, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h9070e, value : 32'hffff}, //phyinit_io_write: 0x9070d, 0xfe
                          '{ step_type : REG_WRITE, reg_addr : 32'h9070f, value : 32'hf040}, //phyinit_io_write: 0x9070e, 0xffff
                          '{ step_type : REG_WRITE, reg_addr : 32'h90710, value : 32'hf040}, //phyinit_io_write: 0x9070f, 0xf040
                          '{ step_type : REG_WRITE, reg_addr : 32'h90711, value : 32'h0}, //phyinit_io_write: 0x90710, 0xf040
                          '{ step_type : REG_WRITE, reg_addr : 32'h90712, value : 32'hffff}, //phyinit_io_write: 0x90711, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90713, value : 32'h0}, //phyinit_io_write: 0x90712, 0xffff
                          '{ step_type : REG_WRITE, reg_addr : 32'h90714, value : 32'h0}, //phyinit_io_write: 0x90713, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90715, value : 32'h0}, //phyinit_io_write: 0x90714, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90716, value : 32'h0}, //phyinit_io_write: 0x90715, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90717, value : 32'h0}, //phyinit_io_write: 0x90716, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90718, value : 32'h0}, //phyinit_io_write: 0x90717, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h90719, value : 32'h0}, //phyinit_io_write: 0x90718, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h9071a, value : 32'h0}, //phyinit_io_write: 0x90719, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h9071b, value : 32'h0}, //phyinit_io_write: 0x9071a, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h700f0, value : 32'hb6d}, //phyinit_io_write: 0x9071b, 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h7007e, value : 32'hc3}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programing Training Hardware Registers for mission mode retraining
                          '{ step_type : REG_WRITE, reg_addr : 32'h701ef, value : 32'h7fff}, //phyinit_io_write: 0x7007e, 0xc3
                          '{ step_type : REG_WRITE, reg_addr : 32'h300a6, value : 32'h1}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming AC0 ForceClkDisable to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h310a6, value : 32'h1}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming AC1 ForceClkDisable to 0x1
                          '{ step_type : REG_WRITE, reg_addr : 32'h701a8, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMParityInvert = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70128, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMCkeControl = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70131, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMInfiniteOLRC = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70132, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMDefaultAddr = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70133, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMDefaultCs = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70134, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMStaticCtrl = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70142, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMLowSpeedClockEnable = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'h70144, value : 32'h0}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Programming PPGC ACSMLowSpeedClockDelay = 0x0
                          '{ step_type : REG_WRITE, reg_addr : 32'hc0080, value : 32'h6}, //[dwc_ddrphy_phyinit_I_loadPIEImage] Disabling Ucclk (PMU)
                          '{ step_type : REG_WRITE, reg_addr : 32'hd0000, value : 32'h1} //[dwc_ddrphy_phyinit_I_loadPIEImage] Isolate the APB access from the internal CSRs by setting the MicroContMuxSel CSR to 1.
//[dwc_ddrphy_phyinit_MicroContMuxSel_write32] phyinit_io_write to csr MicroContMuxSel: 0xd0000, 0x1
//[dwc_ddrphy_phyinit_I_loadPIEImage] End of dwc_ddrphy_phyinit_I_loadPIEImage()
//[dwc_ddrphy_phyinit_userCustom_customPostTrain] End of dwc_ddrphy_phyinit_userCustom_customPostTrain()
   }
                  
// [dwc_ddrphy_phyinit_userCustom_J_enterMissionMode] Start of dwc_ddrphy_phyinit_userCustom_J_enterMissionMode()
// [dwc_ddrphy_phyinit_userCustom_J_enterMissionMode] End of dwc_ddrphy_phyinit_userCustom_J_enterMissionMode()
 
};
