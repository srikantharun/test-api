Module dwc_ddrphy_jtag_dfttdrs_cmd {
   ResetPort reset { ActivePolarity 0; }
   SelectPort ijtag_sel;
   ScanInPort scan_in;
   CaptureEnPort capture_en;
   ShiftEnPort shift_en;
   UpdateEnPort update_en;
   TCKPort tck;
   ScanOutPort scan_out { Source tdr[0]; }
  // DataOutPort TDR_CsrCmdChain { Source tdr[21]; Attribute connection_rule_option = "allowed_no_destination";}

   ScanInterface client {
      Port scan_in;
      Port scan_out;
      Port ijtag_sel;
   }
   ScanRegister tdr[60:0] {
      ScanInSource scan_in;
      CaptureSource 61'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      DefaultLoadValue 61'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      ResetValue 61'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
   }
}

Module dwc_ddrphy_jtag_dfttdrs_RdData {
   ResetPort reset { ActivePolarity 0; }
   SelectPort ijtag_sel;
   ScanInPort scan_in;
   CaptureEnPort capture_en;
   ShiftEnPort shift_en;
   UpdateEnPort update_en;
   TCKPort tck;
   ScanOutPort scan_out { Source tdr[0]; }
  // DataInPort TDR_RdDat[31:0] ;

   ScanInterface client {
      Port scan_in;
      Port scan_out;
      Port ijtag_sel;
   }
   ScanRegister tdr[31:0] {
      ScanInSource scan_in;
      CaptureSource 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      DefaultLoadValue 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      ResetValue 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
   }
}
