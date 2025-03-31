
Module dwc_c20pcie4_upcs_x4_ns_x4_x4_pipe {

   TCKPort phy0_jtag_tck;
   ScanInPort phy0_jtag_tdi {
      Attribute tessent_use_in_dft_specification = "false";
   }
   ScanOutPort phy0_jtag_tdo {
      Source jtag_ctl.jtag_tdo;
      Attribute forced_low_dft_signal_list = "tms_disable";
   }
   TMSPort phy0_jtag_tms {
      Attribute forced_low_dft_signal_list = "tms_disable";
   }
   TRSTPort phy0_jtag_trst_n {
      Attribute connection_rule_option = "allowed_tied_high";
   }

   Instance jtag_ctl Of DWC_pcie_phy_top_jtag_ctl {
      InputPort jtag_clk       = phy0_jtag_tck;
      InputPort jtag_tdi       = phy0_jtag_tdi;
      InputPort jtag_tms       = phy0_jtag_tms;
      InputPort jtag_trst_n    = phy0_jtag_trst_n;
      InputPort jtag_crsel_tdo = creg_ctl.jtag_crsel_tdo;
   }
   Instance creg_ctl Of DWC_pcie_phy_top_creg_ctl {
      InputPort jtag_rst     = phy0_jtag_trst_n;
      InputPort jtag_ser_in  = phy0_jtag_tdi;
      InputPort jtag_capture = jtag_ctl.jtag_capture;
      InputPort jtag_shift   = jtag_ctl.jtag_shift;
      InputPort jtag_update  = jtag_ctl.jtag_update;
      InputPort jtag_clk     = phy0_jtag_tck;
   }

   Attribute keep_active_during_scan_test = "false";
}

Module DWC_pcie_phy_top_jtag_ctl {
   TCKPort jtag_clk;
   ScanInPort jtag_tdi;
   ScanOutPort jtag_tdo {
      Source IRMux;
      Attribute forced_low_output_port_list = "jtag_tdo_en";
      Attribute forced_low_dft_signal_list = "tms_disable";
   }
   TMSPort jtag_tms {
      Attribute forced_low_dft_signal_list = "tms_disable";
   }
   TRSTPort jtag_trst_n {
      Attribute connection_rule_option = "allowed_tied_high";
   }
   ToCaptureEnPort jtag_capture;
   ToShiftEnPort jtag_shift;
   ToUpdateEnPort jtag_update;
   ToResetPort jtag_rst {
      ActivePolarity 0;
   }
   ToSelectPort jtag_crsel_sel {
      Source jtag_crsel_sel_int;
      Attribute connection_rule_option = "allowed_no_destination";
   }
   ScanInPort jtag_crsel_tdo {
      Attribute connection_rule_option = "allowed_no_source";
   }
   ScanInterface tap_client {
      Port jtag_tdi;
      Port jtag_tdo;
      Port jtag_tms;
   }
   ScanInterface crsel_sel_ijtag {
      Port jtag_crsel_tdo;
      Port jtag_crsel_sel;
   }
   Enum state_encoding {
      test_logic_reset = 4'b1111;
      run_test_idle = 4'b1100;
      select_dr = 4'b0111;
      capture_dr = 4'b0110;
      shift_dr = 4'b0010;
      exit1_dr = 4'b0001;
      pause_dr = 4'b0011;
      exit2_dr = 4'b0000;
      update_dr = 4'b0101;
      select_ir = 4'b0100;
      capture_ir = 4'b1110;
      shift_ir = 4'b1010;
      exit1_ir = 4'b1001;
      pause_ir = 4'b1011;
      exit2_ir = 4'b1000;
      update_ir = 4'b1101;
   }
   Enum instruction_opcodes {
      BYPASS = 8'b11111111;
      IDCODE = 8'b00000001;
      CLAMP = 8'b00000010;
      EXTEST = 8'b00000011;
      EXTEST_PULSE = 8'b00000100;
      EXTEST_TRAIN = 8'b00000101;
      INTEST = 8'b00000110;
      SAMPLE = 8'b00000111;
      PRELOAD = 8'b00001000;
      HIGHZ = 8'b00001001;
      CRSEL = 8'b00110001;
   }
   ScanRegister instruction[7:0] {
      ScanInSource jtag_tdi;
      CaptureSource 8'b00000001;
      ResetValue 8'b00000001;
      RefEnum instruction_opcodes;
   }
   ScanRegister bypass {
      ScanInSource jtag_tdi;
      CaptureSource 1'b0;
   }
   ScanRegister idcode[31:0] {
      ScanInSource jtag_tdi;
      CaptureSource 32'b00010001010001000111010011001101;
   }
   ScanMux IRMux SelectedBy fsm.irSel {
      1'b0 : DRMux;
      1'b1 : instruction[0];
   }
   ScanMux DRMux SelectedBy instruction {
      8'b11111111 : bypass;
      8'b00110001 : jtag_crsel_tdo;
      8'b00000001 : idcode[0];
   }
   LogicSignal jtag_crsel_sel_int {
      instruction == CRSEL;
   }
   Instance fsm Of DWC_pcie_phy_top_jtag_fsm {
      InputPort tck = jtag_clk;
      InputPort tms = jtag_tms;
      InputPort trst_n = jtag_trst_n;
   }
   Attribute keep_active_during_scan_test = "false";
}

Module DWC_pcie_phy_top_jtag_fsm {
   TCKPort tck;
   TMSPort tms;
   TRSTPort trst_n;
   ToIRSelectPort irSel;
   ToResetPort jtag_rst;
}


Module DWC_pcie_phy_top_creg_ctl {
   ResetPort jtag_rst {
      ActivePolarity 0;
   }
   SelectPort jtag_crsel_sel;
   ScanInPort jtag_ser_in;
   CaptureEnPort jtag_capture;
   ShiftEnPort jtag_shift;
   UpdateEnPort jtag_update;
   TCKPort jtag_clk;
   ScanOutPort jtag_crsel_tdo {
      Source data[0];
   }
   ScanInterface inf1 {
      Port jtag_ser_in;
      Port jtag_crsel_tdo;
   }

   ScanRegister data[17:0] {
      ScanInSource jtag_ser_in;
      CaptureSource 18'bxxxxxxxxxxxxxxxxxx;
      DefaultLoadValue 18'b000000000000000000;
      ResetValue 18'b000000000000000000;
   }
   Attribute keep_active_during_scan_test = "false";

}
