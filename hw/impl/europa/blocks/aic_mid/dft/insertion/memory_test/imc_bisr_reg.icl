//--------------------------------------------------------------------------
//
//  Unpublished work. Copyright 2024 Siemens
//
//  This material contains trade secrets or otherwise confidential 
//  information owned by Siemens Industry Software Inc. or its affiliates 
//  (collectively, SISW), or its licensors. Access to and use of this 
//  information is strictly limited as set forth in the Customer's 
//  applicable agreements with SISW.
//
//--------------------------------------------------------------------------
//  File created by: Tessent Shell
//          Version: 2024.2
//       Created on: Tue Oct  8 11:05:49 UTC 2024
//--------------------------------------------------------------------------

Module imc_bisr_reg {
    CaptureEnPort    CLK  {Attribute function_modifier = "CaptureShiftClock"; Attribute connection_rule_option = "allowed_tied_low";} 
    DataInPort       RSTB {Attribute connection_rule_option = "allowed_tied_low"; Attribute tessent_no_input_constraints = "on"; DefaultLoadValue 1'b1; Attribute associated_scan_interface = "bisr"; Attribute tessent_bisr_function = "Reset";} 
    DataInPort       MSEL {Attribute connection_rule_option = "allowed_tied_low"; Attribute tessent_no_input_constraints = "on";} 
    ScanInPort       SI   {Attribute connection_rule_option = "allowed_tied_low";}
    ScanOutPort      SO   {Attribute launch_edge = "falling"; Source ShiftReg[0]; Attribute connection_rule_option = "allowed_no_destination";}
    ShiftEnPort      SE   {Attribute connection_rule_option = "allowed_tied_low";}
    DataOutPort      Q[31:0] { Source ShiftReg[31:0]; Attribute connection_rule_option = "allowed_no_destination"; }
    DataInPort       D[31:0] { Attribute connection_rule_option = "allowed_no_source"; }
    Enum ScanRegisterSymbols {
      leading_one    = 32'b00000000000000000000000000000001;
      all_zero       = 32'b00000000000000000000000000000000;
      all_one        = 32'b11111111111111111111111111111111;
      all_x          = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      checkerboard   = 32'b10101010101010101010101010101010;
      inverse_checkerboard               = 32'b01010101010101010101010101010101;
    }
    ScanMux RSTB_MUX SelectedBy RSTB {
      1'b1 : SI;
    }
    ScanRegister ShiftReg[31:0] {
        DefaultLoadValue                 all_zero;
        CaptureSource                    D[31:0];
        ScanInSource                     RSTB_MUX;
        RefEnum                          ScanRegisterSymbols;
    }
    ScanInterface bisr {
        Attribute tessent_chain_type   = "bisr";
        Attribute tessent_chain_length = 32;
        Port SI;
        Port SO;
        Port SE;
        Port CLK;
    }
    Attribute tessent_bisr_register_length = 32;
    Attribute tessent_instrument_type = "mentor::memory_bisr";
    Attribute tessent_repair_word_size = 32;
    Attribute tessent_instrument_subtype = "repair_register";
    Attribute tessent_use_in_dft_specification = "false";
    Attribute tessent_signature = "b0bb0687629ff313e0df36aae1540b50";
    Attribute tessent_ignore_during_icl_verification = "on";
}
