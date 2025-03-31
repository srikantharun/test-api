Module esecure_jtag {
  TCKPort         TCK;
  ScanInPort      TDI;
  ScanOutPort     TDO_OUT    { Source IRMux;}
  TMSPort         TMS    ;
  TRSTPort        nTRST   {
    Attribute connection_rule_option = "allowed_tied_high";
  }
  ScanInterface tap_client { 
    Port TDI; 
    Port TDO_OUT; 
    Port TMS;
  }
  Instance fsm Of fsm_o  {
    InputPort tck  = TCK;
    InputPort tms  = TMS;
    InputPort trst = nTRST;
  }
  ScanRegister instruction[3:0] {
    CaptureSource  4'bxxxx;
    ResetValue     4'b0001;
    ScanInSource   TDI;
    RefEnum        instruction_opcodes;
  }
  Enum instruction_opcodes {
    BYPASS            = 4'b1111;
    IDCODE 	      = 4'b0001;
    DATA 	      = 4'b0000;
    GRANT 	      = 4'b0010;
  }
  ScanRegister bypass       {    CaptureSource  1'b0;    ScanInSource   TDI;  }
  ScanRegister idcode[31:0] {    CaptureSource  32'b00011010001010110011110001001101;    ScanInSource   TDI;  }
  ScanRegister data[33:0]   {    CaptureSource  34'b0;    ScanInSource   TDI;  }
  ScanRegister grant[15:0]  {    CaptureSource  16'b0;    ScanInSource   TDI;  }

  Alias RD_EN            = data[33];
  Alias WR_EN            = data[32];
  Alias DBG_DATA[31:0]   = data[31:0];

  ScanMux IRMux SelectedBy fsm.irSel {
    1'b0 : DRMux;
    1'b1 : instruction[0];
  }
  ScanMux DRMux SelectedBy instruction {
    4'b1111           : bypass;
    4'b0001           : idcode[0];
    4'b0000           : data[0];
    4'b0010           : grant[0];
  }
}





Module n22_dtm_tap {

  TCKPort         tck;
  ScanInPort      tdi;
  TRSTPort        pwr_rst_n   {    Attribute connection_rule_option = "allowed_tied_high";  }
  ScanOutPort     tdo    { Source IRMux;}
  TMSPort         tms    ;
  LocalParameter  DMI_DATA_BITS  = 32;
  LocalParameter  DMI_ADDR_BITS  = 7;
  LocalParameter  DMI_OP_BITS    = 2;
  LocalParameter  DMI_REG_BITS = $DMI_DATA_BITS + $DMI_ADDR_BITS + $DMI_OP_BITS ;
  
  ScanInterface tap_client { 
    Port tdi; 
    Port tdo; 
    Port tms;
  }
  Instance fsm Of fsm_mm  {
    InputPort tck  = tck;
    InputPort tms  = tms;
    InputPort pwr_rst_n = pwr_rst_n;
  }
  ScanRegister instruction[4:0] {
    CaptureSource  5'bxxxxx;
    ResetValue     5'b00001;
    ScanInSource   tdi;
    RefEnum        instruction_opcodes;
  }
  Enum instruction_opcodes {
    BYPASS            = 5'b11111;
    IDCODE 	      = 5'b00001;
    DTM_CTRL_ST	      = 5'b10000;
    DMI_ACCESS	      = 5'b10001;

  }
  ScanRegister bypass                   { CaptureSource  1'b0; ScanInSource   tdi; }
  ScanRegister idcode[31:0]             { CaptureSource  32'b00010000000000000101011000111101;    ScanInSource   tdi;  }
  ScanRegister dmi[$DMI_REG_BITS-1:0]   { CaptureSource  $DMI_REG_BITS'bx; ScanInSource   tdi; }

  Alias dmi_addr[$DMI_ADDR_BITS-1:0]   = dmi[($DMI_REG_BITS-1):($DMI_DATA_BITS+$DMI_OP_BITS)];
  Alias dmi_data[$DMI_DATA_BITS-1:0]   = dmi[($DMI_DATA_BITS+$DMI_OP_BITS)-1:$DMI_OP_BITS];
  Alias dmi_op[$DMI_OP_BITS-1:0]       = dmi[$DMI_OP_BITS-1:0];

  ScanMux IRMux SelectedBy fsm.irSel {
    1'b0 : DRMux;
    1'b1 : instruction[0];
  }
  ScanMux DRMux SelectedBy instruction {
    5'b11111           : bypass;
    5'b00001           : idcode[0];
    5'b10001           : dmi[0];
  }

}

Module fsm_mm {
  TCKPort        tck;
  TMSPort        tms;
  TRSTPort       pwr_rst_n;
  ToIRSelectPort irSel;
  ToResetPort    tlr;
}

Module ncejdtm200_tap {

  TCKPort         tck;
  ScanInPort      tdi;
  TRSTPort        pwr_rst_n   {    Attribute connection_rule_option = "allowed_tied_high";  }
//  ScanOutPort     tdo    { Source IRMux;}
  ScanOutPort         tdo { 
    Source            IRMux; 
    Attribute         forced_high_output_port_list = "tdo_out_en";
  }

  TMSPort         tms    ;
  LocalParameter  DMI_DATA_BITS  = 32;
  LocalParameter  DMI_ADDR_BITS  = 7;
  LocalParameter  DMI_OP_BITS    = 2;
  LocalParameter  DMI_REG_BITS = $DMI_DATA_BITS + $DMI_ADDR_BITS + $DMI_OP_BITS ;
  
  ScanInterface tap_client { 
    Port tdi; 
    Port tdo; 
    Port tms;
  }
  Instance fsm Of fsm_m  {
    InputPort tck  = tck;
    InputPort tms  = tms;
    InputPort pwr_rst_n = pwr_rst_n;
  }
  ScanRegister instruction[4:0] {
    CaptureSource  5'bxxxxx;
    ResetValue     5'b00001;
    ScanInSource   tdi;
    RefEnum        instruction_opcodes;
  }
  Enum instruction_opcodes {
    BYPASS            = 5'b11111;
    IDCODE 	      = 5'b00001;
    DTM_CTRL_ST	      = 5'b10000;
    DMI_ACCESS	      = 5'b10001;

  }
  ScanRegister bypass                   { CaptureSource  1'b0; ScanInSource   tdi; }

  ScanRegister idcode[31:0]             { CaptureSource  32'b00010000000000000101011000111101;    ScanInSource   tdi;  }

  ScanRegister dmi[$DMI_REG_BITS-1:0]    { CaptureSource  $DMI_REG_BITS'bx; ScanInSource   tdi; }

  Alias dmi_addr[$DMI_ADDR_BITS-1:0]   = dmi[($DMI_REG_BITS-1):($DMI_DATA_BITS+$DMI_OP_BITS)];
  Alias dmi_data[$DMI_DATA_BITS-1:0]   = dmi[($DMI_DATA_BITS+$DMI_OP_BITS)-1:$DMI_OP_BITS];
  Alias dmi_op[$DMI_OP_BITS-1:0]       = dmi[$DMI_OP_BITS-1:0];

  ScanMux IRMux SelectedBy fsm.irSel {
    1'b0 : DRMux;
    1'b1 : instruction[0];
  }
  ScanMux DRMux SelectedBy instruction {
    5'b11111           : bypass;
    5'b00001           : idcode[0];
    5'b10001           : dmi[0];
  }

}

Module fsm_m {
  TCKPort        tck;
  TMSPort        tms;
  TRSTPort       pwr_rst_n;
  ToIRSelectPort irSel;
  ToResetPort    tlr;
}

//Module DW_tap {
//  TCKPort         tck;
//  ScanInPort      tdi;
//  ScanOutPort     tdo    { Source IRMux;}
//  TMSPort         tms    ;
//  TRSTPort        trst_n   {
//    Attribute connection_rule_option = "allowed_tied_high";
//  }
//  ScanInterface tap_client { 
//    Port tdi; 
//    Port tdo; 
//    Port tms;
//  }
//  Instance fsm Of fsm_n  {
//    InputPort tck  = tck;
//    InputPort tms  = tms;
//    InputPort trst = trst_n;
//  }
//  ScanRegister instruction[1:0] {
//    CaptureSource  2'bxx;
//    ResetValue     2'b11;
//    ScanInSource   tdi;
//    RefEnum        instruction_opcodes;
//  }
//  Enum instruction_opcodes {
//    BYPASS            = 2'b11;
//    PLL_TDR           = 2'b10;
//  }
//  ScanRegister bypass {
//    CaptureSource  1'bx;
//    ScanInSource   tdi;
//  }
//  ScanRegister pll_tdr[442:0] {
//    CaptureSource  443'bx;
//    ScanInSource   tdi;
//  }
//  ScanMux IRMux SelectedBy fsm.irSel {
//    1'b0 : DRMux;
//    1'b1 : instruction[0];
//  }
//  ScanMux DRMux SelectedBy instruction {
//    2'b11           : bypass;
//    2'b10           : pll_tdr[0];
//  }
//}

Module fsm_n {
  TCKPort        tck;
  TMSPort        tms;
  TRSTPort       trst;
  ToIRSelectPort irSel;
  ToResetPort    tlr;
}


Module srv_1_tap {
  TCKPort         tck;
  ScanInPort      tdi;
  ScanOutPort     tdo    { Source IRMux;}
  TMSPort         tms    ;
  TRSTPort        trstn   {
    Attribute connection_rule_option = "allowed_tied_high";
  }
  ScanInterface tap_client { 
    Port tdi; 
    Port tdo; 
    Port tms;
  }
  Instance fsm Of fsm_o  {
    InputPort tck  = tck;
    InputPort tms  = tms;
    InputPort trst = trstn;
  }
  ScanRegister instruction[2:0] {
    CaptureSource  3'bxxx;
    ResetValue     3'b000;
    ScanInSource   tdi;
    RefEnum        instruction_opcodes;
  }
  Enum instruction_opcodes {
    BYPASS            = 3'b111;
    IDCODE            = 3'b001;
  }
  ScanRegister bypass {
    CaptureSource  1'b0;
    ScanInSource   tdi;
  }

  ScanRegister idcode[31:0]             { CaptureSource  32'b01100000101101011101001100110100;    ScanInSource   tdi;  }

  ScanMux IRMux SelectedBy fsm.irSel {
    1'b0 : DRMux;
    1'b1 : instruction[0];
  }
  ScanMux DRMux SelectedBy instruction {
    3'b111           : bypass;
    3'b001           : idcode[0];
  }
}

Module fsm_o {
  TCKPort        tck;
  TMSPort        tms;
  TRSTPort       trst;
  ToIRSelectPort irSel;
  ToResetPort    tlr;
}


Module ABJWTBR2 {
   Attribute tessent_clock_type = "generated"; 
   ClockPort    REF;
   ToClockPort  PLLOUT1 {  Source   REF;
                           FreqMultiplier 1; }
   ToClockPort  PLLOUT2 {  Source   REF;
                           FreqMultiplier 1; }
   ToClockPort  PLLOUT3 {  Source   REF;
                           FreqMultiplier 1; }
   ToClockPort  PLLOUT4 {  Source   REF;
                           FreqMultiplier 1; }
	   
//Using allowed_no_source/destination for everything as there are no Tessent TDR overrides
//
//  DataOutPort        LOCK  { Attribute connection_rule_option = "allowed_no_destination" };
//
//  DataInPort         FB  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         FSE  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         BYPASS  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Bypass - Active HIGH
//  DataInPort         ENABLE4  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Enable for PLLOUT4 - Active HIGH
//  DataInPort         ENABLE3  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Enable for PLLOUT3 - Active HIGH
//  DataInPort         ENABLE2  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Enable for PLLOUT2 - Active HIGH
//  DataInPort         ENABLE1  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Enable for PLLOUT1 - Active HIGH
//  DataInPort         RESET  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Reset  - Active HIGH
//  DataInPort         DIVF8  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Feedback Divider Control
//  DataInPort         DIVF7  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF6  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF5  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF4  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF3  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF2  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF1  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVF0  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVR5  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Reference Divider Control
//  DataInPort         DIVR4  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVR3  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVR2  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVR1  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVR0  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ2  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Pre-Output Divider Control
//  DataInPort         DIVQ1  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ0  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ43  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Output divider value for PLLOUT4
//  DataInPort         DIVQ42  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ41  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ40  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ33  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Output divider value for PLLOUT3
//  DataInPort         DIVQ32  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ31  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ30  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ23  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Output divider value for PLLOUT2
//  DataInPort         DIVQ22  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ21  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ20  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ13  { Attribute connection_rule_option = "allowed_no_source" } ; 	// Output divider value for PLLOUT1
//  DataInPort         DIVQ12  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ11  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         DIVQ10  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         RANGE2  { Attribute connection_rule_option = "allowed_no_source" } ; 	// RANGE pins
//  DataInPort         RANGE1  { Attribute connection_rule_option = "allowed_no_source" } ; 
//  DataInPort         RANGE0  { Attribute connection_rule_option = "allowed_no_source" } ; 
		
  	   
}
