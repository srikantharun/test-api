#!/usr/bin/env python3

#model dwc_lpddr5xphy_top
#  (
#  <snip>"all-ios"<snip>
#  )(
#  model_source = verilog_module;
#mode(
#  inout (BP_D[1]) (pad_pad_io; )
#  output (BypassInDataDAT[1]) (pad_from_pad; )
#  input  (BypassOutDataDAT[1]) (pad_to_pad; )
#  input  (BypassOutEnDAT[1]) (pad_enable_high; )
#)
#mode(
#  inout (BP_D[2]) (pad_pad_io; )
#  output (BypassInDataDAT[2]) (pad_from_pad; )
#  input  (BypassOutDataDAT[2]) (pad_to_pad; )
#  input  (BypassOutEnDAT[2]) (pad_enable_high; )
#)
#)

#:/data/foundry/LIB/synopsys/lpddr5x/v_roel/Europa_lpddr_phy_config/src/dwc_lpddr5xphy_top.v


#  inout (BP_A) (array = 19 : 0; )
#  inout (BP_B0_D) (array = 12 : 0; )
#  inout (BP_B1_D) (array = 12 : 0; )
#  inout (BP_B2_D) (array = 12 : 0; )
#  inout (BP_B3_D) (array = 12 : 0; )
#  inout (BP_CK0_T) ( )
#  inout (BP_CK0_C) ( )
#  inout (BP_CK1_T) ( )
#  inout (BP_CK1_C) ( )
#  inout (BP_ATO) ( )
#  inout (BP_ATO_PLL) ( )
#  inout (BP_ZN) ( )

for x in range(20):
    print("   mode(                                                   ")
    print("     inout (BP_A["+str(x)+"])             (pad_pad_io;      )    ")
    print("     output (RxBypassDataPad_A["+str(x)+"]) (pad_from_pad;    )    ")
    print("     input  (TxBypassData_A["+str(x)+"])    (pad_to_pad;      )    ")
    print("     input  (TxBypassOE_A["+str(x)+"])      (pad_enable_high; )    ")
    print("   )                                                        ")

print("")
print("")

for y in range(4):
    for x in range(13):
        print("   mode(                                                   ")
        print("     inout (BP_B"+str(y)+"_D["+str(x)+"])             (pad_pad_io;      )    ")
        print("     output (RxBypassDataPad_B"+str(y)+"_D"+str(x)+") (pad_from_pad;    )    ")
        print("     input  (TxBypassData_B"+str(y)+"_D"+str(x)+")    (pad_to_pad;      )    ")
        print("     input  (TxBypassOE_B"+str(y)+"_D"+str(x)+")      (pad_enable_high; )    ")
        print("   )                                                       ")

print("")
print("")

for x in ["T", "C"]:
    for y in range(2):
        print("   mode(                                                   ")
        print("     inout (BP_CK"+str(y)+"_"+x+")                  (pad_pad_io;      )    ")
        print("     output (RxBypassDataPad_CK"+str(y)+"_"+x+")    (pad_from_pad;    )    ")
        print("     input  (TxBypassData_CK"+str(y)+"_"+x+")       (pad_to_pad;      )    ")
        print("     input  (TxBypassOE_CK"+str(y)+"_"+x+")         (pad_enable_high; )    ")
        print("   )                                                       ")


print("")
print("")
print("   mode(      ")
print("      output (BP_MEMRESET_L)              (pad_pad_io;)")
print("      input  (TxBypassData_MEMRESET_L)    (pad_to_pad;)")
print("   )                                                   ")
