# Driver for U250 APU, Xilinx BSCANE taps.
adapter driver ftdi
transport select jtag

ftdi vid_pid 0x0403 0x6011

ftdi layout_init 0x2088 0x3f8b
ftdi layout_signal nSRST -data 0x2000
ftdi layout_signal GPIO2 -data 0x2000
ftdi layout_signal GPIO1 -data 0x0200
ftdi layout_signal GPIO0 -data 0x0100

set _CHIPNAME riscv
# This requires a fair amount of fiddling, especially because the Alveo cards
# are basically undocumented.
# This is the UltraScale(+) guide https://docs.xilinx.com/r/en-US/ug570_7Series_Config/Instruction-Register
# IDCodes are here: https://docs.xilinx.com/r/en-US/ug570_7Series_Config/Device-Resources-and-Configuration-Bitstream-Lengths?section=XREF_95491_JTAG_and_IDCODE
# From there you can see that 6, 12, 18, or 24 are possible. Trial and error brought us to 24.
jtag newtap $_CHIPNAME cpu -irlen 24 -expected-id 0x04b57093

set _TARGETNAME $_CHIPNAME.cpu
target create $_TARGETNAME riscv -chain-position $_TARGETNAME -coreid 0x0

gdb_port pipe
tcl_port disabled
telnet_port disabled

# The User registers shift based on the IR Length. MSB:MSB-IRLength.
# USER3_INSTR    = 24'b100010100100100100100100
# USER4_INSTR    = 24'b100011100100100100100100
riscv set_ir idcode 0x249249
riscv set_ir dtmcs 0x8A4924
riscv set_ir dmi 0x8E4924

adapter speed 1000
