#+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
# clock definitions for soc_periph_p in shift mode
# File is generated on Thu Jan 30 10:57:05 UTC 2025
# This file containts clocks defined only on ports
# To be used during soc_periph_p block_build and STA only
#+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#


#Defining ijtag_tck
set cip_coll ""
append_to_coll cip_coll [get_ports "tck"]
create_clock -add -name ijtag_tck -period 10.000 -waveform {0 5.0000} $cip_coll

#Defining test_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "test_clk"]
create_clock -add -name test_clk -period 10.000 -waveform {0 5.0000} $cip_coll

#Defining emmc_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "i_emmc_clk"]
create_clock -add -name emmc_clk -period 10.000 -waveform {0 5.0000} $cip_coll

#Defining periph_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "i_periph_clk"]
create_clock -add -name periph_clk -period 10.000 -waveform {0 5.0000} $cip_coll
