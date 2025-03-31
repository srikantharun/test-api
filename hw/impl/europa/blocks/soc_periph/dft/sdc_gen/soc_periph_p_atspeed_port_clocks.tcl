#+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
# clock definitions for soc_periph_p in atspeed mode
# File is generated on Thu Jan 30 10:57:05 UTC 2025
# This file containts clocks defined only on ports
# To be used during soc_periph_p block_build and STA only
#+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#


#Defining ijtag_tck
set cip_coll ""
append_to_coll cip_coll [get_ports "ijtag_tck"]
create_clock -add -name ijtag_tck -period 10.000 -waveform {0 5.0000} $cip_coll

#Defining test_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "test_clk"]
create_clock -add -name test_clk -period 10.000 -waveform {0 5.0000} $cip_coll

#Defining bisr_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "bisr_clk"]
create_clock -add -name bisr_clk -period 20.000 -waveform {0 10.0000} $cip_coll

#Defining emmc_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "i_emmc_clk"]
create_clock -add -name emmc_clk -period 5.000 -waveform {0 2.5000} $cip_coll

#Defining periph_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "i_periph_clk"]
create_clock -add -name periph_clk -period 10.000 -waveform {0 5.0000} $cip_coll

#Defining i2c_0_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "i_i2c_0_clk"]
create_clock -add -name i2c_0_clk -period 100.000 -waveform {0 50.0000} $cip_coll

#Defining i2c_1_clk
set cip_coll ""
append_to_coll cip_coll [get_ports "i_i2c_1_clk"]
create_clock -add -name i2c_1_clk -period 100.000 -waveform {0 50.0000} $cip_coll
