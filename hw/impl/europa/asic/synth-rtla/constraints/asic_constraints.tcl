# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Luyi <yi.lu@axelera.ai>

# clock & reset

# clk period
set refClkPeriod = 50 # 20MHz
set tckPeriod = 10 # 100MHz
set testClkPeriod = 10 # 100MHz

create_clock -name ref_clk -period $refClkPeriod [get_ports {i_ref_clk}]
create_clock -name tck -period $tckPeriod [get_ports {i_tck}]
create_clock -name test_clk -period $tckPeriod [get_ports {i_test_clk}]

set_clock_uncertainty -setup [expr ${refClkPeriod} * 0.05 ] [get_clocks {i_ref_clk}]
set_clock_uncertainty -hold 0.010 [get_clocks {i_ref_clk}]

set_clock_uncertainty -setup [expr ${tckPeriod} * 0.05 ] [get_clocks {i_tck}]
set_clock_uncertainty -hold 0.010 [get_clocks {i_tck}]

set_clock_uncertainty -setup [expr ${testClkPeriod} * 0.05 ] [get_clocks {i_test_clk}]
set_clock_uncertainty -hold 0.010 [get_clocks {i_test_clk}]

# reset
set_false_path -from [get_ports {i_por_rst_n}]
set_false_path -from [get_ports {i_button_rst_n}]
set_false_path -from [get_ports {i_pcie_button_rst_n}]
set_false_path -from [get_ports {i_trst_n}]
