# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Andrew Dickson <andrew.dickson@axelera.ai>
#
# Sanity constaints for soc_mgmt IP
#
################################################################################
# Clock period specifications
# 50MHz
set RefClockPeriod        20.0
# 100MHz
set JtagClockPeriod       10.0
set SsnClockperiod        10.0
set BisrClockperiod       10.0

# Fast clock
set Pll0Period             0.8
# APU clock
set Pll1Period             0.8
# DDR Ref clock
set Pll2Period             1.2

################################################################################
# Clock Declarations
#                 clk port
#                     |                  period
#                     |                     |                 clk name
#                     |                     |                    |
#                     V                     v                    v
set inputClocks {
                 {i_ref_clk            $RefClockPeriod        i_ref_clk           }
                 {tck                  $JtagClockPeriod       tck                 }
                 {ssn_bus_clk          $SsnClockperiod        ssn_bus_clk         }
                 {bisr_clk             $BisrClockperiod       bisr_clk            }
                }

set pllClocks   {
                 {u_soc_mgmt/u_soc_mgmt_clk_gen/gen_plls[0].u_pll_wrapper/o_pll_fout  $Pll0Period pll0_clk}
                 {u_soc_mgmt/u_soc_mgmt_clk_gen/gen_plls[1].u_pll_wrapper/o_pll_fout  $Pll1Period pll1_clk}
                 {u_soc_mgmt/u_soc_mgmt_clk_gen/gen_plls[2].u_pll_wrapper/o_pll_fout  $Pll2Period pll2_clk}
                }

################################################################################
# Divided clock def
#                       clk pin index
#                          |          divide
#                          |             |   clock name
#                          |             |       |
#                          v             v       v
set Pll0_Pll1_DivClocks {
                          {0             1 o_fast_clk   }
                          {1             1 o_apu_clk    }
                          {3             6 o_emmc_clk   }
                          {2             2 o_codec_clk  }
                          {4            12 o_periph_clk }
                          {5           150 o_pvt_clk    }
}

################################################################################
# Input Resets
set ResetPorts {
                i_por_rst_n
               }

# internal resets
set GeneratedResets {
  u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[0].u_reset_gen_basic_block_rst/o_rst_n
  u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[0].u_reset_gen_basic_block_rst/o_rst_ip_n[0]
  u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[1].u_reset_gen_basic_block_rst/o_rst_n
  u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[1].u_reset_gen_basic_block_rst/o_rst_ip_n[0]
  u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[2].u_reset_gen_basic_block_rst/o_rst_n
  u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[2].u_reset_gen_basic_block_rst/o_rst_ip_n[0]
}

################################################################################
# IOs
set AsyncInputs  " "
set AsyncOutputs " "

################################################################################
# CLOCKS
####################################
# Input clocks
foreach clkin $inputClocks {
  lassign $clkin portName period clockName

  create_clock -add [get_ports ${portName}] -name ${clockName} -period [format %.4f [expr ${period}]] -waveform "0 [expr ${period}/2]"
  set_clock_uncertainty -setup [expr ${period} * 0.05 ] [get_clocks ${clockName}]
  set_clock_uncertainty -hold 0.010 [get_clocks ${clockName}]
  set_clock_groups -asynchronous -name ${clockName}_async -group ${clockName}
}

####################################
# PLL Clocks
foreach clkpll $pllClocks {
  lassign $clkpll portName period clockName

  create_clock -add [get_pins ${portName}] -name ${clockName} -period [format %.4f [expr ${period}]] -waveform "0 [expr ${period}/2]"
  set_clock_uncertainty -setup [expr ${period} * 0.05 ] [get_clocks ${clockName}]
  set_clock_uncertainty -hold 0.010 [get_clocks ${clockName}]
  set_clock_groups -asynchronous -name ${clockName}_async -group ${clockName}
}

####################################
# Create all generated clocks stemming from PLL0 and PLL1

foreach divclk $Pll0_Pll1_DivClocks {
  lassign $divclk index division clockName

  set div_in_pin      "u_soc_mgmt/u_soc_mgmt_clk_gen/gen_clk_mux[$index].u_axe_ccl_clk_div_by_int/u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div_u_tc_lib_clk_mux/S0"
  set div_out_pin     "u_soc_mgmt/u_soc_mgmt_clk_gen/gen_clk_mux[$index].u_axe_ccl_clk_div_by_int/u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div_u_tc_lib_clk_mux/Y"

  create_generated_clock -name ${clockName} [get_pins ${div_out_pin}] -source $div_in_pin -divide_by "[expr ${division}]" -combinational
  set_clock_groups -asynchronous -group ${clockName}
}

####################################
# OTP generated clock (analog only)
create_generated_clock -name otp_analog_clk -source "i_ref_clk" -divide_by 16 [get_pins u_soc_mgmt/u_soc_mgmt_secu_enclave/otp_clk_div_cnt_q_reg[3]/Q]

################################################################################
# RESETS
####################################
# Reset inputs
foreach reset $ResetPorts {
  set_ideal_network -no_propagate [get_ports $reset]
  set_max_delay [expr 3.00*${Pll0Period}] -from [get_ports $reset]
}

####################################
# Generated Reset
foreach reset $GeneratedResets {
  set_ideal_network -no_propagate [get_pins $reset]
  set_max_delay [expr 3.00*${Pll0Period}] -from [get_pins $reset]
}

################################################################################
# I/O timing

set DelayInpMin [ expr 0.05 * ${Pll0Period} ]
set DelayInpMax [ expr 0.7  * ${Pll0Period} ]
set DelayOupMin [ expr 0.05 * ${Pll0Period} ]
set DelayOupMax [ expr 0.7  * ${Pll0Period} ]

set periph_clk_inputs  [get_ports [list i_lt_axi_s_* i_lt_axi_m_* i_mbist_apb_m_*]]
set periph_clk_outputs [get_ports [list o_lt_axi_s_* o_lt_axi_m_* o_mbist_apb_m_* o_thermal_* o_irq_tms_throttle o_irq_tms_warning o_irq_tms_shutdown o_security_irq]]

# TODO(kluciani, double check if constraining these IOs on fast_clk is correct)
set fast_clk_inputs    [get_ports [list i_aic_boost_req i_throttle]]
set fast_clk_outputs   [get_ports [list o_clock_throttle o_aic_* o_dlm_* o_rtc_irq]]

set tck_inputs         [get_ports [list tms tdi trst]]
set tck_outputs        [get_ports [list tdo_en tdo]]

set ref_clk_inputs     [get_ports [list i_syscfg_apb4_s_*]]
# TODO(kluciani, double check if o_wdt_irq is meant to be on ref_clk)
set ref_clk_outputs    [get_ports [list o_syscfg_apb4_s_* o_wdt_irq o_global_sync o_ao_rst_n o_global_rst_n]]

set bisr_clk_inputs    [get_ports [list bisr_reset bisr_shift_en bisr_si]]
set bisr_clk_outputs   [get_ports [list bisr_so]]

# TODO(kluciani, double check if considering these asynchronous is correct, then add constraint with virtual clock?)
set async_inputs       [get_ports [list i_noc_async_idle_ack i_noc_async_idle_val i_thermal_throttle i_boot_mode i_hart_unavail i_hart_under_reset i_obs_bus]]
set async_outputs      [get_ports [list o_noc_async_idle_req o_obs_bus]]

puts "INFO: constraining [get_object_name $periph_clk_inputs] against o_periph_clk"
set_input_delay -min ${DelayInpMin} -clock o_periph_clk               $periph_clk_inputs
set_input_delay -max ${DelayInpMax} -clock o_periph_clk               $periph_clk_inputs
set_input_delay -min ${DelayInpMin} -clock i_ref_clk -add_delay $periph_clk_inputs
set_input_delay -max ${DelayInpMax} -clock i_ref_clk -add_delay $periph_clk_inputs
puts "INFO: constraining [get_object_name $periph_clk_outputs] against o_periph_clk"
set_output_delay -min ${DelayOupMin} -clock o_periph_clk               $periph_clk_outputs
set_output_delay -max ${DelayOupMax} -clock o_periph_clk               $periph_clk_outputs
set_output_delay -min ${DelayOupMin} -clock i_ref_clk       -add_delay $periph_clk_outputs
set_output_delay -max ${DelayOupMax} -clock i_ref_clk       -add_delay $periph_clk_outputs

puts "INFO: constraining [get_object_name $fast_clk_inputs] against o_fast_clk"
set_input_delay -min ${DelayInpMin} -clock o_fast_clk                  $fast_clk_inputs
set_input_delay -max ${DelayInpMax} -clock o_fast_clk                  $fast_clk_inputs
set_input_delay -min ${DelayInpMin} -clock i_ref_clk        -add_delay $fast_clk_inputs
set_input_delay -max ${DelayInpMax} -clock i_ref_clk        -add_delay $fast_clk_inputs
puts "INFO: constraining [get_object_name $fast_clk_outputs] against o_fast_clk"
set_output_delay -min ${DelayOupMin} -clock o_fast_clk                 $fast_clk_outputs
set_output_delay -max ${DelayOupMax} -clock o_fast_clk                 $fast_clk_outputs
set_output_delay -min ${DelayOupMin} -clock i_ref_clk       -add_delay $fast_clk_outputs
set_output_delay -max ${DelayOupMax} -clock i_ref_clk       -add_delay $fast_clk_outputs

puts "INFO: constraining [get_object_name $tck_inputs] against tck"
set_input_delay -min ${DelayInpMin} -clock tck  $tck_inputs
set_input_delay -max ${DelayInpMax} -clock tck  $tck_inputs
puts "INFO: constraining [get_object_name $tck_outputs] against tck"
set_output_delay -min ${DelayOupMin} -clock tck $tck_outputs
set_output_delay -max ${DelayOupMax} -clock tck $tck_outputs

puts "INFO: constraining [get_object_name $bisr_clk_inputs] against bisr_clk"
set_input_delay -min ${DelayInpMin} -clock bisr_clk  $bisr_clk_inputs
set_input_delay -max ${DelayInpMax} -clock bisr_clk  $bisr_clk_inputs
puts "INFO: constraining [get_object_name $bisr_clk_outputs] against bisr_clk"
set_output_delay -min ${DelayOupMin} -clock bisr_clk $bisr_clk_outputs
set_output_delay -max ${DelayOupMax} -clock bisr_clk $bisr_clk_outputs

puts "INFO: constraining [get_object_name $ref_clk_inputs] against ref_clk"
set_input_delay -min ${DelayInpMin} -clock i_ref_clk  $ref_clk_inputs
set_input_delay -max ${DelayInpMax} -clock i_ref_clk  $ref_clk_inputs
puts "INFO: constraining [get_object_name $ref_clk_outputs] against ref_clk"
set_output_delay -min ${DelayOupMin} -clock i_ref_clk $ref_clk_outputs
set_output_delay -max ${DelayOupMax} -clock i_ref_clk $ref_clk_outputs

puts "INFO: constraining ssn_bus_data_in against ssn_bus_clk"
set_input_delay  -min ${DelayInpMin} -clock ssn_bus_clk [get_ports ssn_bus_data_in]
set_input_delay  -max ${DelayOupMax} -clock i_ref_clk   [get_ports ssn_bus_data_in]
puts "INFO: constraining ssn_bus_data_out against ssn_bus_clk"
set_output_delay -min ${DelayOupMin} -clock ssn_bus_clk [get_ports ssn_bus_data_out]
set_output_delay -max ${DelayOupMax} -clock i_ref_clk   [get_ports ssn_bus_data_out]

# Estimated loads seen externally by ports.
set_load -pin_load 0.030 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]

########################################
# Contrain the special clk mux divider #
########################################

foreach sys_clk_index {0 1 2 3 4 5} {
  set_clock_gating_check -low  -setup 0.050 -hold 0.050 u_soc_mgmt/u_soc_mgmt_clk_gen/gen_clk_mux[$sys_clk_index].u_axe_ccl_clk_div_by_int/u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div_u_tc_lib_clk_mux/A
  set_clock_gating_check -high -setup 0.050 -hold 0.050 u_soc_mgmt/u_soc_mgmt_clk_gen/gen_clk_mux[$sys_clk_index].u_axe_ccl_clk_div_by_int/u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div_u_tc_lib_clk_mux/B
}

################################################################################
# Disable OTP timing. OTP is an analog macro and simulation model takes care of the timing between its signals.

set otp_macro_path "u_soc_mgmt/u_soc_mgmt_secu_enclave/u_otp_wrapper/u_otp_wrapper/u_sf_otp16kb_cp_a100_ln05lpe_4006000"

foreach {from_all to_all} {
    { PGMEN WEB READEN }     { ADD[0] ADD[1] ADD[2] ADD[3] ADD[4] ADD[5] ADD[6] ADD[7] ADD[8] ADD[9] ADD[10] ADD[11] ADD[12] ADD[13] }
    { CPUMPEN RSTB READEN }  PGMEN
    { PGMEN WEB READEN }     DLE
    { PGMEN WEB DLE READEN } RSTB
    READEN                   WEB
    RSTB                     CEB
    WEB                      CPUMPEN
} {
    foreach from $from_all {
        foreach to $to_all {
            set_disable_timing -from $from -to $to $otp_macro_path
        }
    }
}

################################################################################
# Test mode
set_case_analysis 0 [get_ports test_mode]

report_clock
