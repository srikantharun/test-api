source help.tcl
source clocks.tcl

add_to_ax_procs "fast_printf"
proc fast_printf {enable} {
  # enable/disable fast printf (bypass UART logic to print chars)
  xforce hdl_top/i_europa/u_aipu/u_soc_periph_p/u_soc_periph/u_peripherals/soc_periph_dw_uart/fast_printf_en $enable
}

proc get_spm_mem_path {base_path bk sb mb inst} {
  return "$base_path/u_spm_mem/g_bank_inst[$bk]/u_spm_mem_bank/g_sub_bank_inst[$sb]/u_spm_mem_sub_bank/g_mini_bank_inst[$mb]/u_spm_mem_mini_bank/g_sram_inst[$inst]/u_tc_sram/gen_macro/u_macro/u_mem/ram_array"
}

proc download_binaries_spm {spm_type spm_path texthex_basepath} {
  if {$spm_type == "fake_sys_spm"} {
    memory download -instance $spm_path/mem -file ${texthex_basepath}.sys_spm.64b.texthex
    return
  } elseif {$spm_type == "sys_spm"} {
    set bk_nb 4
    set sb_nb 4
    set mb_nb 4
    set inst_nb 2
  } elseif {$spm_type == "pve_0.spm"} {
    set bk_nb 2
    set sb_nb 2
    set mb_nb 2
    set inst_nb 2
  } elseif {$spm_type == "pve_1.spm"} {
    set bk_nb 2
    set sb_nb 2
    set mb_nb 2
    set inst_nb 2
  } elseif {$spm_type == "aicore_0.spm" || $spm_type == "aicore_1.spm" || $spm_type == "aicore_2.spm" || $spm_type == "aicore_3.spm" || $spm_type == "aicore_4.spm" || $spm_type == "aicore_5.spm" || $spm_type == "aicore_6.spm" || $spm_type == "aicore_7.spm"} {
    set bk_nb 2
    set sb_nb 1
    set mb_nb 2
    set inst_nb 2
  } else {
    puts "ERROR: unknown spm_type $spm_type"
  }

  for {set bk 0} {$bk < $bk_nb} {incr bk} {
    for {set sb 0} {$sb < $sb_nb} {incr sb} {
      for {set mb 0} {$mb < $mb_nb} {incr mb} {
        for {set inst 0} {$inst < $inst_nb} {incr inst} {
          set memory_instance [get_spm_mem_path $spm_path $bk $sb $mb $inst]
          set texthex_file "${texthex_basepath}.${spm_type}.bk_${bk}.sb_${sb}.mb_${mb}.inst_${inst}.64b.texthex"
          memory download -instance $memory_instance -file $texthex_file
        }
      }
    }
  }
}

proc get_l1_mem_path {base_path sb mb} {
  return "$base_path/u_l1_mem/g_sbank[$sb]/u_sub_bank/g_mini_bank[$mb]/u_mini_bank/g_macro[0]/u_macro/gen_macro/u_macro/u_mem/ram_array"
}

proc download_binaries_l1 {l1_type l1_path texthex_basepath} {
  for {set sb 0} {$sb < 4} {incr sb} {
    for {set mb 0} {$mb < 16} {incr mb} {
      set memory_instance [get_l1_mem_path $l1_path $sb $mb]
      set texthex_file "${texthex_basepath}.${l1_type}.sb_${sb}.mb_${mb}.128b.texthex"
      memory download -instance $memory_instance -file $texthex_file
    }
  }
}

proc download_binaries_pve_0_l1 {pve_path texthex_basepath} {
  for {set cluster 0} {$cluster < 4} {incr cluster} {
    # For all clusters we preload the same data as the execute the same workload.
    download_binaries_l1 "pve_0.l1_0" "$pve_path/g_cluster[${cluster}]/u_cluster/u_pve_l1/u_pve_l1/u_l1" $texthex_basepath
  }
}

proc download_binaries_pve_1_l1 {pve_path texthex_basepath} {
  for {set cluster 0} {$cluster < 4} {incr cluster} {
    # For all clusters we preload the same data as the execute the same workload.
    download_binaries_l1 "pve_1.l1_0" "$pve_path/g_cluster[${cluster}]/u_cluster/u_pve_l1/u_pve_l1/u_l1" $texthex_basepath
  }
}

proc download_binaries_l2_one_module {l2_module_path texthex_module_basepath} {
  for {set bank 0} {$bank < 16} {incr bank} {
    for {set ram 0} {$ram < 4} {incr ram} {
      for {set sram 0} {$sram < 4} {incr sram} {
        set memory_instance "$l2_module_path/u_l2_gdr/u_l2_mem/g_bank[$bank]/u_l2_bank/g_ram[$ram]/u_l2_ram/g_sram[$sram]/u_l2_ram_wrapper/gen_macro/u_macro/u_mem/ram_array"
        set texthex_file "$texthex_module_basepath.bank_$bank.ram_$ram.sram_$sram.128b.texthex"
        memory download -instance $memory_instance -file $texthex_file
      }
    }
  }
}

proc download_binaries_l2_all_modules {l2_path texthex_basepath module_nb} {
  for {set module 0} {$module < $module_nb} {incr module} {
    set l2_module_path "${l2_path}_$module/u_l2_impl"
    set texthex_module_basepath "${texthex_basepath}_$module"
    download_binaries_l2_one_module $l2_module_path $texthex_module_basepath
  }
}

proc download_binaries_ddr {ddr_type ddr_path texthex_basepath} {
  if {$ddr_type == "fake_ddr"} {
    memory download -instance $ddr_path/mem -file ${texthex_basepath}.ddr_1.256b.texthex
    return
  }
}

proc download_emmc_binaries {emmc_hex_file} {
  if {$Axelera::DUT == "top_light" || $Axelera::DUT == "top" || $Axelera::DUT == "top_aic0" || $Axelera::DUT == "top_light_real_lpddr_ppp_0" } {
    set emmc_hdl_path hdl_top/i_emmc_softmodel/core_0
    memory download -instance ${emmc_hdl_path}/EMEM_0/user_0/mem -file $emmc_hex_file
  }
}

add_to_ax_procs "init_spi_softmodel"
proc init_spi_softmodel {texthex_path} {
  # Preload SPI softmodel registers and memory
  if {$Axelera::DUT == "top_light" || $Axelera::DUT == "top" || $Axelera::DUT == "top_aic0" || $Axelera::DUT == "top_light_real_lpddr_ppp_0"} {
    set spi_path {hdl_top/i_spi_softmodel/sf_core}
    set reg_file_path $::env(REPO_ROOT)/hw/dv/spinor_softmodel/sfdp_s25fs512s.hex
    memory download -instance $spi_path/sf_ID_mem/SFDP_CFI_ARRAY -file $reg_file_path
    memory download -instance $spi_path/mem_0/i_memArray -file $texthex_path
  }
}

add_to_ax_procs "download_binaries"
proc download_binaries {texthex_basepath} {
  # backdoor load test code in memories
  if {$Axelera::DUT == "top"} {
    download_binaries_spm "sys_spm" "hdl_top/i_europa/u_aipu/u_sys_spm_p/u_sys_spm/u_spm" $texthex_basepath
    download_binaries_spm "pve_0.spm" "hdl_top/i_europa/u_aipu/u_pve_p_0/u_pve/u_spm" $texthex_basepath
    download_binaries_spm "pve_1.spm" "hdl_top/i_europa/u_aipu/u_pve_p_1/u_pve/u_spm" $texthex_basepath
    download_binaries_spm "aicore_0.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_0/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_1.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_1/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_2.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_2/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_3.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_3/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_4.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_4/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_5.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_5/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_6.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_6/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_spm "aicore_7.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_7/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_pve_0_l1 "hdl_top/i_europa/u_aipu/u_pve_p_0/u_pve" $texthex_basepath
    download_binaries_pve_1_l1 "hdl_top/i_europa/u_aipu/u_pve_p_1/u_pve" $texthex_basepath
    download_binaries_l1 "aicore_0.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_0/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_1.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_1/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_2.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_2/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_3.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_3/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_4.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_4/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_5.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_5/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_6.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_6/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l1 "aicore_7.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_7/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
    download_binaries_l2_all_modules "hdl_top/i_europa/u_aipu/u_l2_p" $texthex_basepath.l2.module 8
    download_binaries_ddr "fake_ddr" "hdl_top/i_europa/u_aipu/u_lpddr_p_ppp_0/i_fake_lpddr" $texthex_basepath
  } elseif {$Axelera::DUT == "top_light" || $Axelera::DUT == "top_light_real_lpddr"} {
    download_binaries_spm "sys_spm" "hdl_top/i_europa/u_aipu/u_sys_spm_p/u_sys_spm/u_spm" $texthex_basepath
    download_binaries_spm "pve_0.spm" "hdl_top/i_europa/u_aipu/u_pve_p_0/u_pve/u_spm" $texthex_basepath
    download_binaries_pve_0_l1 "hdl_top/i_europa/u_aipu/u_pve_p_0/u_pve" $texthex_basepath
    download_binaries_l2_all_modules "hdl_top/i_europa/u_aipu/u_l2_p" $texthex_basepath.l2.module 8
    download_binaries_ddr "fake_ddr" "hdl_top/i_europa/u_aipu/u_lpddr_p_ppp_0/i_fake_lpddr" $texthex_basepath
  } elseif {$Axelera::DUT == "top_aic0"} {
    download_binaries_spm "sys_spm" "hdl_top/i_europa/u_aipu/u_sys_spm_p/u_sys_spm/u_spm" $texthex_basepath
    download_binaries_l2_all_modules "hdl_top/i_europa/u_aipu/u_l2_p" $texthex_basepath.l2.module 8
    download_binaries_spm "aicore_0.spm" "hdl_top/i_europa/u_aipu/u_ai_core_p_0/u_ai_core/u_aic_infra_p/u_aic_infra/u_aic_spm" $texthex_basepath
    download_binaries_ddr "fake_ddr" "hdl_top/i_europa/u_aipu/u_lpddr_p_ppp_0/i_fake_lpddr" $texthex_basepath
    download_binaries_l1 "aicore_0.l1" "hdl_top/i_europa/u_aipu/u_ai_core_p_0/u_ai_core/u_aic_ls_p/u_aic_ls/u_l1" $texthex_basepath
  } else {
    puts "ERROR: unknown DUT $Axelera::DUT"
  }
}

add_to_ax_procs "init_emmc_softmodel"
proc init_emmc_softmodel {} {
  # backdoor load emmc softmodel registers.
  if {$Axelera::DUT == "top_light" || $Axelera::DUT == "top" || $Axelera::DUT == "top_aic0" || $Axelera::DUT == "top_light_real_lpddr_ppp_0"} {
    set emmc_regs_path $::env(REPO_ROOT)/hw/dv/emmc_softmodel
    set emmc_hdl_path hdl_top/i_emmc_softmodel/core_0
    memory download -instance ${emmc_hdl_path}/RESP_GEN_0/CID_0/mem -file ${emmc_regs_path}/preload_CID.hex
    memory download -instance ${emmc_hdl_path}/RESP_GEN_0/CSD_0/mem -file ${emmc_regs_path}/preload_CSD.hex
    memory download -instance ${emmc_hdl_path}/RESP_GEN_0/OCR_0/mem -file ${emmc_regs_path}/preload_OCR.hex
    memory download -instance ${emmc_hdl_path}/MFSM_0/Ext_CSD_0/mem -file ${emmc_regs_path}/preload_EXT_CSD.hex
  }
}

add_to_ax_procs "run_reset_sequence"
proc run_reset_sequence {} {
  if {$Axelera::DUT == "top" || $Axelera::DUT == "top_light" || $Axelera::DUT == "top_aic0" || $Axelera::DUT == "top_light_real_lpddr"} {
    xforce hdl_top/i_por_rst_n 0
    # TODO: deadlogic
    #xforce hdl_top/i_trst_n 0
    run 6us
    xforce hdl_top/i_por_rst_n 1
    # TODO: deadlogic
    #xforce hdl_top/i_trst_n 1
  } else {
    puts "ERROR: unknown DUT $Axelera::DUT"
  }
}

add_to_ax_procs "force_dfi_timing_param"
proc force_dfi_timing_param {} {
  # force some dfi signals on the veloce dfi model
  xforce hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi_tphy_wrlat 10
  xforce hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi_tphy_wrdata 2
  xforce hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi_tphy_rddata_en 4
  xforce hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi_tphy_rdlat 2
}

add_to_ax_procs "dump_buffer"
proc dump_buffer {dir_name} {
  # dump waveform buffer featuring the 100k last cycles
  upload -tracedir $dir_name
}


add_to_ax_procs "dump_waves"
proc dump_waves {dir_name} {
  # continuously dump waveforms for all nets in the design
  # Warning: very slow
  hwtrace autoupload on -tracedir $dir_name
}

add_to_ax_procs "dump_xwaves"
proc dump_xwaves {group} {
  # continuously dump waveforms specified at compile time by xwave_siglist,
  # waves are dumped here: in veloce.wave/tbx.stw
  # group: "all" or group name specified in xwave_siglist.txt
  xwave on
  if {$group == "all"} {
    xwave select_all_groups
  } else {
    xwave -select_group $group
  }
}


add_to_ax_procs "run_until"
proc run_until {path value} {
  # run until {path} is equal to {value}
  set event_id [hwevent add $path $value]
  run
  # waitfor runcomplete
  if {$Axelera::INTERRUPTABLE_TEST} {
    while {[hwclock isrunning] || ![hwevent ismatured $event_id]} {
      exec sleep 1
      if {[file exists ./stop_test]} {
        run -stop
        break
      }
    }
  } else {
    waitfor runcomplete
  }
  hwevent delete $event_id
}


add_to_ax_procs "run_until_completion"
proc run_until_completion {} {
  # run until test main() returns
  if {$Axelera::DUT == "top" || $Axelera::DUT == "top_light" || $Axelera::DUT == "top_aic0" || $Axelera::DUT == "top_light_real_lpddr"} {
    # FIXME: use pad when available
    run_until hdl_top/i_europa/u_aipu/u_soc_periph_p/o_gpio[2] 1
  } else {
    puts "ERROR: unknown DUT $Axelera::DUT"
  }
}


add_to_ax_procs "report_test_status"
proc report_test_status {{testname ""}} {
  # report test success/failure by checking GPIO
  if {$Axelera::DUT == "top" || $Axelera::DUT == "top_light" || $Axelera::DUT == "top_aic0" || $Axelera::DUT == "top_light_real_lpddr"} {
    # FIXME: use pad when available
    set gpio_val [reg getvalue hdl_top/i_europa/u_aipu/u_soc_periph_p/o_gpio]
  } else {
    puts "ERROR: unknown DUT $Axelera::DUT"
  }
  set sys_exit [expr "($gpio_val >> 2) & 0x1"]
  set exit_code [expr "($gpio_val >> 3) & 0x1"]
  if { ($sys_exit == 1) && ($exit_code == 0) } {
    puts "report_test_status: \[PASS\] $testname"
  } else {
    puts "report_test_status: \[FAIL\] $testname"
  }
}


add_to_ax_procs "dump_cpu_instructions"
proc dump_cpu_instructions {cpu_type enable} {
  # enable/disable dump of CPU instructions; cpu_type is ax65 or cva6v
  if {[lsearch -exact {"top" "top_light" "top_aic0" "top_light_real_lpddr"} $Axelera::DUT] >= 0} {
    xforce hdl_top/enable_${cpu_type}_instruction_dump $enable
    xforce hdl_top/new_file_${cpu_type}_instruction_dump $enable
  }
}


add_to_ax_procs "close_cpu_instructions"
proc close_cpu_instructions {cpu_type} {
  # close CPU instructions files; cpu_type is ax65 or cva6v
  if {[lsearch -exact {"top" "top_light" "top_aic0" "top_light_real_lpddr"} $Axelera::DUT] >= 0} {
    # set new_file to 0 long enough to be registered by the clock
    xforce hdl_top/new_file_${cpu_type}_instruction_dump 0
    run 100ns
    xforce hdl_top/enable_${cpu_type}_instruction_dump 0
  }
}


add_to_ax_procs "tcl_cmd_server"
proc tcl_cmd_server {port} {
  # start a server evaluating TCL cmd
  set s [socket -server tcl_cmd_accept $port]
  puts "tcl_cmd_server is ready"
  vwait forever
}


proc tcl_cmd_accept {sock addr port} {
  # ensure that each "puts" by the server
  # results in a network transmission
  fconfigure $sock -buffering line
  # set up a callback for when the client sends data
  fileevent $sock readable [list tcl_cmd_eval $sock]
}


proc tcl_cmd_eval {sock} {
  gets $sock tcl_cmd
  eval $tcl_cmd
  puts $sock "tcl_cmd is done"
  close $sock
}

add_to_ax_procs "download_kse_bootrom"
proc download_kse_bootrom {integration_rom_lower integration_rom_upper production_rom_lower production_rom_upper test_name} {
  # backdoor load bootrom in KSE ROM
  set PATH_KSE_ROM_LOWER hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_secu_enclave/u_kudelski_kse3_rom/gen_macro/u_macro_lower/rom_array
  set PATH_KSE_ROM_UPPER hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_secu_enclave/u_kudelski_kse3_rom/gen_macro/u_macro_upper/rom_array
  if {$test_name == "test_sec_integration"} {
    memory download -instance $PATH_KSE_ROM_LOWER -file $integration_rom_lower
    memory download -instance $PATH_KSE_ROM_UPPER -file $integration_rom_upper
  } else {
    memory download -instance $PATH_KSE_ROM_LOWER -file $production_rom_lower
    memory download -instance $PATH_KSE_ROM_UPPER -file $production_rom_upper
  }
}
