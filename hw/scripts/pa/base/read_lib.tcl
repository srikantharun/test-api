# Script to read in the .lib files and create a Library Database (if not present)
# or to read in the created Library Database (if already present).

source ${make_dir}/pa_setup.tcl

proc mcsplit "str splitStr {mc {\x00}}" {
    return [split [string map [list $splitStr $mc] $str] $mc]
}

proc check_vt {tech_lib {ip_version ""} {Tpf "_"}} {
  set BU_TEMP 25c
  set BU_VOLTAGE 0p75
  # check if corner / temp combination is available
  # if not: first check with back up voltage, second with back up temperature, last back-up both
  set V $::VOLTAGE
  set T $::TEMP
  set SYNTH_CORNER "${ip_version}*$::CORNER*${V}*${Tpf}${T}"
  if { [catch {glob ${tech_lib}/${ip_version}*${SYNTH_CORNER}*}] } {
    # failed, check with BU Voltage:
    set SYNTH_CORNER "${ip_version}*$::CORNER*${BU_VOLTAGE}*${Tpf}$::TEMP"

    if { [catch {glob ${tech_lib}/${SYNTH_CORNER}*}] } {
      # failed, check only BU Temp:
      set SYNTH_CORNER "${ip_version}*$::CORNER*$::VOLTAGE*${Tpf}${BU_TEMP}"

      if { [catch {glob ${tech_lib}/${SYNTH_CORNER}*}] } {
        # failed, assume both back-up (else black-box will be inserted)
        set V ${BU_VOLTAGE}
        set T ${BU_TEMP}

        puts "WARNING! Using back-up temperature ${T} and back-up voltage ${V} for ${tech_lib} as $::TEMP and $::VOLTAGE are not present! (${SYNTH_CORNER})"
      } else {
        set T ${BU_TEMP}
        puts "WARNING! Using back-up temperature ${T} for ${tech_lib} as $::TEMP is not present!"
      }
    } else {
      set V ${BU_VOLTAGE}
      puts "WARNING! Using back-up voltage ${V} for ${tech_lib} as $::VOLTAGE is not present!"
    }
  }
  return "${ip_version}*$::CORNER*${V}*${Tpf}${T}*"
}

set lib_db    "$env(PA_GENERAL)/${PROJECT}/lib/${CORNER}_${VOLTAGE}_${TEMP}"
if { ![file exist ${lib_db}] } {
  puts "LIB dir ${lib_db} not present, setting local"
  set lib_db    "$PDB_DIR/LIB_${CORNER}_${VOLTAGE}_${TEMP}"
}

# Add name of .lib files including WLM as part of 'list_of_lib_files' variable.
set MEM_IP ${DESIGN_NAME}
set eda_tool rtl_shell
source $env(REPO_ROOT)/hw/ip/tech_cell_library/default/rtl/sf5a/tc_techlib.tcl

set stdlib_dbs ""
foreach tech_lib "${STD_CELL_LIBS}" {
  set SYNTH_CORNER [check_vt $tech_lib]
  if { ![file exists $lib_db] } {
    ReadLibrary -name [glob $tech_lib/${SYNTH_CORNER}.lib*]
  }
  set stdlib_dbs "${stdlib_dbs} [glob ${tech_lib}/${SYNTH_CORNER}.db*]"
}


foreach tech_lib_full "${MEM_LIBS} ${REG_FILES}" {
  puts "Reading: ${tech_lib_full}"
  set sub_path [mcsplit $tech_lib_full "fusion_ref"]
  set tech_lib [lindex $sub_path 0]
  set post_path [lindex $sub_path 1]

  set SYNTH_CORNER 0
  set ip_version ""
  set Tpf "_"

  if {
      ([string first "tu_pll0519a01"  $tech_lib_full] != -1) ||
      ([string first "tu_pvt0501a01"  $tech_lib_full] != -1) ||
      ([string first "tu_tem0501ar01" $tech_lib_full] != -1)
  } {
    set sub_path [lindex [mcsplit $tech_lib_full "generated"] 0]
    set ip [lindex [mcsplit [lindex [mcsplit ${post_path} "_ln05lpe"] 0] "tu_"] 1]
    set ip_version [lindex [mcsplit [lindex [mcsplit ${post_path} "/"] 2] "ln05"] 0]
    set tech_lib "${sub_path}/${ip}/*/FE-Common/LIBERTY/"
  } elseif {
    ([string first "_efuse" $tech_lib_full] != -1) ||
    ([string first "_otp" $tech_lib_full] != -1)
  } {
    set sub_path [lindex [mcsplit $tech_lib_full "generated"] 0]
    set ip [lindex [mcsplit ${post_path} "/"] 1]
    set ip_version [lindex [mcsplit [lindex [mcsplit ${post_path} "/"] 2] "ln05"] 0]

    if {[string first "_otp" $tech_lib_full] != -1} {
      set pf "synopsys/"
    } else {
      set pf ""
    }
    set tech_lib "${sub_path}/${ip}/*/LIBERTY/${pf}"
  } elseif {
    ([string first "ln05lpe_gpio_lib_" $tech_lib] != -1 ) ||
    ([string first "_c54l08_" $tech_lib] != -1 ) } {
  } elseif {[string first "pcie4_pma" $tech_lib_full] != -1} {
    set tech_lib "/data/foundry/samsung/sf5a/ip/synopsys/dwc_pcie4phy_sssf5a_x4ns/Latest/pma/./timing/13M_4Mx_7Dx_2Iz_LB/lib_pg/"
    set SYNTH_CORNER "*tt0p75v125c*"
  } elseif {[string first "dwc_lpddr5" $tech_lib_full] != -1} {
    set ip "dwc_ap_lpddr5x_phy_sssf5a"
    set sub_path [lindex [mcsplit $tech_lib_full "generated"] 0]
    set full_sub   [lindex [mcsplit ${post_path} "/"] 2]
    set ip_version [lindex [mcsplit ${full_sub} "_top"] 0]

    set Tpf "v"

    set tech_lib "${sub_path}/${ip}/*/*/Latest/*/*/lib_pg/"
  } elseif {
      ([string first "_monitor" $tech_lib] != -1) ||
      ([string first "imc_bank" $tech_lib] != -1)
  } {
    set Tpf "v"
  }

  if { ${SYNTH_CORNER} == 0 } {
    set SYNTH_CORNER [check_vt ${tech_lib} ${ip_version} ${Tpf}]
  }

  # read in the library:
  if { ![catch {glob ${tech_lib}/${SYNTH_CORNER}.lib*}] } {
    if { ![file exists $lib_db] } {
      ReadLibrary -name [glob ${tech_lib}/${SYNTH_CORNER}.lib*]
    }
  } else {
    puts "WARNING! No .lib found for ${tech_lib}/${SYNTH_CORNER}.lib*, enable black box allowing..."
    pa_set elaborate_auto_black_box true
  }
}
set stdlib_dbs "${stdlib_dbs} $env(DW_ROOT)/libraries/syn/dw_foundation.sldb"

set AW_WORKLIB_DIR ${script_dir}/build_aw_worklib; # stores DW compiled data
if {![file exists $AW_WORKLIB_DIR]} { exec mkdir -p $AW_WORKLIB_DIR }

pa_set enable_dw_synthesis true
pa_set dw_write_directory ${AW_WORKLIB_DIR}
pa_set dw_synthesized_dir_path ${AW_WORKLIB_DIR}
pa_set aw_directories ${script_dir}/aw_custom
pa_set dblib ${stdlib_dbs}

# Check if the library DB is already present; if not => create it.
# !! Quick and dirty check if "$lib_db" is present, it is NOT an intelligent check !!
# (like in makefiles) !!
# If anything is changed in the .lib file setup:
# ==> "$lib_db" needs to be removed to enforce re-generation!
pa_set mixed_design_case_sensitive true
if { ![file exists $lib_db] } {
  # Write library DB.
  WriteLibraryDatabase -write_library_database_dir $lib_db \
                       -write_library_database_log $LOG_DIR/${filename}_write_lib_db.log
}

# Add pointer to saved library DB.
pa_set library_database_dirs "${lib_db}"

