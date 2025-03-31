set GIT_ROOT            [exec git rev-parse --show-toplevel]
set DEPENDENCIES_DIR    $env(DEPENDENCIES_DIR)
set SF5A_TECH_CELL_LIBS "/data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.10/FE-Common/ATPG/FastScan/*/ln05lpe*.mdt \
                         /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/FE-Common/ATPG/FastScan/*/ln05lpe*.mdt"

set MEM_IP ${DESIGN}
source ${GIT_ROOT}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

proc read_mem_libs { } {
  global MEM_LIBS_MEMLIB REG_FILES_MEMLIB
  global MEM_LIBS_MDT REG_FILES_MDT
  global MEM_LIBS_PATH REG_FILES_PATH
  global MEM_LIBS_V REG_FILES_V

  if { [info exists MEM_LIBS_MEMLIB] == 0 || [info exists REG_FILES_MEMLIB] == 0 } {
    puts "WARNING: No memlibs to load (design not found)"
    return
  }

  if { [llength $MEM_LIBS_MEMLIB] == 0 && [llength $REG_FILES_MEMLIB] == 0 } {
    puts "WARNING: No memlibs to load (design with no memories)"
    return
  }

  read_core_descriptions ${MEM_LIBS_MEMLIB}${REG_FILES_MEMLIB}
  read_cell_library ${MEM_LIBS_MDT}${REG_FILES_MDT}
  set_design_sources -format tcd_memory -Y ${MEM_LIBS_PATH}${REG_FILES_PATH} -extensions .memlib
  read_verilog ${MEM_LIBS_V}${REG_FILES_V} -interface_only -exclude_from_file_dictionary
}

proc write_librarymap { file_name } {
    set fd [open "${file_name}" w]
    puts $fd ""
    #if a file is included in the design_sources include it here.
    foreach {arg f} [get_design_sources -path_list] {
        if {$arg eq "-v"} {
            puts $fd $f
        }
    }
    close $fd
}

proc write_filemap { file_name } {
    set filemap [get_instrument_dictionary DftSpecification file_map_list]
    while {[set t [join $filemap]] ne $filemap} {set filemap $t}
    set fd [open "${file_name}" w]
    set i 0
    foreach f $filemap {
      # Print source and modified files to shell
      puts $f
      # Print only modified files to listfile
      if { [expr $i % 2] == 1 } {
        puts $fd $f
      }
      incr i
    }

    close $fd
}



proc add_config_tdr { } {

  set list_of_rams [ get_memory_instances ]
  set N_list_of_rams [sizeof_collection [get_memory_instances]]
  
  set MEM_PINS [list ]
 # ------------------- pin ------ dft_signal
  lappend  MEM_PINS  "MCS"             "mcs_control"     ; #This pin can be a single bit or an array of 2      
  lappend  MEM_PINS  "MCSRD"           "mcsrd_control"  
  lappend  MEM_PINS  "MCSWR"           "mcswr_control"  
  lappend  MEM_PINS  "MCSW"            "mcsw_control"   
  lappend  MEM_PINS  "RET"             "ret_control"    
  lappend  MEM_PINS  "PDE"             "pde_control"    
  lappend  MEM_PINS  "KCS"             "kcs_control"    
  lappend  MEM_PINS  "ADME"            "adme_control"   

  set signals [list ]
  for {set i 0} {$i < $N_list_of_rams} {incr i} {
  foreach {MEM_PIN DFT_SIG} ${MEM_PINS} {

          set mem [index_collection $list_of_rams $i]

          ## Different ram/rom types have different default values
          set mod_name [get_attribute_value $mem -name module_name]
          set ram_types  [list \
                            _ra1   \
                            _rf1   \
                            _rf2   \
                            _ra2   \
                            _rd2   \
                            _vrom   \
                           ]
          foreach type $ram_types {
              set is${type} [regexp $type $mod_name]
              set vname "is${type}"
              if {[set "$vname"]} {
                  set pf0 "${type}"
              }
          }
          foreach den [list \
                           _hs \
                           _hd \
                          ] {
              set is${den} [regexp $den $mod_name]
              set vname "is${den}"
              if {[set "$vname"]} {
                  set pf1 "${den}"
              }
          }
          
          set rst_val "0"
          if {${MEM_PIN} eq "MCS"} {
              if {!$is_vrom} {
                  set rst_val "01"
              }
          }
          if {${MEM_PIN} eq "MCSWR"} {
              if {$is_rf2 || $is_rd2} {
                  set rst_val "01"
              } else {
                  set rst_val "10"
              }
          }
          if {${MEM_PIN} eq "MCSRD"} {
              set rst_val "01"
          }
          if {${MEM_PIN} eq "ADME"} {
              if {($is_ra1&$is_hd)|($is_rf1&$is_hd)} {
                  set rst_val "011"
              } else {
                  set rst_val "100"
              }
          }
              

          set pin [get_pins -of_instances $mem ${MEM_PIN} -silent]
          set pin_sz [sizeof_collection $pin]
          
          if { $pin_sz == 0} {
              puts "$MEM_PIN is not found, skipping control point insertion on [get_name $mem]"
          } else {
              puts "$MEM_PIN is found, adding control point on [get_name $mem]"              

              for {set j 0} {$j < $pin_sz } {incr j } {
                  #need to postfix the dft-signal names as reset values could be different
                  set pf ${pf0}${pf1}
                  set name ${DFT_SIG}${j}${pf} ; # control pins name with suffix starting at zero

                  if {$name ni $signals} {
                      #execute only once to prevent warning messages
                      register_static_dft_signal_names $name -reset_value [string index $rst_val end-$j]
                      add_dft_signals $name -create_with_tdr
                      lappend signals $name
                  }
                  add_dft_control_points [index_collection [sort_collection $pin index  -numerical] $j] -dft_signal_source_name $name
              }
          }
      }
  }
  report_dft_signal_names
  report_dft_control_points
}


### proc to connect occ scan chain in rtl
proc connect_occ_scan_chain { } {
  set first_occ 1
  set prev_occ ""

  # Iterate using foreach
  global DESIGN
  global DESIGN_ID
  foreach_in_collection item [get_instances -of_modules ${DESIGN}_${DESIGN_ID}_tessent_occ] {
    set occ [get_attribute_value_list $item -name name]
    
    if {$first_occ} {
        # connect scan_in of the first occ in the chain to scan buf
	puts "create_connection tessent_occ_scan_buf_i_0/o_z $occ/scan_in"
	delete_connection $occ/scan_in
	create_connection tessent_occ_scan_buf_i_0/o_z $occ/scan_in
        set first_occ 0
    } else {
        # connect scan_out to scan_in of OCCs in the midle
	puts "create_connection $prev_occ/scan_out $occ/scan_in"
	delete_connection $occ/scan_in
	create_connection $prev_occ/scan_out $occ/scan_in
    }
    set prev_occ $occ
  }

  # Connect scan_out of last occ in the chain to the scan buf
  puts "create_connection $prev_occ/scan_out tessent_occ_scan_buf_o_0/i_a" 
  create_connection $prev_occ/scan_out tessent_occ_scan_buf_o_0/i_a 

}


###### add_pll_tdr ############
# proc to add tdr control to pll module tu_pll0519a01_ln05lpe_4007002
# tdr_name is the one used for create_dft_specification command
proc add_pll_tdr { tdr_name id pll_inst} {

  global dftSpec
  
  #add_config_element $dftSpec/IjtagNetwork/HostScanInterface(sri)/Sib($tdr_name)/Tdr($id)

  add_config_element Tdr($id) -in_wrapper [get_config_elements -hier Sib($tdr_name) -in_wrappers $dftSpec]

  #set pll_tdr        "$dftSpec/IjtagNetwork/HostScanInterface(sri)/Sib($tdr_name)/Tdr($id)"
  set pll_tdr       [get_attribute_value_list [get_config_elements -hier Tdr($id)] -name name]

  add_config_element $pll_tdr/DataInPorts
  add_config_element $pll_tdr/DataOutPorts

  add_config_element $pll_tdr/DataInPorts/connection(0)  -value $pll_inst/o_pll_lock
  add_config_element $pll_tdr/DataOutPorts/connection(0) -value $pll_inst/i_pll_resetb
  add_config_element $pll_tdr/DataOutPorts/connection(1) -value $pll_inst/i_pll_bypass

  set pin_sz [sizeof_collection [get_pins "$pll_inst/i_pll_m"]]

  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 2}]
    add_config_element $pll_tdr/DataOutPorts/connection($j) -value $pll_inst/i_pll_m[$i] 
  }

  set pin_sz [sizeof_collection [get_pins "$pll_inst/i_pll_p"]]

  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 12}]
    add_config_element $pll_tdr/DataOutPorts/connection($j) -value $pll_inst/i_pll_p[$i] 
  }

  set pin_sz [sizeof_collection [get_pins "$pll_inst/i_pll_s"]]

  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 18}]
    add_config_element $pll_tdr/DataOutPorts/connection($j) -value $pll_inst/i_pll_s[$i] 
  }

  set_config_value $pll_tdr/reset_value "21'b0" 
}

#################### add process monitors TDRs ############

proc add_tdr_process_monitors {sib id tdr_core_inst} {
  
  global dftSpec
    
  add_config_element Tdr($id) -in_wrapper [get_config_elements -hier Sib($sib) -in_wrappers $dftSpec]
  
  set tdr_path [get_attribute_value_list [get_config_elements -hier Tdr($id) -in_wrappers $dftSpec] -name name]
  
  set_config_value parent_instance          -in_wrapper [get_config_elements -hier Tdr($id)] $tdr_core_inst  
  set_config_value extra_bits_capture_value -in_wrapper [get_config_elements -hier Tdr($id)] self  
  
  
  add_config_element $tdr_path/DataInPorts
  
  add_config_element $tdr_path/DataOutPorts
  
  set_config_value multiplexing -in_wrapper $tdr_path/DataOutPorts off
    
  # DataInPorts  
  add_config_element $tdr_path/DataInPorts/connection(0)  -value $tdr_core_inst/i_valid
  
  set pin_sz [sizeof_collection [get_pins "$tdr_core_inst/i_count"]]
  
  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 1}]
    add_config_element $tdr_path/DataInPorts/connection($j) -value $tdr_core_inst/i_count[$i] 
  }
   
  # DataOutPorts
  add_config_element $tdr_path/DataOutPorts/connection(0) -value $tdr_core_inst/o_enable 
  add_config_element $tdr_path/DataOutPorts/connection(1) -value $tdr_core_inst/o_jtag_mode 
  
  set pin_sz [sizeof_collection [get_pins "$tdr_core_inst/o_use_ro"]]
  
  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 2}]
    add_config_element $tdr_path/DataOutPorts/connection($j) -value $tdr_core_inst/o_use_ro[$i] 
  }
  
  set init $pin_sz
  set pin_sz [sizeof_collection [get_pins "$tdr_core_inst/o_target"]]
  
  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + $init + 2}]
    add_config_element $tdr_path/DataOutPorts/connection($j) -value $tdr_core_inst/o_target[$i] 
  }
}


