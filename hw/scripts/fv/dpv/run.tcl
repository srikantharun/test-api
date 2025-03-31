

#Configure host file
set_host_file $::env(REPO_ROOT)/hw/scripts/fv/dpv/host.qsub

#C++ New Front End Flow
set _hector_comp_use_new_flow true

#Enable Vacuity
set_fml_var fml_vacuity_on true

#Enable Witness
set_fml_var fml_witness_on true

#set_fml_var _hector_cfg_zero_init yes

set_app_var dpv_cex_use_packaged_gdb_ddd true

set_fml_var fv_license_mode fml_elite

# Enable Impl coverage
set_fml_var fml_enable_prop_density_cov_map true

source ../settings.tcl

proc compile_spec {} {
  global SPEC_NAME
  global SPEC_FILE
  create_design -name spec -top $SPEC_NAME -cov
  cppan -I../dpv_model \
        ../dpv_model/$SPEC_FILE
  compile_design spec 
}

proc compile_impl {} {
  global IMPL_NAME
  global CLK
  global RSTN
  create_design -name impl -top $IMPL_NAME -clock $CLK -reset $RSTN -negReset -cov
  source rtl.analyze.tcl
  compile_design impl
}

proc run_solve {} {
  #Enable all multiple solve scripts
  set_hector_multiple_solve_scripts true

  proc_run_preparation
}

proc make {} {

  if {[compile_spec] == 0} {
    puts "Failure in compiling the specification model."
  }
  if {[compile_impl] == 0} {
    puts "Failure in compiling the implementation model."
  }
  if {[compose] == 0} {
    puts "Failure in composing the design."
  }
}

proc run {} {
  global COV
  make
  run_solve

  report_fv -verbose

  if {[info exists COV]} {
    save_property_density_results -db_name COI.vdb -design impl
    check_cpp_coverage -phase 1
    report_cpp_coverage -html model_cov
    puts "Coverage results generated for both model and implementation."
  } else {
    puts "No coverage generated. If you want it, define COV variable."
  }

  save_session
}

run
