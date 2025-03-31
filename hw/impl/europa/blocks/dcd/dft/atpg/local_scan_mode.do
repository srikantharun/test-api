foreach_in_collection mod [get_modules .*tessent_(edt_c1_int_\[0-9\]*$|occ.*) -regexp] {
    add_core_instances -module $mod
}
set subblock_instances [get_instances -of_modules {alg_core_wrapper}]
foreach_in_collection inst [get_instances ".*_tessent_sib_sti_inst$" -regexp -below_instances $subblock_instances] {
  add_core_instances -instance $inst
}

set_static_dft_signal_values int_ltest_en 1
set_static_dft_signal_values int_edt_mode 1
set_static_dft_signal_values int_mode 1
set_static_dft_signal_values ext_edt_mode 0
set_static_dft_signal_values tck_occ_en   1
