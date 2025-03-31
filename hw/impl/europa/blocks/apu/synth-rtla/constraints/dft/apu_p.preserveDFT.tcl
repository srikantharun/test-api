set_ungroup [get_cells -hier  *_tessent_*] false
set_boundary_optimization [get_cells -hier  *_tessent_*] none

set_ungroup [get_cells -hier  tessent_*] false
set_boundary_optimization [get_cells -hier  tessent_*] none

#set_scan_configuration -exclude_elements [get_cells -hier  *_tessent_*]
set_dft_clock_gating_configuration -exclude_elements [get_cells -hier  *_tessent_* ]
set_clock_gating_objects -exclude  [get_cells -hier  *_tessent_*]

set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_sib_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_c1_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_tap_main_inst*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst*]
set_scan_element false  [get_cells -hier *_tessent_occ_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_receiver_1x_pipe_pi_inst*]
set_scan_element false  [get_cells -hier *_bisr_inst*]
