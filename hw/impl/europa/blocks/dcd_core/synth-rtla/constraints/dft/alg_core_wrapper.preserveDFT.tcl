set_ungroup [get_cells  *_tessent_*] false
set_boundary_optimization [get_cells -hier  *_tessent_*] none

set_ungroup [get_cells -hier  tessent_*] false
set_boundary_optimization [get_cells -hier  tessent_*] none

#set_scan_configuration -exclude_elements [get_cells  *_tessent_*]
set_dft_clock_gating_configuration -exclude_elements [get_cells  *_tessent_* ]
set_clock_gating_objects -exclude  [get_cells  *_tessent_*]

# prevent scan-replacing tessent cells
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_sib_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_*]
set_scan_element false  [get_cells -hier *_bisr_inst*]
