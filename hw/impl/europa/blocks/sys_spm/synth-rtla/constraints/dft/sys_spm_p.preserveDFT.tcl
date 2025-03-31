##########################################################################################
# Script: sys_spm_p.preserveDFT.tcl
#
# Description: PD FC script to preserve DFT logic.
#              Run in init_design.design_import step, after elaborate.
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set_ungroup [get_cells *_tessent_*] false
set_boundary_optimization [get_cells -hier *_tessent_*] none

set_ungroup [get_cells -hier tessent_*] false
set_boundary_optimization [get_cells -hier tessent_*] none

set_dft_clock_gating_configuration -exclude_elements [get_cells *_tessent_* ]
set_clock_gating_objects -exclude [get_cells *_tessent_*]

# prevent scan-replacing tessent cells
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_sib_*]
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_*]
set_scan_element false [get_cells -hier *_bisr_inst*]

redirect -file ../rpt/report_ungroup {report_ungroup}
redirect -file ../rpt/report_boundary_optimization {report_boundary_optimization}
redirect -file ../rpt/report_scan_configuration {report_scan_configuration}
redirect -file ../rpt/report_clock_gating_objects {report_clock_gating_objects}
redirect -file ../rpt/report_dft_clock_gating_configuration {report_dft_clock_gating_configuration}
