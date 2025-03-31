   	   set_ungroup [get_cells -hier  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst] false
   	   set_boundary_optimization [get_cells -hier  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst] none

   	   set_ungroup [get_cells -hier  *_tessent_*] false
   	   set_boundary_optimization [get_cells -hier  *_tessent_*] none

   	   set_ungroup [get_cells -hier  tessent_*] false
   	   set_boundary_optimization [get_cells -hier  tessent_*] none

   	   #puts "set_size_only -all_instances [get_cells -quiet tessent_scan_buf_*_*]"
   	   #set_size_only -all_instances [get_cells -quiet tessent_scan_buf_*_*]

   	   #set_multibit_options -exclude [get_cells  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst]
   	   #set_freeze_ports -all [get_cells  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst] true ;# belt and braces to retain the interfaces

   	   # Protect any pre-existing mapped Tessent cells with size_only. I have seen Tessent be very picky about finding certain cell names in the netlist.
   	   # This was only needed when Tessent IP arrived as gates.
   	   # set_size_only -all_instances [get_cells -quiet -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_edt_c1_int_inst -filter ?!is_hierarchical && is_mapped?]
 
   	   set_scan_configuration -exclude_elements [get_cells -hier  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst]
   	   set_dft_clock_gating_configuration -exclude_elements [get_cells -hier  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst ]
   	   set_clock_gating_objects -exclude  [get_cells -hier  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst]

   	   set_scan_configuration -exclude_elements [get_cells -hier  *_tessent_*]
   	   set_dft_clock_gating_configuration -exclude_elements [get_cells -hier  *_tessent_* ]
   	   set_clock_gating_objects -exclude  [get_cells -hier  *_tessent_*]
	   
	   set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_sib_*]
	   set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
	   set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_c1_*]
	   set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_tap_main_inst*]
	   set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst*]
	   #set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_occ_*]
	   set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_receiver_1x_pipe_pi_inst*]

    # temporary fix
   	   #set_ungroup [get_cells -hier  u_l2c_p] false
   	   #set_boundary_optimization [get_cells -hier u_l2c_p] none
   	   #set_ungroup [get_cells -hier  *u_core_p*] false
   	   #set_boundary_optimization [get_cells -hier *u_core_p*] none
