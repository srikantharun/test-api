
proc axe_add_memory_grouping { } {

  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank3_ram/gen_l2c_data_ram[*].u_data_ram/l2c_data/genblk3.gen_banks[*].u_axe_tcl_sram/gen_macro.u_macro}] -physical_cluster_override north_dram_3_2 
  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank2_ram/gen_l2c_data_ram[*].u_data_ram/l2c_data/genblk3.gen_banks[*].u_axe_tcl_sram/gen_macro.u_macro}] -physical_cluster_override north_dram_3_2 


  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank1_ram/gen_l2c_data_ram[*].u_data_ram/l2c_data/genblk3.gen_banks[*].u_axe_tcl_sram/gen_macro.u_macro}] -physical_cluster_override south_dram_1_0 
  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank0_ram/gen_l2c_data_ram[*].u_data_ram/l2c_data/genblk3.gen_banks[*].u_axe_tcl_sram/gen_macro.u_macro}]  -physical_cluster_override south_dram_1_0 

  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank3_ram/gen_l2c_tag_ram[*].u_tag_ram/l2c_tag/u_axe_tcl_sram/gen_macro.u_macro}]  -physical_cluster_override north_tramb_3_2 
  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank2_ram/gen_l2c_tag_ram[*].u_tag_ram/l2c_tag/u_axe_tcl_sram/gen_macro.u_macro}]  -physical_cluster_override north_tramb_3_2 

  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank1_ram/gen_l2c_tag_ram[*].u_tag_ram/l2c_tag/u_axe_tcl_sram/gen_macro.u_macro}]  -physical_cluster_override north_tramb_1_0 
  set_memory_instance_options [get_memory_instances {u_ax65_l2_wrapper/u_ax65_l2_top/u_l2c_bank0_ram/gen_l2c_tag_ram[*].u_tag_ram/l2c_tag/u_axe_tcl_sram/gen_macro.u_macro}] -physical_cluster_override north_tramb_1_0 

}
