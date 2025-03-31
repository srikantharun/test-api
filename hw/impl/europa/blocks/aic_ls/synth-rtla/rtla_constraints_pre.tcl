# flatten VTRSP to be able to meet some sort of timing:
ungroup_cells [get_cells -hier -filter "ref_name=~*vtrsp_transpose_buffer*"]
