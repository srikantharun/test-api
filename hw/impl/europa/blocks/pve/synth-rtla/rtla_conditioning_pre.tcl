echo "PVE Specialization for Conditioning"
set_attribute -objects [get_cell -hier *pve_l1_p]   -name boundary -value {{0 0} {0 500} {500 500} {500 0}}
set_attribute -objects [get_cell -hier *pve_cva6v_p]   -name boundary -value {{0 0} {0 500} {500 500} {500 0}}
