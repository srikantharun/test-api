set DESIGN          noc_top
set IP_DIR          $env(MAKEFILE_DIR)/../
set GIT_REPO        [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a } 
set BBOX_MODULES   { \
    noc_ddr_east_p noc_ddr_west_p \
    noc_h_east_p noc_h_north_p noc_h_south_p noc_h_west_p \
    noc_soc_p \
    sdma_p \
    noc_v_center_p \
}

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl
