##########################################################################################
# Script: pt_setup.tcl
#
# Description: PT script to process DFT constraints for APU_CORE.
#              Script is for advanced users only. For more info contact maintainer.
#
#              shift mode
#
# Maintainer: <redouan.tahraoui@axelera.ai>
#
##########################################################################################

#Temp
set INST_HIER ""
alias ax_get_pins get_pins
set PINS_OR_PORTS ports

#########
set CHECK_MANUAL_CHANGES 0
set DESIGN soc_mgmt_p
set MEM_IP ${DESIGN}
set GIT_ROOT [exec git rev-parse --show-toplevel]
source ${GIT_ROOT}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

set glob_paths {}
foreach mem_lib [split $MEM_LIBS_PATH$REG_FILES_PATH " "] {
    if { $mem_lib == "" } {
        # Trailing whitespace, skip
        continue
    }
    lappend glob_paths "${mem_lib}/fusion_ref_library/*"
}
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*c54/*/FE-Common/LIBERTY/*/*c54l08_tt_nominal_max_0p7500v_125c.db_ccs_tn_lvf"
set link_paths {}
foreach glob_path $glob_paths {
    lappend link_paths [glob $glob_path]
}

set_app_var link_path "* [join $link_paths]"


read_verilog /data/europa/pd/soc_mgmt_p/block_build/dev_202501301203_topv12_pinoptv1/build/fc/compile/results/soc_mgmt_p.mapped.v.gz

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false
