# *****************************************************
# Modified top-level constraints for pcie_p, 
# Original version from SNPS at $PCIE_WORKSPACE/syn/constrain/script/DWC_pcie_subsystem_con.tcl
# Axelera modified to intercept pcie_p, this adds/changes stuff for the following points
# - i_ref_clk -> additional clock added by axelera driving always on logic in the wrapper. Does not propagate into subsys.
# - i_pcie_aux_clk -> top-level clock, this clock drives aux_clk clock in subsystem.
# - i_pcie_init_mt_axi_aclk -> top-level clock, this clock drives mstr_aclk and phy_fw_clk clock in subsystem.
# - i_pcie_targ_mt_axi_aclk -> top-level clock, this clock drives slv_aclk clock in subsystem.
# - i_pcie_targ_cfg_dbi_axi_aclk -> top-level clock, this clock drives dbi_aclk clock in subsystem.
# - i_pcie_aux_clk -> top-level clock, this clock drives aux_clk clock in subsystem.
#   - removed existing create_clock statements and replaced by axelera one
#   - create generated clock for all subsystem clocks
# - intercept changes to interface -> existing in/out delays modified, some removed and some added.
# - Removed max delay statements on memory control signals that will be tied.
# - Removed max delay statements on DFT signals, DFT constraints intercept these.
# - Added MBIST releated constrants.

change_names -rule verilog -hierarchy

if { [info exists synopsys_program_name] } {
 if { $synopsys_program_name == "dc_shell" } {
  set flow syn
 } elseif { $synopsys_program_name == "fc_shell" } {
  set flow syn
 } elseif { $synopsys_program_name == "pt_shell" } {
  set flow sta
 }
}

if { ![info exists CONSTR_DIR] } {
  puts WARNING: CONSTR_DIR is not defined. Setting to local dir. It should point to the directory that contains all axelera constraints files.
  set CONSTR_DIR "."
}

source -e -v ${CONSTR_DIR}/fc_syn_variables.tcl

source -e -v ${CONSTR_DIR}/pcie_p_bcm_pin_map.tcl

source -e -v ${CONSTR_DIR}/pcie_p_constraints_procs.tcl

set init_variables [lsort [info globals]]
source -e -v ${CONSTR_DIR}/pcie_p_constraints_vars.tcl

set path_name [prefixing $hiervar  phy*/${pma_inst_name}/*]
remove_generated_clock [get_clocks -filter "full_name=~$path_name"]

source -e -v ${CONSTR_DIR}/pcie_p_clocks.tcl
source -e -v ${CONSTR_DIR}/pcie_p_clock_arrays.tcl

source -e -v ${CONSTR_DIR}/pcie_p_clock_queries_pre_stop_clocks.tcl
source -e -v ${CONSTR_DIR}/pcie_p_clock_uncertainty.tcl
source -e -v ${CONSTR_DIR}/pcie_p_clock_exceptions.tcl

source -e -v ${CONSTR_DIR}/pcie_p_mbist.sdc

source -e -v ${CONSTR_DIR}/pcie_p_io_constraints.tcl
if { !$PT_SHELL && !$GCA_SHELL && !$TCM_SHELL } {
  source -e -v ${CONSTR_DIR}/pcie_p_io_drive_load.tcl
}

source -e -v ${CONSTR_DIR}/pcie_p_clock_queries_post_stop_clocks.tcl
source -e -v ${CONSTR_DIR}/pcie_p_exceptions.tcl
