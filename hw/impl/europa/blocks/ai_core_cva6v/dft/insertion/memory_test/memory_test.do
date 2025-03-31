# Settings
set DESIGN            ai_core_cva6v
set DESIGN_ID         rtl1
set BLACKBOXES        { axe_tcl_sram }
# set BLACKBOXES        { \
#                         cva6v_acc_dispatcher \
#                         cva6v_raptor_elem_dataflow \
#                         cva6v_raptor_vfpu \
#                       }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
# TODO update for Europa once memlibs are available
# read_core_descriptions ../../../implementation/tsmc7/memories/src/*/DFT/MBIST/*_tessent_tt_0p750v_25c_typical.lib
# read_verilog -interface_only ../../../implementation/tsmc7/memories/src/*/VERILOG/SYN/*_syn.v

dofile ${DEPENDENCIES_DIR}/read_rtl.do

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

add_clock 0 i_clk -period 1ns -pulse_always
add_input_constraints i_rst_ni -c1

report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on

set_system_mode analysis

set dftSpec [create_dft_specification]
# read_config_data dftSpec.${DESIGN}.rtl1.memory_test
# set dftSpec /DftSpecification(${DESIGN},rtl1)
report_config_data $dftSpec

process_dft_specification

extract_icl

set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
