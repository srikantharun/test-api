# Set up common design identifiers
set DESIGN_NAME pcie_p
set PROJECT europa

# Corner:
set CORNER              "tt"
set VOLTAGE             "0p85"
set TEMP                "85c"

# Constraints, required for at least determining the clock:
variable this_dir [file dirname  [file normalize [info script]]]
set CONSTR_DIR ${this_dir}/../synth-rtla/constraints/
## take mbist ones as the other one is not passing PA
set sdc_files ../synth-rtla/constraints/${DESIGN_NAME}_mbist.sdc
# set synopsys_program_name dc_shell
# set sdc_files ../synth-rtla/constraints/${DESIGN_NAME}_constraints.tcl

## activity settings for avg power:
#set TOP_INST hdl_top.dut
#set ACTIVITY_FILE novas.fsdb
#set ANALYSIS_WINDOWS {18ns:110ns}

## directive for idle VAF:
#set vaf_idle_directive [list "SetStimulus -net {__net__constant_1} -duty 1 -override true" \
#                         "SetStimulus -net {__net__constant_0} -duty 0 -override true"]
