# Set up common design identifiers
set DESIGN_NAME ai_core_p
set PROJECT europa

# Corner:
set CORNER              "tt"
set VOLTAGE             "0p85"
set TEMP                "25c"

# Constraints, required for at least determining the clock:
set sdc_files ../synth-rtla/constraints/${DESIGN_NAME}_constraints.tcl

## activity settings for avg power:
#set TOP_INST hdl_top.dut
#set ACTIVITY_FILE novas.fsdb
#set ANALYSIS_WINDOWS {18ns:110ns}

## directive for idle VAF:
set vaf_idle_directive [list "SetStimulus -net {*u_aic_infra*cva6v_cg*i_en} -duty 1 -override true"]
