# Set up common design identifiers
set DESIGN_NAME lpddr_p
set PROJECT europa

# Corner:
set CORNER              "tt"
set VOLTAGE             "0p85"
set TEMP                "85c"

# Constraints, required for at least determining the clock:
variable this_dir [file dirname  [file normalize [info script]]]
set CONSTR_DIR ${this_dir}/../synth-rtla/constraints/
set sdc_files ../synth-rtla/constraints/${DESIGN_NAME}_constraints.tcl

#set BBOX_MODULES {dwc_lpddr5xphyzcal_top dwc_lpddr5xphycmosx2_top dwc_lpddr5xphymaster_top dwc_lpddr5xphyacx2_top dwc_lpddr5xphycsx2_top dwc_lpddr5xphyckx2_top dwc_lpddr5xphydx4_top dwc_lpddr5xphydx5_top}
set MAP_MODULES {{{dwc_lpddr5xphyzcal_top dwc_lpddr5xphyzcal_top_ew} {{DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphycmosx2_top dwc_lpddr5xphycmosx2_top_ew} {{DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphymaster_top dwc_lpddr5xphymaster_top_ew} {{DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphyacx2_top dwc_lpddr5xphyacx2_top_ew} {{PclkIn PclkIn} {DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphycsx2_top dwc_lpddr5xphycsx2_top_ew} {{PclkIn PclkIn} {DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphyckx2_top dwc_lpddr5xphyckx2_top_ew} {{PclkIn PclkIn} {DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphydx4_top dwc_lpddr5xphydx4_top_ew} {{PclkIn PclkIn} {DfiClkIn DfiClkIn}}}
                 {{dwc_lpddr5xphydx5_top dwc_lpddr5xphydx5_top_ew} {{PclkIn PclkIn} {DfiClkIn DfiClkIn}}}
                 }

## activity settings for avg power:
#set TOP_INST hdl_top.dut
#set ACTIVITY_FILE novas.fsdb
#set ANALYSIS_WINDOWS {18ns:110ns}

## directive for idle VAF:
#set vaf_idle_directive [list "SetStimulus -net {__net__constant_1} -duty 1 -override true" \
#                         "SetStimulus -net {__net__constant_0} -duty 0 -override true"]
