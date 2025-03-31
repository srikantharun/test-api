#!/usr/bin/env bash

# Quick and dirty regenerate script...
# To be cleaned up later

# Default value for SDC_SIMPLIFIER
: ${SDC_SIMPLIFIER:=1}

module switch pt/V-2023.12-SP5

srun -c8 pt_shell -file sdc_gen_shift.tcl   -output_log_file sdc_gen_shift.log
# PT always prints 1 error, ignore it
grep -q "Diagnostics summary: 1 error" sdc_gen_shift.log || (echo "Error: Unexpected errors in sdc_gen_shift" && exit 1)

srun -c8 pt_shell -file sdc_gen_atspeed.tcl -output_log_file sdc_gen_atspeed.log
grep -q "Diagnostics summary: 1 error" sdc_gen_atspeed.log || (echo "Error: Unexpected errors in sdc_gen_atspeed" && exit 1)

srun -c8 pt_shell -file sdc_gen_mbist.tcl   -output_log_file sdc_gen_mbist.log
grep -q "Diagnostics summary: 1 error" sdc_gen_mbist.log || (echo "Error: Unexpected errors in sdc_gen_mbist" && exit 1)

workdir=$(pwd)
block="alg_core_wrapper"

#Modify the dft constraints following https://git.axelera.ai/ai-pd-team/europa/-/issues/144
for mode in Mbist Shift Atspeed; do
    infile=${workdir}"/"${block}".cns${mode}.sdc"
    echo Modify $infile
    sed -E -e 's/tessent_test_clock/test_clk/g' \
        -e '/^set_input_delay|^set_output_delay/{ s/^/# /; }' \
        $infile > ../../synth-rtla/constraints/dft/${block}.cns${mode}.sdc


    if [ "$SDC_SIMPLIFIER" -eq 1 ]; then
        echo Simplify ../../synth-rtla/constraints/dft/${block}.cns${mode}.sdc
        python3 $REPO_ROOT/hw/impl/europa/dft/scripts/sdc_simplifier.py ../../synth-rtla/constraints/dft/${block}.cns${mode}.sdc
    fi
done
