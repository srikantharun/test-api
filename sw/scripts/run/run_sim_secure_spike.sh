#!/bin/bash

test_binary="$1"
shift
$REPO_ROOT/sw/scripts/run/common_sw_sim.sh $test_binary \
  --testbench=$REPO_ROOT/hw/impl/europa/blocks/soc_mgmt/dv/secure_spike_tb/sim \
  --uvm_testname="spike_top_test" --memory="sys_spm" +ELF_FILE="$test_binary" \
  +SEC_ROM_FILE="$KUDELSKI_KSE3_HOME/../20241217_kse3_ax12_release_axelera/rom/kse3_rom_integration.hex" $@
