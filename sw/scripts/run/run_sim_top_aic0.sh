#!/usr/bin/env bash

test_binary="$1"
shift
$REPO_ROOT/sw/scripts/run/common_sw_sim.sh $test_binary \
  --testbench=$REPO_ROOT/hw/impl/europa/dv/top_aic0 \
  --uvm_testname="fw_base_test" \
  --memory="sys_spm" \
  --memory="ddr_1"  \
  --memory="aicore_0.spm" \
  --memory="aicore_0.l1" \
  --memory="l2"  \
  --release_dir=/home/projects_2/workspace/verif_team/releases/nightly/top_aic0 \
  +SEC_ROM_FILE="$KUDELSKI_KSE3_HOME/../20241217_kse3_ax12_release_axelera/rom/kse3_rom_integration.hex" \
  $@
