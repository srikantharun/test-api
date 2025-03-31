#!/usr/bin/env bash

test_binary="$1"
shift
$REPO_ROOT/sw/scripts/run/common_sw_sim.sh $test_binary \
  --testbench=$REPO_ROOT/hw/impl/europa/dv/top_light \
  --uvm_testname="fw_base_test" \
  --memory="sys_spm"      \
  --memory="pve_0.spm"    \
  --memory="pve_0.l1_0"   \
  --memory="pve_0.l1_1"   \
  --memory="pve_0.l1_2"   \
  --memory="pve_0.l1_3"   \
  --memory="ddr_1"  \
  --memory="l2"  \
  --release_dir=/home/projects_2/workspace/verif_team/releases/nightly/top_light \
  +SEC_ROM_FILE="$KUDELSKI_KSE3_HOME/../20241217_kse3_ax12_release_axelera/rom/kse3_rom_integration.hex" \
  $@
