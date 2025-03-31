#!/usr/bin/env bash

test_binary="$1"
shift
$REPO_ROOT/sw/scripts/run/common_sw_sim.sh $test_binary \
  --testbench=$REPO_ROOT/hw/impl/europa/dv/top \
  --uvm_testname="fw_base_test" \
  --memory="sys_spm"      \
  --memory="pve_0.spm"    \
  --memory="pve_0.l1_0"   \
  --memory="pve_0.l1_1"   \
  --memory="pve_0.l1_2"   \
  --memory="pve_0.l1_3"   \
  --memory="pve_1.spm"    \
  --memory="pve_1.l1_0"   \
  --memory="pve_1.l1_1"   \
  --memory="pve_1.l1_2"   \
  --memory="pve_1.l1_3"   \
  --memory="aicore_0.spm" \
  --memory="aicore_1.spm" \
  --memory="aicore_2.spm" \
  --memory="aicore_3.spm" \
  --memory="aicore_4.spm" \
  --memory="aicore_5.spm" \
  --memory="aicore_6.spm" \
  --memory="aicore_7.spm" \
  --memory="aicore_0.l1" \
  --memory="aicore_1.l1" \
  --memory="aicore_2.l1" \
  --memory="aicore_3.l1" \
  --memory="aicore_4.l1" \
  --memory="aicore_5.l1" \
  --memory="aicore_6.l1" \
  --memory="aicore_7.l1" \
  --memory="ddr_0"  \
  --memory="ddr_1"  \
  --memory="l2"  \
  --release_dir=/home/projects_2/workspace/verif_team/releases/nightly/top \
  +SEC_ROM_FILE="$KUDELSKI_KSE3_HOME/../20241217_kse3_ax12_release_axelera/rom/kse3_rom_integration.hex" \
  $@
