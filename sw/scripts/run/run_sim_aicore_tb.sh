#!/bin/bash

test_binary="$1"
shift

$REPO_ROOT/sw/scripts/run/common_sw_sim.sh $test_binary \
  --testbench=$REPO_ROOT/hw/ip/aicore/default/dv/sim \
  --uvm_testname="ai_core_base_test" --memory="aicore_0.spm" --memory="aicore_0.l1" --memory="sys_spm" \
  "ELF_FILE=$test_binary +UVM_SW_IPC_HANDLE_END_OF_TEST" $@
