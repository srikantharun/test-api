#!/bin/bash

args=()
plus_args=()

usage() {
  echo "Usage: $0 TEST_BIN --simulator=vsim|vcs --test_bench=TESTBENCH_DIR [ARGS]"
}

TESTNAME=$(basename "$1")
shift

# Parse options
while [[ $# > 0 ]]; do
  case "$1" in
    -h | --help)
      usage
      exit 0
      ;;
    --test_bench=*)
      TESTBENCH_DIR="$REPO_ROOT/${1#*=}"
      shift
      ;;
    --uvm_testname=*)
      TESTNAME="${1#*=}"
      shift
      ;;
    --simulator=*)
      SIM="${1#*=}"
      shift
      ;;
    --seed=*)
      SEED="${1#*=}"
      args+=("SEED=$SEED")
      shift
      ;;
    +*)
      plus_args+=("$1")
      shift
      ;;
    *)
      args+=("$1")
      shift
      ;;
  esac
done

if [ -z "$SIM" ] || [ -z "$TESTBENCH_DIR" ] || [ -z "$TESTNAME" ]; then
  usage
  exit 1
fi

# Check that there is a testbench built
if ! [ -d $TESTBENCH_DIR/build_$SIM*/compile_$SIM ]; then
  echo "No testbench built!"
  exit 1
fi

make -C $TESTBENCH_DIR run_$SIM TESTNAME=$TESTNAME NODEPS=1 ${args[@]} PLUSARGS="${plus_args[*]}"
