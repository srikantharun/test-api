#!/usr/bin/env bash
set -eu

usage() {
  cat << EOF
Usage: $(basename "$0") TEST_BINARY [options]
Run test binary using the Spike ISA simulator or specified simulator with test bench.

-h, --help         show this help
--test_bench=DIR   specify the test bench directory
--simulator=SIM    specify the simulator: vsim, vcs
--seed=SEED        specify the seed value
[ARGS]             additional arguments to pass to the simulator
+ARGS              plus arguments to pass to the simulator
EOF
}

# Default values for options
TESTBENCH_DIR=""
SIM=""
SEED=""
args=()
plus_args=()

test_binary="$1"
shift
# Determine the test name and set the CSV and log file names
TESTNAME=$(basename "$test_binary" .bin)  # Assuming the test binary might have a .bin extension
ELF=$test_binary

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
    --simulator=*)
      SIM="${1#*=}"
      shift
      ;;
    --seed=*)
      SEED="${1#*=}"
      args+=("SEED=$SEED")
      shift
      ;;
    --ELF=*)
      ELF="${1#*=}"
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
if ! [ -d $TESTBENCH_DIR/build_$SIM*/compile_$SIM ] && [ $SIM != 'spike' ]; then
  echo "No testbench built!"
  exit 1
fi

# Ensure args and plus_args are properly handled
make -C $TESTBENCH_DIR run_$SIM TESTNAME=$TESTNAME ELF=$ELF NODEPS=1 ${args[@]+"${args[@]}"} PLUSARGS="${plus_args[*]:-}"
