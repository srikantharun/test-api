#!/usr/bin/env bash

set -eu

usage () {
  cat << EOF
Usage: $(basename "$0") [options] TEST_BINARY
Run test binary using GDB via JTAG.

-h, --help                 show this help
-d, --debug                debug mode (no command list passed to GDB)
--design [design]          specify design the binary is built for:
                             top, aicore0, ... (default: top)
-p, --platform [platform]  specify the platform (required)a
EOF
}

options=$(getopt -o 'hdp:' --long 'help,debug,design:,platform:' -- "$@")
eval set -- "$options"

# Default values for options
do_debug=0
design="top"
platform=""

# Parse options
while true; do
  case "$1" in
    -h | --help)
      usage
      exit 0
      ;;
    -d | --debug)
      do_debug=1
      shift
      ;;
    -p | --platform)
      platform="$2"
      shift 2
      ;;
    --design)
      design="$2"
      shift 2
      ;;
    -- )
      shift
      break
      ;;
    * )
      echo "Error: Option declared but not handled."
      usage
      exit 1
      ;;
  esac
done

if [ -z "$platform" ]; then
  echo "Error: Missing required option --platform."
  usage
  exit 1
fi

TEST_BINARY="$1"
if [ -z "$1" ]; then
  echo "Error: Missing positional argument TEST_BINARY."
  usage
  exit 1
fi

# Only apply command if on non-debug mode
COMMAND=""
if [ "$do_debug" -ne 1 ]; then
  COMMAND="--command $REPO_ROOT/sw/scripts/gdb/test.gdb"
fi

set -ex
# Explicitly prefix the script name with ./
riscv64-unknown-elf-gdb -ex "target extended-remote | openocd -f $REPO_ROOT/sw/scripts/openocd/openocd.tcl" ${COMMAND} ${TEST_BINARY}
