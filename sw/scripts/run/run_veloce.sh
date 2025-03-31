#!/bin/bash

copy_if_exists() {
  rm -f "$2"
  if [ -e "$1" ]; then
    cp -f "$1" "$2"
  fi
}

display_help() {
  local run_script=$DATABASE_ROOT/run
  cat << EOF
Usage: $(basename 0) [--no_tcl_server] [run args]

This script is a wrapper around ${run_script}

Args:
  -a|--attach_to_tcl_server: if specified the `--attach_to_tcl_server` option is passed to ${script}
  *: Any extra arg is passed to ${run_script}. See ${run_script} -h
EOF
}

set -e

# The first argument is the TEST_BINARY
TEST_BINARY="$1"
shift 1
attach_to_tcl_server=""
plusargs=""
emmc_hex_file=""
args=()
while [ "$#" -gt 0 ]
do
  case "$1" in
    -a|--attach_to_tcl_server)
    shift 1
    attach_to_tcl_server="--attach_to_tcl_server"
    ;;
    --uvm_testname=*) # Discarded
      shift 1
      ;;
    -h|--help)
      display_help
      exit 0
      ;;
    *)
      args+=("$1")
      shift 1
      ;;
  esac
done

if [ -z "$TEST_BINARY" ]; then
  echo "Usage: $0 TEST_BINARY"
  exit 1
fi

if [ "$DATABASE_ROOT" = "" ]; then
  echo "DATABASE_ROOT is undefined. Please source the database environment file 'OUTPUT_*/database.env'."
  exit 1
fi

cd "$DATABASE_ROOT"
set +e
./run $attach_to_tcl_server ${args[*]} --no_sw_build --timeout 3600 $TEST_BINARY
return_code=$?
set -e

# Handle log file
test_dir="$(dirname "$TEST_BINARY")"
test_name="$(basename "$TEST_BINARY")"
copy_if_exists "${DATABASE_ROOT}/run_logs/${test_name}.log" "${test_dir}/veloce.log"

exit $return_code
