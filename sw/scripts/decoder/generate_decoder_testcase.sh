#!/bin/sh
# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner:       Max Wipfli <max.wipfli@axelera.ai>
# Description: Generates decoder testcases using a modified version of Allegro's
#              test harness and converts it into a C file so it can be played
#              from the APU.
set -euo pipefail

SCRIPT_DIR="$(realpath "$(dirname "$0")")"

usage () {
  cat << EOF
Usage: $(basename "$0") [ARGS]
Generate firmware testcases for the Allegro decoder IP based on the
vendor-provided testbench and scripts.

-h, --help                 show this help
--boot-only                generate testcase that only boots the MCU
                               (does not require --config)
--config [config_file]     path to the (vendor-provided) testcase config file
                               (e.g., /path/to/JPG_128x64_420_8_1c1.cfg)
--delivery [delivery_dir]  path to the vendor-provided IP delivery (containing
                               bin/ and sim/ subdirectories)
--work [work_dir]          path to the script working directory (default:
                               \$SCRIPT_DIR/work)
EOF
}

options=$(getopt -o 'h' --long 'help,boot-only,config:,delivery:,work:' -- "$@")
eval set -- "$options"

# default values for options
do_boot_only_testcase=0
config_file=""
delivery_dir=""
work_dir="$SCRIPT_DIR/work"

while true; do
  case "$1" in
    -h | --help)
      usage
      exit 0
      ;;
    --boot-only)
      do_boot_only_testcase=1
      shift
      ;;
    --config)
      config_file="$2"
      shift 2
      ;;
    --delivery)
      delivery_dir="$2"
      shift 2
      ;;
    --work)
      work_dir="$2"
      shift 2
      ;;
    --)
      break
      ;;
    *)
      echo "Error: Option declared but not handled."
      echo "$1"
      exit 1
      ;;
  esac
done

# check required options have been set
if [ -z "$config_file" ] && [ "$do_boot_only_testcase" -ne 1 ]; then
  echo "Error: Specify testcase using --config [config_file] or --boot-only"
  exit 1
fi
if [ -z "$delivery_dir" ]; then
  echo "Error: Missing required option --delivery [delivery_dir]"
  exit 1
fi

# Make paths absolute
if [ $do_boot_only_testcase -ne 1 ]; then
  orig_config_file="$(realpath "$config_file")"
fi
orig_delivery_dir="$(realpath "$delivery_dir")"
work_dir="$(realpath "$work_dir")"
# Assemble paths in working directory
if [ $do_boot_only_testcase -eq 1 ]; then
  config_name="boot_only"
else
  config_name="$(basename "$orig_config_file" .cfg)"
fi
config_file="$work_dir/$config_name.cfg"
delivery_dir="$work_dir/delivery"
testcase_dir="$work_dir/$config_name"

prepare_delivery() {
  echo "[+] Creating working directory..."
  rm -rf "$work_dir"
  mkdir -p "$work_dir"
  if [ -n "${orig_config_file+x}" ]; then
    echo "[+] Copying config file..."
    cp "$orig_config_file" "$config_file"
  fi
  echo "[+] Copying delivery to $delivery_dir..."
  cp -r "$orig_delivery_dir" "$delivery_dir" || true
  echo "[+] Patching delivery..."
  pushd "$delivery_dir"
  for patch in "$SCRIPT_DIR"/allegro_delivery_patches/*.patch; do
    echo "patch: $patch"
    patch -p1 < "$patch"
  done
  popd
}

generate_vendor_testcase() {
  echo "[+] Generating testcase $config_name..."
  if [ -s "$orig_config_file" ]; then
    echo "[+] Using vendor-provided scripts to generate testcase files..."
    pushd "$delivery_dir/sim"
    set -x
    ./run.pl -no_compile -no_sim "$config_file"
    set +x
    popd
  else
    echo "[+] $orig_config_file is empty, using pre-generated testcase files..."
    rm -rf "$testcase_dir"
    cp -r "$(dirname "$orig_config_file")/$config_name" "$testcase_dir"
  fi
  echo "[+] Testcase directory: $testcase_dir"
}

generate_boot_only_testcase() {
  echo "[+] Generating boot-only testcase using vendor-provided scripts..."

  mcu_dir="$delivery_dir/bin/mcu"

  # generate C and testbench instructions (instructions.{hex,c}) from empty input
  pushd "$mcu_dir/src"
  "./mcu_hex2c.pl" /dev/null
  popd

  # build sram_0000.MCU.mem
  make -C "$mcu_dir" clean all
  # move instructions.hex and MCU mem file to output directory
  rm -rf "$testcase_dir"
  mkdir -p "$testcase_dir"
  cp "$mcu_dir/sram_0000.MCU.mem" "$mcu_dir/src/instructions.hex" "$testcase_dir"
}

convert_testcase() {
  echo "[+] Converting vendor-provided testcase to C source file..."
  "$SCRIPT_DIR/convert_testcase_from_allegro_format.py" "$testcase_dir"
}

prepare_delivery
if [ $do_boot_only_testcase -eq 1 ]; then
  generate_boot_only_testcase
else
  generate_vendor_testcase
fi

convert_testcase

echo "[+] Done: $testcase_dir/$config_name.c"
