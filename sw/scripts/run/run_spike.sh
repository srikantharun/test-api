#!/usr/bin/env bash
set -eu

usage () {
  cat << EOF
Usage: $(basename "$0") TEST_BINARY [options]
Run test binary using the Spike ISA simulator.

-h, --help         show this help
--design [design]  specify design the binary is built for: apu, aicore
                     (default: apu)
EOF
}

options=$(getopt -o 'h' --long 'help,design:' -- "$@")
eval set -- "$options"

# Default values for options
design="apu"

# Parse options
while true; do
  case "$1" in
    -h | --help)
      usage
      exit 0
      ;;
    --design)
      design="$2"
      shift 2
      ;;
    --)
      shift
      break
      ;;
    *)
      echo "Error: Option declared but not handled."
      exit 1
      ;;
  esac
done

# Check if a test binary was provided
if [ "$#" -ne 1 ] || [ -z "$1" ]; then
  usage
  exit 1
fi

test_binary="$1"

sys_spm_region="0x7000000:0x800000"
aicore_0_spm_region="0x14000000:0x80000"
aicore_0_l1_region="0x18000000:0x400000"
ddr_1_region="0x002800000000:0x000800000000"

case "$design" in
  apu)
    spike_opts="--isa=rv64gc -p6 -m${sys_spm_region},${aicore_0_spm_region},${aicore_0_l1_region},${ddr_1_region}"
    ;;
  aicore)
    spike_opts="--isa=rv64gcv_zfh_zvfh_zicntr_zihpm --varch=vlen:4096,elen:32 \
      -m${sys_spm_region},${aicore_0_spm_region},${aicore_0_l1_region},${ddr_0_region}"
    ;;
  *)
    echo "Error: Unknown design '$design'."
    exit 1
    ;;
esac

# Execute the spike command with the given test name
set -x
spike $spike_opts "${test_binary}"
