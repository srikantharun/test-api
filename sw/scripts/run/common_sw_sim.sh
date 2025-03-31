#!/usr/bin/env bash

# Sensible default: stop on first non-zero return code
set -e

######################################
# Util functions
######################################
error() {
  >&2 echo "ERROR: $@"
  exit 1
}

# Display program information and expected arguments
print_help() {
  echo -e "Usage: $0 TEST_BINARY_PATH [args]\n"

  if ! [ -z "$testbench" ]; then
    echo -e "Call run for ${testbench#$REPO_ROOT} testbench\n"
  else
    echo -e "Call run for <testbench>\n"
  fi

  cat << EOF
  Args:
-h|--help            : Display this help
-d|--debug           : Enable debug (i.e. log waveforms and enable CPU trace dump"
--fc|--force_compile : Compile testbench before run (i.e. NODEPS=0). NODEPS=1 by default.
--release            : link to release instead of locally compiled testbench
--gui                : Run  the test with visualizer GUI opened. '--gui' and '--gui --debug' are equivalent

EOF
}

testbench=
debug=0
gui=0
nodeps=1
link_release=0
make_opts=()
plus_args=()

add_debug_opts() {
  make_opts+=("DEBUG=$1")
  plus_args+=("+dump_ax65_instructions=$1")
  plus_args+=("+dump_cva6v_instructions=$1")
}

parse_args() {
  local show_help=0

  # handle the case were the script is called just with '-h'
  if [[ "$1" == +(-h|--help) ]]; then
    show_help=1
  else
    test_binary="$1"
    hex_path="$(dirname $1)/texthexify/$(basename $1)"
    plus_args+=("+HEX_PATH=$hex_path")
    make_opts+=("TESTNAME=$(basename $test_binary)")
    make_opts+=("VSIM_RUN_DIR=$(dirname $test_binary)")
  fi
  shift

  while [[ $# > 0 ]]; do
    case "$1" in
      -h|--help) show_help=1
        shift
        ;;
      -d|--debug)
        debug=1
        shift
        ;;
      --gui)
        debug=1
        gui=1
        shift
        ;;
      --fc|--force_compile)
        nodeps=0
        shift
        ;;
      --uvm_testname=*)
        uvm_testname=${1#*=}
        shift
        ;;
      --testbench=*)
        testbench=${1#*=}
        shift
        ;;
      --release_dir=*)
        release_dir="${1#*=}"
        shift
        ;;
      --release)
        link_release=1
        shift
        ;;
      --simulator=*)
        echo "Warning: '--simulator' option is ignored. The simulation will be run on vsim."
        shift
        ;;
      --memory=*)
        local mem="${1#*=}"
        # Generate texthex files
        if [[ "$mem" == *"spm"* ]]; then
          texthexify --elf "$test_binary" -w 64 --memory "$mem"
        elif [[ "$mem" == *"l1"* ]]; then
          texthexify --elf "$test_binary" -w 128 --memory "$mem"
        elif [[ "$mem" == *"ddr"* ]]; then
          texthexify --elf "$test_binary" -w 256 --memory "$mem"
        elif [[ "$mem" == "l2" ]]; then
          texthexify --elf $test_binary -w 128 --memory l2 --l2_interleaving INTER_1X8_4K
        else
          error "Unknown memory type '$mem'. Expected 'spm', 'l1' or 'ddr'."
        fi
        shift
        ;;
      +*)
        plus_args+=("$1")
        shift
        ;;
      *)
        make_opts+=("$1")
        shift
        ;;
    esac
  done

  # Opts are added at the end to allow overload
  make_opts+=("NODEPS=$nodeps")
  make_opts+=("UVM_TESTNAME=$uvm_testname")
  make_opts+=("GUI=$gui")
  add_debug_opts $debug

  if [[ $show_help == 1 ]]; then
    print_help
    exit 0
  fi
}

check_tb() {
  local tb_dir="$1"
  if ! [ -d $tb_dir/build_vsim_*/compile_vsim ] && [[ $nodeps == 1 ]]; then
    echo "No testbench built!"
    exit 1
  fi
}

######################################
# Main program
######################################

parse_args $@

if [ -z "$test_binary" ]; then
  echo "Test binary not found!"
  print_help
  exit 1
fi
echo "TEST_NAME: $(basename $test_binary)"

if ((link_release)); then
  link_release_path="$release_dir/link_to_release"
  [ -f "$link_release_path" ] || error "$link_release_path does not exist"
  $link_release_path
fi

check_tb $testbench
test_dir=$(dirname $test_binary)
cd $test_dir
rm -f sim_dir
ln -s $testbench sim_dir
rm -f "qwave.db.lock" # happens when previous sim was killed
make -C $testbench run_vsim ${make_opts[@]} VSIM_RUN_OPTS_EXT="${plus_args[*]}"
