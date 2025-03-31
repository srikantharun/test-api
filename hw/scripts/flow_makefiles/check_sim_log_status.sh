#!/usr/bin/env bash

set -e


#--------------------------------------------------------------
# functions
#--------------------------------------------------------------
usage() {
  cat << EOF
usage: $(basename $0) [ARGS] SIM_LOG

returns 1 if SIM_LOG indicates a failure

where ARGS are:
  -h|--help               : display this help
  --simulator SIMULATOR   : set SIMULATOR to either "vsim" or "vcs" (default: vsim)
  --uvm UVM               : check for UVM report if UVM=1 (default: 1)

EOF
}

error() {
  >&2 echo "ERROR: $@"
  exit 1
}


#--------------------------------------------------------------
# execution
#--------------------------------------------------------------
simulator="vsim"
uvm=1
dft_tb=0

while [ "$#" -gt 0 ]
do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --simulator)
      shift 1
      simulator=$1
      shift 1
      ;;
    --uvm)
      shift 1
      uvm=$1
      shift 1
      ;;
    --dft_tb)
      shift 1
      dft_tb=$1
      shift 1
      ;;
    --*)
      usage
      error "$1 is not a valid argument"
      ;;
    *)
      sim_log="$1"
      shift 1
      ;;
  esac
done

[ -f "$sim_log" ] || error "sim_log=$sim_log is not a file"

return_value=1

# 1. check for must see strings
if ((uvm)); then
  (grep 'UVM_ERROR :    0' $sim_log && grep 'UVM_FATAL :    0' $sim_log) &> /dev/null && return_value=0
elif ((dft_tb)); then
  grep "No error between simulated and expected patterns" $sim_log &> /dev/null && return_value=0
else
  return_value=0
fi

# 2. check for typical errors
# simple test to check assert/error/fatal in vcs and vsim:
# https://git.axelera.ai/antoine.madec/test_axelera/-/tree/master/check_sim_log_status
if [ "$simulator" = "vcs" ]; then
  grep '	Offending ' $sim_log &> /dev/null && return_value=1         # assert()
  grep '^Error: ' $sim_log &> /dev/null && return_value=1             # $error()
  grep '^Fatal: ' $sim_log &> /dev/null && return_value=1             # $fatal()
  grep 'Timing violation in' $sim_log &> /dev/null && return_value=1  # timing violation
elif [ "$simulator" = "vsim" ]; then
  grep '^# \*\* Error:' $sim_log &> /dev/null && return_value=1   # assert(), $error() and timing violation
  grep '^# \*\* Fatal:' $sim_log &> /dev/null && return_value=1   # $fatal()
else
  error "unknown simulator $simulator"
fi

# 3. check for block specific errors
grep 'SimulError' $sim_log &> /dev/null && return_value=1   # NOC errors
grep "SvtTestEpilog: Failed" $sim_log &> /dev/null && return_value=1 # SVT VIP errors

exit $return_value
