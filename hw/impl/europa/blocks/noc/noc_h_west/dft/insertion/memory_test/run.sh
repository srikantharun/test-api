#!/usr/bin/env bash

set -e
set -o pipefail

# Directories
git_root=$(git rev-parse --show-toplevel)
workdir=$(pwd)
dft_scripts="${git_root}/hw/impl/europa/dft/scripts"
bender_mani_loc=$(readlink -f ../../../rtl)
# Executables
bender_to_tessent="${dft_scripts}/bender_to_tessent.sh"
postprocess_tsdb="${dft_scripts}/postprocess_tsdb.sh"
# Environment
export DEPENDENCIES_DIR="$(readlink -f ./build_dependencies)"
export TESSENT_DC_PATH="$SYNOPSYS/bin"

# Cleanup
rm -rf tsdb_outdir
rm -rf ${DEPENDENCIES_DIR}
mkdir -p ${DEPENDENCIES_DIR}
mkdir -p ${workdir}/rpt
mkdir -p ${workdir}/log

# Dependencies
# Create RTL read script from 
bender -d ${bender_mani_loc} update
bender -d ${bender_mani_loc} script flist-plus -t rtl -t asic -t sf5a -t tessent > ${DEPENDENCIES_DIR}/bender.flist
${bender_to_tessent} ${DEPENDENCIES_DIR}/bender.flist ${DEPENDENCIES_DIR}/read_rtl.do

# Run tessent
tessent -shell -dofile ${workdir}/$(basename ${workdir}).do -log ${workdir}/log/$(basename ${workdir})_$(date +%Y-%m-%d_%H:%M:%S).log

if [[ $(basename ${workdir}) == logic_test ]];
then
    ${postprocess_tsdb}
fi
