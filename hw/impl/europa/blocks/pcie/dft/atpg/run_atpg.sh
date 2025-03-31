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



# Run tessent
tessent -shell -dofile atpg.do -log ${workdir}/log/$(basename ${workdir})_$(date +%Y-%m-%d_%H:%M:%S).log

