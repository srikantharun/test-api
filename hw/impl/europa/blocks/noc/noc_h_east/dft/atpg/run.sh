#!/usr/bin/env bash

set -e
set -o pipefail

# Directories
git_root=$(git rev-parse --show-toplevel)
workdir=$(pwd)

# Environment
export DEPENDENCIES_DIR="$(readlink -f ./build_dependencies)"
export TESSENT_DC_PATH="$SYNOPSYS/bin"

# Cleanup
rm -rf tsdb_outdir
rm -rf rpt
mkdir -p ${workdir}/log
mkdir -p ${workdir}/rpt

# Run tessent
tessent -shell -dofile ${workdir}/$(basename ${workdir}).do -log ${workdir}/log/$(basename ${workdir})_$(date +%Y-%m-%d_%H:%M:%S).log


