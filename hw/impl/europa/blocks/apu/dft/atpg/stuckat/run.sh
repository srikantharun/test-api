#!/usr/bin/env bash

# Directories
git_root=$(git rev-parse --show-toplevel)
workdir=$(pwd)
SRUN="srun -J tessent_atpg --pty --x11 -c32 --mem=32G"

# Environment
export DEPENDENCIES_DIR="$(readlink -f ./build_dependencies)"
export TESSENT_DC_PATH="$SYNOPSYS/bin"
mkdir -p ${workdir}/log
# Run tessent
${SRUN} tessent -shell -dofile ${workdir}/$(basename ${workdir}).do -log ${workdir}/log/atpg_`date +log_file_%m_%d_%y_%H_%M_%S`

