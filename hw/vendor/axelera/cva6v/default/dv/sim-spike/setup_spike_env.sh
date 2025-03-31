#!/bin/bash

# Function to check if environment variables are set and non-empty
check_env() {
    if [ -z "${!1}" ]; then
        echo -e "\033[1;31mError: Environment variable $1 is not set or is empty.\033[0m"
    fi
}

# Function to load a module if not already loaded, with feedback
load_module() {
    if ! module list 2>&1 | grep -q "$1"; then
        module load "$1"
        echo "$1 module loaded now."
    else
        echo "$1 module already loaded, so not loading again."
    fi
}

# Load modules with check and feedback
load_module gcc/10.5.0
load_module riscv/spike/2024_03_08
load_module cva6v_isacov/2024_04_23
load_module axelera-riscv-toolchain/0.1.0
load_module imperas/20240305


# Export other variables
export CVA6_VERIF_HOME="$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/deps"
export SIM_SPIKE="$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/sim-spike"
export DV_SCRIPTS="$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/scripts"

# Print module list
module list

# Print a message indicating successful setup
echo "REPO_ROOT is set to: $REPO_ROOT"
echo "CVA6_VERIF_HOME set to: $CVA6_VERIF_HOME"
echo "SPIKE_HOME set to: $SPIKE_HOME"
echo "DV_SCRIPTS set to: $DV_SCRIPTS"
echo "SIM_SPIKE set to: $SIM_SPIKE"
echo "CVA6V_ISACOV_HOME set to: $CVA6V_ISACOV_HOME"
echo "IMPERAS_HOME set to: $IMPERAS_HOME"
echo "Environment variables set."

# Check required environment variables
check_env "CVA6_VERIF_HOME"
check_env "REPO_ROOT"
check_env "SPIKE_HOME"
check_env "CVA6V_ISACOV_HOME"
# Check additional environment variables after exports
check_env "IMPERAS_HOME"
check_env "SIM_SPIKE"
check_env "DV_SCRIPTS"
