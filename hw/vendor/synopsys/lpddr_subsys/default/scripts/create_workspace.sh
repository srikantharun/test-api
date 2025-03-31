#!/usr/bin/env bash

current_dir=$(pwd)
name_arg="my_workspace"
clean_flag=0
overwrite_flag=0
swutil_flag=0
usage() {
  echo "Description:"
  echo "SCript to setup a coreconsultant workspace for the LPDDR ctrl. This script uses the version of the lpddr release you have selected using  <module load lpddr>"
  echo "Usage: $0 [-n string] [-c] [-f] [-s] [-h]"
  echo "  -n string  Name of the workspace"
  echo "  -c         Clean all other existing workspaces"
  echo "  -f         Overwrite any existing workspace with the same name."
  echo "  -s         Include the generation of sw_util sources for the driver development -> does simulation dry-run"
  echo "  -h         Display this help message"
  exit 1
}

while getopts "n:cfsh" opt; do
  case $opt in
    n)
      name_arg=$OPTARG
      ;;
    c)
      clean_flag=1
      ;;
    f)
      overwrite_flag=1
      ;;
    s)
      swutil_flag=1
      ;;
    h)
      usage
      ;;
    \?)
      usage
      ;;
  esac
done

# Check that the LPDDR version is set
if [ -z "${LPDDR_VERSION+x}" ]; then
  echo "ERROR: LPDDR version not correcty set. Use module load lpddr/version to get all variables set."
  exit 1
else
  echo "INFO: using LPDDR version $LPDDR_VERSION"
  echo "INFO: using SNPS CTRL DDR IP $DDR_CONTROLLER_IP_HOME"
  echo "INFO: using SNPS CTRL DDR primeprofile $DDR_CONTROLLER_PRIMEPROFILE"
fi

# Move to the right place
cd $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default

# Remove all workspaces if any exist
if [ "$clean_flag" -eq 1 ]; then
    if [ -d "workspaces" ]; then
        echo "INFO: removing all workspaces"
        rm -rf workspaces
        # Sleep to make sure everything is really gone by the time coreConsultant starts
        sleep 0.5
    fi
fi

# Overwrite any existing workspace with the same name
if [ "$overwrite_flag" -eq 1 ]; then
    echo "INFO: Overwrite flag set"
    if [ -d "workspaces" ]; then
        echo "INFO: Existing workspaces found"
        if [ -d "workspaces/$name_arg" ]; then
            echo "INFO: Removing workspaces/$name_arg"
            rm -rf workspaces/$name_arg
            # Sleep to make sure everything is really gone by the time coreConsultant starts
            sleep 0.5
        fi
    fi
fi

# Setup the directories
mkdir -p workspaces
cd workspaces

# Call the coreConsultant script.
export SNPS_DDR_WORKSPACE_NAME=$name_arg
export SNPS_DDR_WORKSPACE_SETUP_SWUTIL=$swutil_flag
coreConsultant -shell -f ../scripts/create_workspace.tcl | tee ${name_arg}_cc.log

corecon_dir=$(pwd)
echo "INFO: workspace created under $corecon_dir"

cd $current_dir


