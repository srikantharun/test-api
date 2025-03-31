#!/usr/bin/env bash

current_dir=$(pwd)
wrapper_flag=0
dryrun_flag=0
skip_cc_flag=0
dft_flag=0
usage() {
  echo "Description:"
  echo "SCript to setup a coreconsultant workspace for the LPDDR ctrl. This script uses the version of the lpddr release you have selected using  <module load lpddr>"
  echo "Usage: $0 [-p] [-h]"
  echo "  -p         Run the simulation including the inv_wrapper, _p wrapper, and subsys wrapper"
  echo "  -d         DryRun setup everything, but do not start the compile or simulation itself. (Setup does required running coreConsultant workspace gen)"
  echo "  -s         Skip coreConsultant workspace creation, assume there is an existing workspace with the correct name."
  echo "  -t         Run the simulation on the DFT inserted RTL, this required -p as well."
  echo "  -h         Display this help message"
  exit 1
}

while getopts "pdsth" opt; do
  case $opt in
    p)
      wrapper_flag=1
      ;;
    d)
      dryrun_flag=1
      ;;
    s)
      skip_cc_flag=1
      ;;
    t)
      dft_flag=1
      ;;
    h)
      usage
      ;;
    \?)
      usage
      ;;
  esac
done

cd $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default

# Create the workspace
if [ "$skip_cc_flag" -eq 0 ]; then
  # Create a new clean workspace with the simulation sources setup.
  # Using -s option to trigger simulation dry-run to populate the vip scratch dir with the required files.
  # We need to use gcc 9.x for this
  module switch gcc/9.2.0
  ./scripts/create_workspace.sh -n ${LPDDR_VERSION}_simulations -f -s
fi

# Check that the workspace is where it should be.
if [ ! -d $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default/workspaces/${LPDDR_VERSION}_simulations ]; then
  echo "ERROR: expected workspace directory $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default/workspaces/${LPDDR_VERSION}_simulations does not exists, try running without the -s flag to create it."
  exit 1
fi

# Check that if the dft flag is set, the wrapper flag is set as well
if [ "$dft_flag" -eq 1 ]; then
  if [ "$wrapper_flag" -eq 0]; then
    echo "ERROR: if -t is set, -p should be set as well, exiting"
    exit 1
  fi
fi

# Set the name of the sim run dir, depends on the wrapper setting to be able to have both setups at the same time.
if [ "$wrapper_flag" -eq 0 ]; then
  local_sim_dir=sim_${LPDDR_VERSION}_snps_run_dir
else
  local_sim_dir=sim_${LPDDR_VERSION}_axe_run_dir
fi

# SETUP the SNPS sim dir
# Clean up the previous dir.
if [ -d ./workspaces/$local_sim_dir ]; then
  rm -rf ./workspaces/$local_sim_dir
fi

# Copy the SNPS SS sim release dir to a local location
mkdir ./workspaces/$local_sim_dir
cp -rf ${DDR_SUBSYSTEM_RTL_PATH}/sim workspaces/$local_sim_dir/sim
cd workspaces/$local_sim_dir/sim

# Setup all required PATH variables as described in sim_readme.txt
# 3. Please setup below env variables.
# 	DDR_SS_DIR             -> <subsystem_workspace_path> , i.e, <ss_sim_path(pwd)>/..
# 	DDR_SS_RTL_PATH        -> current  Subsystem WS that is released .
# 	DDR_SS_CC_DIR          -> Configured DDR Controller
# 	DDR_SS_SVT_VIP_DIR     -> VIP path point to the scratch directory that is generated after running coreConsultant for controller.
# 	DDR_SS_PHY_PATH        -> Configured PHY path after running coreConsultant with PHY corekit.
# 	DDR_MEM_PATH           -> Current Subsystem WS Components path.

# Example (If you are inside <ss_sim_path>):
# 	setenv DDR_SS_RTL_PATH   	/remote/us01sgnfs00726/DDR_SS/Axelera_Europa/kkamlesh/Europa/lpddr5x54x_config/ddr_chip_subsys/ws_snps_ddr_subsystem/
# 	setenv DDR_SS_CC_DIR    	/remote/us01sgnfs00901/DWC_ddr_subsystem/customer/axelera/corekits/CTRL/09042024/ws_controller/
# 	setenv DDR_SS_PHY_PATH  	/remote/us01sgnfs00901/DWC_ddr_subsystem/customer/axelera/corekits/PHY/06102024/axelera_lpddr_phy_config_06102024/
# 	setenv DDR_SS_DIR       	$PWD/../
# 	setenv DDR_SS_SVT_VIP_DIR 	/remote/us01sgnfs00901/DWC_ddr_subsystem/customer/axelera/corekits/CTRL/08092024/AXELERAAI_EUROPA_AXI_IPHY_SIMULATION/scratch
# 	setenv DDR_MEM_PATH 	    $DDR_SS_RTL_PATH/components

export DDR_SS_DIR=$DDR_SUBSYSTEM_RTL_PATH
export DDR_SS_RTL_PATH=$DDR_SUBSYSTEM_RTL_PATH
export DDR_SS_CC_DIR="$REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default/workspaces/${LPDDR_VERSION}_simulations"
export DDR_SS_SVT_VIP_DIR=${DDR_SS_CC_DIR}/scratch
export DDR_SS_PHY_PATH=$DDR_PHY_RTL_PATH
## DDR_MEM_PATH is set when loading lpddr as a module and is correct as is.
# export DDR_MEM_PATH           -> Current Subsystem WS Components path.


# Taken from set_sim_env
export SS_INTERNAL=1
export UMCTL2_OS_VERSION="WS7.0|CS7.0|CS7.3"
export UMCTL2_QSUB_OPTIONS="os_distribution=redhat|centos,os_version=${UMCTL2_OS_VERSION}"
export RCE_PALS_QSUB_RESOURCE=${UMCTL2_QSUB_OPTIONS}

# Update the shebang/path that snps uses for perl with where our perl executable is located.
grep -rl /depot/Perl/perl-5.8.3/bin/perl . | xargs sed -i 's#/depot/Perl/perl-5.8.3/bin/perl#/usr/bin/perl#g'

# Make sure slurm is used by adding it in front of every runtest command in the make file
sed -i s+./runtest+srun\ ./runtest+g Makefile

# Disable UUMmode to avoid errors on delay_mode_path
sed -i s+--UUMFlow\ \"1\"+--UUMFlow\ \"0\"+g Makefile

# Run presetup, this creates a bunch of soft-links to (rtl) sources
make  presetup

# If the wrapper flag is set, go about and modify the snps setup to include our wrappers
if [ "$wrapper_flag" -eq 1 ]; then
  axelera_hier=ddr_chip_inv_wrapper.axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst
  # Adapt the dut to target our inv wrapper
  sed -i "s/snps_ddr_subsystem ddr_chip (/lpddr_subsys_inv_wrapper ddr_chip_inv_wrapper (/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
  # Adapt the hierachy used in some force and bind statements from snps
  sed -i "s/ddr_chip.i_DWC_lpddr5x_phy/$axelera_hier.i_DWC_lpddr5x_phy/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
  sed -i "s/ddr_chip.i_uddrctl/$axelera_hier.i_uddrctl/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
  # sed -i "s/U_ddr_chip_wrapper.ddr_chip.i_DWC_lpddr5x_phy/U_ddr_chip_wrapper.$axelera_hier.i_DWC_lpddr5x_phy/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
  # Update all hierarchical paths containing "U_ddr_chip_wrapper.ddr_chip" to $axelera_hier as to intercept axelera's wrapper changes
  grep -rl --include \*.sv --include \*.svh --include \*.el "\.ddr_chip" ./testbench | xargs sed -i "s/\.ddr_chip/.$axelera_hier/g"

  # Append the compile file list from snps to include all required axelera files.
  # Std-cell models are required cause our sync cells use some syncs that are not included in the premapped files from snsp.
  echo "/data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.10/FE-Common/MODEL/ln05lpe_sc_s6t_flk_lvt_c54l08/ln05lpe_sc_s6t_flk_lvt_c54l08.v" >> ./testbench/modules/compile.f
  echo "/data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/FE-Common/MODEL/ln05lpe_sc_s6t_flk_rvt_c54l08/ln05lpe_sc_s6t_flk_rvt_c54l08.v" >> ./testbench/modules/compile.f
  # Use bender without the snps subsys dependency and only keep files in the repo to avoid samsung libs
  if [ "$dft_flag" -eq 1 ]; then
    bender script flist-plus -d $REPO_ROOT/hw/impl/europa/blocks/lpddr/rtl/dft -t asic -t rtl -t sf5a -t dft -t simulation -t vcs | grep -v /data/foundry/LIB/synopsys/lpddr5x | grep -v /data/foundry/samsung/sf5a/memory/ >> ./testbench/modules/compile.f
  else
    bender script flist-plus -d $REPO_ROOT/hw/impl/europa/blocks/lpddr/rtl -e synopsys_lpddr_subsys -t asic -t rtl -t sf5a -t simulation -t vcs | grep $REPO_ROOT >> ./testbench/modules/compile.f
  fi
  # Inv wrapper is not included in bender deps.
  echo "/home/projects_2/workspace/ruytterh/europa/europa_rtl_repo/hw/impl/europa/blocks/lpddr/rtl/generated/lpddr_subsys_inv_wrapper.sv" >> ./testbench/modules/compile.f
  # Add delay_mode_path as a vcs compile option to avoid timing issues cause by focring clocks over the pctl clock gates.
  sed -i '/$main::common_compile_options.= " +vcs+loopdetect ";/a $main::common_compile_options.= " +delay_mode_path ";' runtest.pm
fi

# Create the workspace
if [ "$dryrun_flag" -eq 0 ]; then
  # Compile step
  make  compile_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=18 NUM_RANK=2

  # Run set, this will run all tests in workspaces/sim_${LPDDR_VERSION}_run_dir/sim/testlists/dwc_ddrctl.rel.testlist
  # It will take a while
  make  run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=18 NUM_RANK=2
fi
# Further options to change the LPDDR speedbin and density setup.
# --> Options for make command:

#  SPEED_BIN_LP5 = <SPEED_BIN> :- Specifies Speed Bins for the configuration
#      ======================================
#      |  SPEED  |     SPEED_BIN_LP5 value  |
#      ======================================
#      |  8533   |           14             |
#      ======================================
#      |  6400   |           12             |
#      ======================================
#      |  4800   |           9              |
#      ======================================
#      |  4267   |           8              |
#      ======================================
#      |  3200   |           6              |
#      ======================================
#      |  2133   |           4              |
#      ======================================


#  DEV_SEL_LP5 = <DEVICE_SEL> :- Specifies Device Ranges Density
#      ======================================================================
#      |        DEVICE                               |    DEV_SEL_LP5 value |
#      ======================================================================
#      | 	2GB_8MB_16DQ_4BK_4BG_PER_CHANNEL	       |           1          |
#      ======================================================================
#      | 	3GB_12MB_16DQ_4BK_4BG_PER_CHANNEL	       |           2          |
#      ======================================================================
#      |	4GB_16MB_16DQ_4BK_4BG_PER_CHANNEL	       |           3          |
#      ======================================================================
#      |	6GB_24MB_16DQ_4BK_4BG_PER_CHANNEL	       |           4          |
#      ======================================================================
#      |	8GB_32MB_16DQ_4BK_4BG_PER_CHANNEL	       |           5          |
#      ======================================================================
#      |	12GB_48MB_16DQ_4BK_4BG_PER_CHANNEL         |           6          |
#      ======================================================================
#      |	16GB_64MB_16DQ_4BK_4BG_PER_CHANNEL	       |           7          |
#      ======================================================================
#      |	24GB_96MB_16DQ_4BK_4BG_PER_CHANNEL	       |           8          |
#      ======================================================================
#      |	32GB_128MB_16DQ_4BK_4BG_PER_CHANNEL	       |           9          |
#      ======================================================================
#      |  32GB_256MB_8DQ_4BK_4BG_PER_CHANNEL         |           18         |
#      ======================================================================
#      | 	2GB_8MB_16DQ_16BK_PER_CHANNEL	           |           19         |
#      ======================================================================
#      | 	32GB_128MB_16DQ_16BK_PER_CHANNEL           |           27         |
#      ======================================================================

#  NUM_RANK = <num_rank> :- Specifies Number of Ranks(1,2)
#  ECOV = 1 :- This is used to launch the tests with coverage enabled
#  WAVE = 1 :- This is to enable wave dumping for the tests

#  REGRESS = 1 :- This is used in make run to launch the tests in grid for execution in parallel

# --> Possible combinations of configurations (LPDDR5):
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=1  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=2  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=3  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=4  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=5  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=6  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=7  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=8  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=9  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=18 NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=1  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=2  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=3  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=4  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=5  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=6  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=7  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=8  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=9  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=18 NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=1  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=2  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=3  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=4  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=5  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=6  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=7  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=8  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=9  NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=18 NUM_RANK=1
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=1  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=2  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=3  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=4  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=5  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=6  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=7  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=8  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=9  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=12 DEV_SEL_LP5=18 NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=1  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=2  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=3  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=4  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=5  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=6  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=7  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=8  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=9  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=9 DEV_SEL_LP5=18 NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=1  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=2  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=3  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=4  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=5  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=6  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=7  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=8  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=9  NUM_RANK=2
#   make compile_lp5/run_lp5 SPEED_BIN_LP5=8 DEV_SEL_LP5=18 NUM_RANK=2

# Jump back to the original start directory
cd $current_dir
