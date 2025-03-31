#!/bin/sh
make FIRMWARE_PATH=/home/projects_2/workspace/bdrasko/europa/hw/vendor/synopsys/lpddr_subsys/default/workspaces/Europa_lpddr_ctrl_config_lp5x_1_60a/sim/sw_utilities/phy/firmware SR_FW_FILES_LOC=/home/projects_2/workspace/bdrasko/europa/hw/vendor/synopsys/lpddr_subsys/default/workspaces/Europa_lpddr_ctrl_config_lp5x_1_60a/sim/sw_utilities/phy/firmware/save_restore >& phyinit_lpddr5_compile.log 
if [ $? -eq 0 ] 
then
  echo "PHYINIT compiled ok"
if [ -d "../lpddr5_64" ]; then rm -rf ../lpddr5_64; fi
mkdir ../lpddr5_64
cp -rf obj/* ../lpddr5_64/
make clean
else
  exit 1
fi

