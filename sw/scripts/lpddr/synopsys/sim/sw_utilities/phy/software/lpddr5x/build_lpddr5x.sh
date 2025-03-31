#!/bin/sh
make FIRMWARE_PATH=/remote/us01dwt1p095/garrigan/p4work/umctl5/dev_lpddr54_1.60a_lca00/DWC_ddr_umctl5/lib_axelera/AXELERAAI_EUROPA_AXI_IPHY_SIMULATION/sim/sw_utilities/phy/firmware SR_FW_FILES_LOC=/remote/us01dwt1p095/garrigan/p4work/umctl5/dev_lpddr54_1.60a_lca00/DWC_ddr_umctl5/lib_axelera/AXELERAAI_EUROPA_AXI_IPHY_SIMULATION/sim/sw_utilities/phy/firmware/save_restore >& phyinit_lpddr5x_compile.log 
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

