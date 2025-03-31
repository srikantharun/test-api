#!/bin/sh
# make FIRMWARE_PATH=/remote/us01sgnfs00901/DWC_ddr_subsystem/customer/axelera/corekits/PHY/10162024/config_axelera_090a_phy_10162024/firmware/Latest/training SR_FW_FILES_LOC=/slowfs/us01dwt2p532/vasanthi/AXELERAAI_EUROPA_AXI_IPHY_SIMULATION/sim/sw_utilities/phy/firmware/save_restore >& phyinit_lpddr5x_compile.log
make FIRMWARE_PATH=/home/rodrigo.borges/workspace/hw/europa_cinit_ss4/sw/scripts/lpddr/synopsys/sim/sw_utilities/phy/firmware SR_FW_FILES_LOC=/home/rodrigo.borges/workspace/hw/europa_cinit_ss4/sw/scripts/lpddr/synopsys/sim/sw_utilities/phy/firmware/save_restore >& phyinit_lpddr5x_compile.log
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

