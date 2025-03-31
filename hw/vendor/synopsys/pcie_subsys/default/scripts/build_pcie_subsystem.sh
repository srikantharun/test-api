#!/bin/sh

###### Set Enviroment Variables ######
#DESIGNWARE_HOME=/global/cust_apps_sgip001/dw_internal
#export DESIGNWARE_HOME
echo "\$DESIGNWARE_HOME=$DESIGNWARE_HOME"

#PCIE_PHY_PATH=/remote/us01sgnfs00725/DWC_pcie_subsystem/axelera_europa/PHY/synopsys/dwc_pcie4phy_sssf5a_x4ns/2.01a

#export PCIE_PHY_PATH
echo "\$PCIE_PHY_PATH=$PCIE_PHY_PATH"

PCIE_PRODUCT=DWC_pcie_ctl
export PCIE_PRODUCT
echo "\$PCIE_PRODUCT=$PCIE_PRODUCT"

PCIE_VERSION=6.20a
export PCIE_VERSION
echo "\$PCIE_VERSION=$PCIE_VERSION"

PCIE_CTRL_WS=Axelera_Europa_pcie_gen4_ctrl_6.20a_SS2
export PCIE_CTRL_WS
echo "\$PCIE_CTRL_WS=$PCIE_CTRL_WS"

#PCIE_WORKSPACE=`pwd`
#export PCIE_WORKSPACE
echo "\$PCIE_WORKSPACE=$PCIE_WORKSPACE"

PCIE_CTRL_CONFIG=Axelera_Europa_pcie_gen4_ctrl_6.20a_SS2_Latest.tcl
export PCIE_CTRL_CONFIG
echo "\$PCIE_CTRL_CONFIG=$PCIE_CTRL_CONFIG"

###### Check Enviroment Variables ######
echo "Check enviroment variable PCIE_PHY_PATH ..."
if [ -z $PCIE_PHY_PATH ]; then
  echo "ERROR! Enviorment viariable \$PCIE_PHY_PATH is not set."
  exit 1
else
  echo "\$PCIE_PHY_PATH=$PCIE_PHY_PATH"
fi

echo "Check enviroment variable \$DESIGNWARE_HOME ..."
if [ -z $DESIGNWARE_HOME ]; then
  echo "ERROR! Enviorment viariable \$DESIGNWARE_HOME is not set."
  exit 1
else
  echo "\$DESIGNWARE_HOME=$DESIGNWARE_HOME"
fi


echo "Check enviroment variable \$CT_HOME ..."
if [ -z $CT_HOME ]; then
  echo "ERROR! Enviorment viariable \$CT_HOME is not set."
  exit 1
else
  echo "\$CT_HOME=$CT_HOME"
fi

###### Create PCIe Workspace ######
if [ -d "$PCIE_WORKSPACE/$PCIE_CTRL_WS" ];then
  echo "Skip building workspace"
else
  ####### Create Workspace ######
  echo "Creating Controller workspace for the configuration ..."
  $CT_HOME/bin/coreConsultant -shell -f $PCIE_CTRL_CONFIG
fi

PCIE_X4_CTRL_PATH=${PCIE_WORKSPACE}/${PCIE_CTRL_WS}
export PCIE_X4_CTRL_PATH


###### Build Subsystem ######
if [ -d "./subsystem" ];then
  echo "Removing old Subsystem database ..."
  rm -rf ./subsystem
fi

echo "Building subsystem ..."
mkdir -p ./subsystem
cd ./subsystem

\cp -Trf ../db/rpt         ./rpt
\cp -Trf ../db/doc         ./doc
\cp -Trf ../db/sim_uvm     ./sim_uvm
\cp -Trf ../db/src         ./src
\cp -Trf ../db/syn         ./syn
\cp -Trf ../db/spyglass    ./spyglass
\cp -Trf ../db/checksum_ss ./checksum_ss

#
##### The end ######
echo "DWC_pcie_subsystem is now ready!"
