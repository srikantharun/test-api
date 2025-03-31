#!/bin/sh
make --directory=../ clean-all PROTOCOL=lpddr4 CINIT_PLATFORM=simulation
make --directory=../ load-hw-config CINIT_PLATFORM=simulation PROTOCOL=lpddr4 PHY_VDEFINES_FILE=/remote/us01dwt1p095/garrigan/p4work/umctl5/dev_lpddr54_1.60a_lca00/DWC_ddr_umctl5/lib_axelera/AXELERAAI_EUROPA_AXI_IPHY_SIMULATION/sim/testbench/macros/dwc_ddrphy_VDEFINES.v
make --directory=../ gen-verilog-headers PROTOCOL=lpddr4 CINIT_PLATFORM=simulation
make --directory=../ LINK_PHYINT=1 CINIT_PLATFORM=simulation PHY_VDEFINES_FILE=/remote/us01dwt1p095/garrigan/p4work/umctl5/dev_lpddr54_1.60a_lca00/DWC_ddr_umctl5/lib_axelera/AXELERAAI_EUROPA_AXI_IPHY_SIMULATION/sim/testbench/macros/dwc_ddrphy_VDEFINES.v PROTOCOL=lpddr4
if [ $? -eq 0 ] 
then
  echo "CINIT compiled ok"
else
  exit 1
fi

