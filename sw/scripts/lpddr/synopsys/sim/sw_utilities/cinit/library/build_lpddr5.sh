#!/bin/sh
make --directory=../ clean-all PROTOCOL=lpddr5 CINIT_PLATFORM=simulation
make --directory=../ load-hw-config CINIT_PLATFORM=simulation PROTOCOL=lpddr5 PHY_VDEFINES_FILE=/home/rodrigo.borges/workspace/hw/europa_cinit_ss4/sw/scripts/lpddr/synopsys/sim/testbench/macros/dwc_ddrphy_VDEFINES.v
make --directory=../ gen-verilog-headers PROTOCOL=lpddr5 CINIT_PLATFORM=simulation
make --directory=../ LINK_PHYINT=1 CINIT_PLATFORM=simulation PHY_VDEFINES_FILE=/home/rodrigo.borges/workspace/hw/europa_cinit_ss4/sw/scripts/lpddr/synopsys/sim/testbench/macros/dwc_ddrphy_VDEFINES.v PROTOCOL=lpddr5
if [ $? -eq 0 ]
then
  echo "CINIT compiled ok"
else
  exit 1
fi

