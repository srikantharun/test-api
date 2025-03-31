General notes on the Axelera release structure

RELEASE VERSION

DFT1 v5.0

DIRECTORY structure

- src: all added or modified source files
- constraints: constraint files to be used
- scan_scripts: contains scan related script to be executed on snps side
- sim: contains simulation setup related files and scripts.
- config: contains filelist to be used

CONFIG

all_axe_files.lst: all files in the Axelera release
modified_files.lst: all files that existed in the SS2 release that have been modified by Axelera
pcie_axe_rtl_sim.lst: pcie_ss_rtl_sim.lst appended with the added files. You can use PCIE_AXE_RTL_PATH variable to point to the Axelera files
defines_sim.lst: defines to be used for simulation
defines_synt.lst: defines to be used for synthesis

SCAN_SCRIPTS

Script to be used for scan chain insertion. Modification of memory model paths will be required.

CONSTRAINTS

Included constraints are the full functional constraints matching the newest RTL changes in the pcie_p wrapper.
