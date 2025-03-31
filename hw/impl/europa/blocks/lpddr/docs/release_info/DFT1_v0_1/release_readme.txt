General notes on the Axelera release structure

RELEASE VERSION

DFT1 v0.1

DIRECTORY structure

- src: all added or modified source files
- constraints: constraint files to be used
- scan_scripts: contains scan related script to be executed on snps side
- sim: contains simulation setup related files and scripts.
- config: contains filelist to be used

CONFIG

all_axe_files.lst: all files in the Axelera release
modified_files.lst: all files that existed in the SS2 release that have been modified by Axelera
lpddr_axe_rtl_sim.lst: lpddr_ss_rtl_sim.lst appended with the added files. You can use DDR_AXE_RTL_PATH variable to point to the Axelera files

SCAN_SCRIPTS

Script to be used for scan chain insertion. Modification of memory model paths will be required.

SIM

adapt_sim_setup.sh is a script that should be sourced between the make presetup and the make compile_lp5 command of the snps subsys simulation flow in the sim dir.
It adapts hierarchical paths to intercept the additional levels of hierarchy created by the axelera wrappers.
It also adds a bunch of extra compile source to the compile.f file picked up by the compilation flow.

All this is experimental, and can be replaced by other means to reach the same goal of running the simulations. This approach works on axelera side, and has been included as an example.

CONSTRAINTS

Included constraints are in a pre-draft stage and should not be used. We will need a FC database to develop these constraints properly.
