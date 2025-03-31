General notes on the Axelera release structure

RELEASE VERSION

DFT3 v3

RELEASE notes

- Integration of SS4 SNPS subsys team release
- Fixed constraint issue related to InternalBypassClk by adding -edges option to generated clock statement (as discussed in solvnet case 01786908)
- Fixed missing constraints on o_*_obs ports
- Connected AXI and DDRC low power interfaces to axelera low power controller in the lpddr_p top-level module (as discussed in solvnet case 01806936)
- DFT refixes and respin on latest RTL
  - fixed floating test_se of clock gates in rtl
  - fixed floating scan_shift[5:0] pins in rtl
  - increased scan in/out buffers to 1800 to better balance the number of FFs in internal scan chains.

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
defines.lst: macro defines that should be used during RTL reading and elaboration

SCAN_SCRIPTS

Script to be used for scan chain insertion. Modification of memory model paths will be required.

These still need an update that will follow in a later release.

SIM

adapt_sim_setup.sh is a script that should be sourced between the make presetup and the make compile_lp5 command of the snps subsys simulation flow in the sim dir.
It adapts hierarchical paths to intercept the additional levels of hierarchy created by the axelera wrappers.
It also adds a bunch of extra compile source to the compile.f file picked up by the compilation flow.

All this is experimental, and can be replaced by other means to reach the same goal of running the simulations. This approach works on axelera side, and has been included as an example.

CONSTRAINTS

Included constraints are a first draft to be tested by SNPS. They contain only the functional mode, scan_shift and scan_atspeed will follow in a later release.

Functional constraints
- Axelera top-level clock definitions have been added, and included in clock grouping statements. 
- Original snps clocks are defined as generated clocks with the same fan-out cone. As a result, any downstream constraints using these clocks, can be kept.
- io constraints have been adapted to target the axelera top-level interface
    - budgetting of synchronous interfaces (AXI/APB) is still to be discussed with axelera PD-team
- Scan clocks are no longer defined in functional mode, they have been commented in any constraints that used them.
