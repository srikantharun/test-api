General notes on the Axelera release structure

RELEASE VERSION

DFT2 v0.4

DIRECTORY structure

- src: all added or modified source files
- constraints: constraint files to be used
- scan_scripts: contains scan related script to be executed on SNPS side
- dft logs: containts logs and reports from DFT insertion
- config: contains filelist to be used

CONFIG

all_axe_files.lst: all files in the Axelera release
modified_files.lst: all files that existed in the SS2 release that have been modified by Axelera
defines_sim.lst: defines to be used for simulation
defines_synt.lst: defines to be used for synthesis

SCAN_SCRIPTS

Script to be used for scan chain insertion. Modification of memory model paths will be required.

CONSTRAINTS

Included constraints the full functional constraints matching the newest RTL changes in the pcie_p wrapper
as well as full set of DFT constraints (atspeed, shift and mbist). mbist constraints are merged with functional
constraints, while atspeed and shift should be executed standalone.
mbist constraints contain $post_synth switch set to 0 that excludes mbist_exception. This should be set to 1 after synthesis.
