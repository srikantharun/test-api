  
# Script to modify the ss release sim setup to be able to handle the extra hierarchy and other changes caused by the axelera top-level wrappers.
# To be executed in the sim dir of the ss release.
axelera_hier=ddr_chip_inv_wrapper.axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst
# Adapt the dut to target our inv wrapper
sed -i "s/snps_ddr_subsystem ddr_chip (/lpddr_subsys_inv_wrapper ddr_chip_inv_wrapper (/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
# Adapt the hierachy used in some force and bind statements from snps
sed -i "s/ddr_chip.i_DWC_lpddr5x_phy/$axelera_hier.i_DWC_lpddr5x_phy/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
sed -i "s/ddr_chip.i_uddrctl/$axelera_hier.i_uddrctl/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
# sed -i "s/U_ddr_chip_wrapper.ddr_chip.i_DWC_lpddr5x_phy/U_ddr_chip_wrapper.$axelera_hier.i_DWC_lpddr5x_phy/g" ./testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
# Update all hierarchical paths containing "U_ddr_chip_wrapper.ddr_chip" to $axelera_hier as to intercept axelera's wrapper changes
grep -rl --include \*.sv --include \*.svh --include \*.el "\.ddr_chip" ./testbench | xargs sed -i "s/\.ddr_chip/.$axelera_hier/g"

# Add the required extra sim sources to the compile.f
cat ./testbench/modules/compile.f $DDR_AX_RTL_PATH/sim/extra_compile.f > ./testbench/modules/compile.f
# Add delay_mode_path as a vcs compile option to avoid timing issues cause by focring clocks over the pctl clock gates.
sed -i '/$main::common_compile_options.= " +vcs+loopdetect ";/a $main::common_compile_options.= " +delay_mode_path ";' runtest.pm
