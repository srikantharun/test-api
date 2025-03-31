# Configuration for the IP
IP_NAME            = pcie
TOP_LEVEL_MODULES  = TB

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

# Enable DFT testbench mode
DFT         = 1
DFT_TB_ROOT = $(MAKEFILE_DIR)/../dv/dft_tb

# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS += -access=rw+/.
VSIM_ELAB_OPTS += -suppress 8760

VCS_ELAB_OPTS_EXT   += -pvalue+TB.DUT_inst.u_pcie_subsys.u_pcie_phy_top.u_phy_memory_top.u_phy_rom_0.u_mem.PreloadFilename='\"$(MAKEFILE_DIR)/../rom/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.fastsim.bin\"'

