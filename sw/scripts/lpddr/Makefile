PYTHON = python3.10

LPDDR_PHYINIT_PATH	:= $(REPO_ROOT)/sw/scripts/lpddr/synopsys/dwc_ap_lpddr5x_phy_sssf5a/Latest/phyinit/Latest/software/lpddr5
# LPDDR_SOFTWARE_PATH	:= $(REPO_ROOT)/sw/scripts/lpddr/synopsys/dwc_ap_lpddr5x_phy_sssf5a/phy/Latest/
LPDDR_FIRMWARE_PATH	:= $(REPO_ROOT)/sw/scripts/lpddr/synopsys/dwc_ap_lpddr5x_phy_sssf5a/Latest/firmware/Latest/training

gen_lpddr:
	$(MAKE) -C $(LPDDR_PHYINIT_PATH) run FIRMWARE_PATH=$(LPDDR_FIRMWARE_PATH)

clean:
	$(MAKE) -C $(LPDDR_PHYINIT_PATH) clean
