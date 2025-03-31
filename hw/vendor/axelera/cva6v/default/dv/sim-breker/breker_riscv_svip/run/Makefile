ifndef BREKER_HOME
$(error Please set up $$BREKER_HOME before running this Makefile)
endif

TREKSVIP = treksvip
PLATFORM_YAML = ../yaml/platform.yaml
TREKSVIP_YAML = $(BREKER_HOME)/examples/tutorials/svip/treksvip/yaml/treksvip.yaml
HELLO_YAML    = $(BREKER_HOME)/examples/tutorials/svip/treksvip/tests/test_hello.yaml
CONSTRAINTS_YAML = ../yaml/test_constraints.yaml
COH_CONSTRAINTS_YAML = ../yaml/test_constraints_coherency.yaml
SOC_CONSTRAINTS_YAML = ../yaml/test_constraints_soc.yaml
MMU_CONSTRAINTS_YAML = ../yaml/test_constraints_mmu.yaml
RVOPS_CONSTRAINTS_YAML = ../yaml/test_constraints_rvops.yaml
OUTPUTDIR = ../../../tests/breker/cva6v_dv_breker_$@

trek_test:
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) -p $(CONSTRAINTS_YAML)       -o $(OUTPUTDIR)/trek_test -e pss_top.entry 

hello:
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) -p $(HELLO_YAML)             -o $(OUTPUTDIR)/trek_hello -e pss_top.entry 

coherency:
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) -p $(COH_CONSTRAINTS_YAML)   -o $(OUTPUTDIR)/trek_coherency -e pss_top.entry 

soc:
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) -p $(SOC_CONSTRAINTS_YAML)   -o $(OUTPUTDIR)/trek_soc -e pss_top.entry 

mmu:
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) -p $(MMU_CONSTRAINTS_YAML)   -o $(OUTPUTDIR)/trek_mmu -e pss_top.entry 

rvops:
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) -p $(RVOPS_CONSTRAINTS_YAML) -o $(OUTPUTDIR)/trek_rvops -e pss_top.entry 

uvm_output:
	rm -rf uvm_output
	$(TREKSVIP) -p $(PLATFORM_YAML) -p $(TREKSVIP_YAML) --uvm_output=uvm_output
	sed -i '/export "DPI-C" function trek/ s/^/ \/\//' uvm_output/trek_uvm.sv 

clean:
	@/bin/ls --hide="Makefile" | /usr/bin/xargs rm -rf;

