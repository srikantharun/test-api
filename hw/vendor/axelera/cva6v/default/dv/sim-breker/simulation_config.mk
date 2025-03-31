BREKER_V2 := 1

# Configuration for the IP
IP_NAME            = ai_core_cva6v
TOP_LEVEL_MODULES  = hdl_top

BENDER_MANI_LOC := .
UVM       = 1
TESTNAME ?= cva6v_dv_breker_hello
ELF      ?= 
SEED     ?= 1

# Regression configuration
REGRESS_VERIFSDK_PLATFORM ?= cva6v.BREKER
REGRESS_VERIFSDK_LABEL    ?= CVA6V_DV_BREKER_TESTS

# SIM COMPILE
DPI_C_SRC    += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c/dpi_memory.cc
DPI_C_SRC    += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c/dummy.cc
DPI_C_INCDIR += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c
SV_LIBS      += -sv_lib /apps/eda/breker/trek5-2.1.3-GCC6_el7/linux64/lib/libtrek

GLOBAL_DEFINES += +define+TARGET_VERIF

# SIM RUN
PLUSARGS_COMMON  += +elf_file=$(ELF)
PLUSARGS_COMMON  += +tohost_addr=2000001000

ifndef BREKER_V2
	TOP_LEVEL_MODULES += trek_uvm
else
	GLOBAL_DEFINES += +define+BREKER
endif
