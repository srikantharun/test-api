AX_ASM_SRC_DIR = $(MAKEFILE_DIR)/../asm/tests
AX_ASM_BUILD_DIR = $(MAKEFILE_DIR)/../asm/tests/build
AX_ASM_SUBDIRS = \
directed \
vector

# Collect all .S files in the subdirectories
S_FILES := $(wildcard $(foreach dir,$(AX_ASM_SUBDIRS),$(AX_ASM_SRC_DIR)/$(dir)/*.S))

AX_ASM_ARCH ?= rv64imafc_zicsr_zifencei_zve32f_zfh_zfhmin

CMD := cva6v_asmdir_to_elf

# Rule to create build directories
.PHONY: $(AX_ASM_BUILD_DIR)
$(AX_ASM_BUILD_DIR):
	@# Create the build directory
	mkdir -p $@

# Rule to execute the command for each subfolder
.PHONY: build_ax_asm
build_ax_asm: $(AX_ASM_BUILD_DIR)
	@echo "Executing command $(CMD) for each subdirectory containing .S files..."
	@$(foreach dir,$(AX_ASM_SUBDIRS), \
		if ls $(AX_ASM_SRC_DIR)/$(dir)/*.S > /dev/null 2>&1; then \
			$(CMD) --input_dir $(AX_ASM_SRC_DIR)/$(dir) --output_dir $(AX_ASM_BUILD_DIR)/$(dir) --arch $(AX_ASM_ARCH); \
		fi;)

FLOW_PREREQUISITES += build_ax_asm

CLEAN_PREREQUISITES += clean_ax_asm_testsuites
.PHONY: clean_ax_asm_testsuites
clean_ax_asm_testsuites:
	rm -rf $(AX_ASM_BUILD_DIR)

# Automatically detect ELF names based on testname
# CVA6V_DV_RAG - example testname cva6v_rag_random-base_loop_0
ifneq ($(strip $(findstring cva6v_rag_,$(TESTNAME))),)
  SUFFIX = $(subst cva6v_rag_,,$(TESTNAME))
  DELIMITER_POS = $(findstring -,$(SUFFIX))
  DELIMITER = $(word 1,$(subst $(DELIMITER_POS), ,$(SUFFIX)))
  TEST_SRC = $(subst $(DELIMITER)-,,$(SUFFIX))
  ELF = $(REPO_ROOT)/hw/vendor/axelera/cva6v/default/dv/asm/tests/build/$(DELIMITER)/$(TEST_SRC)
endif
