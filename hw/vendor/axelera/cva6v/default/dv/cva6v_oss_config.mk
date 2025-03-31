OSS_SRC_DIR   = $(MAKEFILE_DIR)/../deps/tests
OSS_BUILD_DIR = $(OSS_SRC_DIR)/build

OSS_ARCH_TEST_LABELS = CVA6V_DV_MR_TESTS CVA6V_DV_TESTS CVA6V_DV_OSS_TESTS CVA6V_DV_OSS_ARCH_TESTS
OSS_COMPLIANCE_TEST_LABELS = CVA6V_DV_MR_TESTS CVA6V_DV_TESTS CVA6V_DV_OSS_TESTS CVA6V_DV_OSS_COMPLIANCE_TESTS
OSS_P_TEST_LABELS = CVA6V_DV_MR_TESTS CVA6V_DV_TESTS CVA6V_DV_OSS_TESTS CVA6V_DV_OSS_P_TESTS
OSS_V_TEST_LABELS = CVA6V_DV_MR_TESTS CVA6V_DV_TESTS CVA6V_DV_OSS_TESTS CVA6V_DV_OSS_V_TESTS
OSS_VECTOR_TEST_LABELS = CVA6V_DV_MR_TESTS  CVA6V_DV_TESTS CVA6V_DV_OSS_TESTS CVA6V_DV_OSS_VECTOR_TESTS
IMPERAS_VB_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VB_TESTS
IMPERAS_VF_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VF_TESTS
IMPERAS_VI_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VI_TESTS
IMPERAS_VM_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VM_TESTS
IMPERAS_VP_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VP_TESTS
IMPERAS_VR_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VR_TESTS
IMPERAS_VX_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_V_TESTS CVA6V_DV_IMPERAS_VX_TESTS
IMPERAS_F_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_F_TESTS
IMPERAS_I_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_I_TESTS
IMPERAS_M_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_M_TESTS
IMPERAS_ZICSR_TEST_LABELS = CVA6V_DV_TESTS CVA6V_DV_IMPERAS_TESTS CVA6V_DV_IMPERAS_ZICSR_TESTS

OSS_TESTSUITES =

# Append based on REGRESS_VERIFSDK_LABEL
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(OSS_ARCH_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_riscv-arch-test-cv64a6_imafdc_sv39.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(OSS_COMPLIANCE_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_riscv-compliance-cv64a6_imafdc_sv39.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(OSS_P_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_riscv-tests-cv64a6_imafdc_sv39-p.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(OSS_V_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(OSS_VECTOR_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_riscv-tests-cv64a6_vector.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VB_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vb.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VF_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vf.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VI_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vi.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VM_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vm.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VP_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vp.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VR_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vr.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_VX_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_vector_rv64i_Vx.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_F_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_floatingpoint_rv64i_F.yaml
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_floatingpoint_rv32i_Zfh.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_F_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_floatingpoint_rv64i_F.yaml
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_floatingpoint_rv32i_Zfh.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_I_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_rv64i_I.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_M_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_rv64i_M.yaml
endif
ifneq ($(filter $(REGRESS_VERIFSDK_LABEL),$(IMPERAS_ZICSR_TEST_LABELS)),)
  OSS_TESTSUITES += testlist_imperas_riscv-tests-cv64a6_rv64i_Zicsr.yaml
endif

OSS_TESTSUITES_COMPILE_TARGETS = $(addprefix $(OSS_BUILD_DIR)/, $(OSS_TESTSUITES))

.PHONY: $(OSS_BUILD_DIR)
$(OSS_BUILD_DIR):
	@# Create the build directory
	mkdir -p $@

$(OSS_BUILD_DIR)/%.yaml: $(OSS_SRC_DIR)/%.yaml | $(OSS_BUILD_DIR)
	@# Open Source Testsuite
	# Likely the first time the virtual env is made
	# clear makeflags incase we are running in parallel
	unset MAKEFLAGS
	$(GRID_CMD) cva6v_yml_to_elf --testlist $< --linker_file /${REPO_ROOT}/sw/src/lib/cva6v/link.ld |& tee $@

FLOW_PREREQUISITES += compile_oss_testsuites
.PHONY: compile_oss_testsuites
compile_oss_testsuites: $(OSS_TESTSUITES_COMPILE_TARGETS)

CLEAN_PREREQUISITES += clean_oss_testsuites
.PHONY: clean_oss_testsuites
clean_oss_testsuites:
	rm -rf $(OSS_BUILD_DIR)




