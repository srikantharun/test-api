# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
# Domenic & Pawel

## RISCV-DV revision
DV_REV :=  14c9cb2

## Generator simulation tool
DV_SIM_TOOL ?= questa

## Target to build for
TARGET ?= base

## Max parallel jobs for test generation
GRID_NUM_CPUS ?= 2

ifndef RANDOM_SEED
	SEED := $(strip $(shell od -vAn -N4 -tu4 < /dev/urandom))
else
	SEED := $(RANDOM_SEED)
endif

RAG_DIR ?= $(shell pwd)
SETTINGS_DIR := $(RAG_DIR)/target/$(TARGET)
SOURCE_CODE_DIR := $(RAG_DIR)/dv_$(DV_REV)
RAG_TEMP_OUT_DIR := generation_out
RAG_OUT_DIR ?= ../asm/tests/random
RAG_VENV ?= .venvrag

## Fixed settings for CVA6V. Zurich passes this dynamically to avoid having diffetent core settings (no recompile)
GEN_SIM_ARGS := +zve_extension=zve32f +vector_memport_width=128
GEN_SIM_ARGS += +enable_zvfh_extension=1 +enable_zvfhmin_extension=1

## Generator Timeout in seconds
GEN_TIMEOUT ?= 1800

.PHONY: create_rag_venv rag_build split_yaml rag_gen rag_clean rag_clean_outdir

create_rag_venv:
	@if [ ! -d $(RAG_VENV) ]; then\
	  echo "[RAG] Creating RAG venv";\
	  python3 -m venv "$(RAG_VENV)";\
	  echo "[RAG] Activating created RAG venv";\
	  source "$(RAG_VENV)/bin/activate";\
	  pip install pyyaml;\
	else\
	  echo "[RAG] Activating existing RAG venv";\
	  source "$(RAG_VENV)/bin/activate";\
	fi

## Build generator
rag_build: create_rag_venv
	python3 $(SOURCE_CODE_DIR)/run.py -ct $(SETTINGS_DIR) -si $(DV_SIM_TOOL) --co -s gen -o $(RAG_TEMP_OUT_DIR)

## Yq will split the yaml to 1-scenario/test per yaml in split folder
## Sed will restore/indent them back to the original form (array)
split_yaml:
ifeq ($(GRID_NUM_CPUS),1)
	@echo "[RAG] Skipping yaml splitting for serial job"
else
	@echo "[RAG] Splitting yaml for parallel job"
	mkdir -p $(SETTINGS_DIR)/split
	yq '.[]' $(SETTINGS_DIR)/testlist.yaml -s '"$(SETTINGS_DIR)/split/"+ .test + ".yaml"'
	for f in $(SETTINGS_DIR)/split/*.yaml; do \
		sed -i '1s/^/- /' "$$f"; \
		sed -i '2,$$s/^/  /' "$$f"; \
	done
endif

rag_gen: create_rag_venv split_yaml rag_clean_outdir
	mkdir -p $(RAG_OUT_DIR)
	mkdir -p $(RAG_OUT_DIR)/../build/random
ifeq ($(GRID_NUM_CPUS),1)
	@echo "[RAG] Generating tests serially"
	srun python3 $(SOURCE_CODE_DIR)/run.py -ct $(SETTINGS_DIR) -si $(DV_SIM_TOOL) --so -s gen  \
		-o $(RAG_TEMP_OUT_DIR) --start_seed $(SEED) --sim_opts "$(GEN_SIM_ARGS)" --gen_timeout $(GEN_TIMEOUT)
else
	@echo "[RAG] Generating tests in parallel"
	find $(SETTINGS_DIR)/split -name "*.yaml" | xargs -n 1 -P $(GRID_NUM_CPUS) -I {} \
		srun python3 $(SOURCE_CODE_DIR)/run.py -tl {} -ct $(SETTINGS_DIR) -si $(DV_SIM_TOOL) --so -s gen  \
		-o $(RAG_TEMP_OUT_DIR) --start_seed $(SEED) --sim_opts "$(GEN_SIM_ARGS)" --gen_timeout $(GEN_TIMEOUT)
	rm -rf $(SETTINGS_DIR)/split
endif
	$(GRID_CMD)	bash -c "(
	cp -a $(RAG_TEMP_OUT_DIR)/asm_test/. $(RAG_OUT_DIR)
	cva6v_asmdir_to_elf --input_dir $(RAG_OUT_DIR) --output_dir $(RAG_OUT_DIR)/../build/random
	cva6v_asmdir_to_verifsdk --input_dir $(RAG_OUT_DIR) --label CVA6V_DV_RAG_LOCAL_TESTS --output_file ${REPO_ROOT}/verifsdk/tests_fw_cva6v_autogenerated.yaml)"

rag_clean:
	rm -rf ./work
	rm -rf ./$(RAG_VENV)
	rm -rf $(RAG_TEMP_OUT_DIR)
	rm -rf $(RAG_OUT_DIR)/../build/random
	rm -rf $(RAG_OUT_DIR)
	rm -rf $(REPO_ROOT)/verifsdk/tests_fw_cva6v_autogenerated.yaml

rag_clean_outdir:
	rm -rf $(RAG_TEMP_OUT_DIR)
	rm -rf $(RAG_OUT_DIR)/../build/random
	rm -rf $(RAG_OUT_DIR)
