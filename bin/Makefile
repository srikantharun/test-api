SHELL := /usr/bin/bash
.SHELLFLAGS := -eu -o pipefail -c
.ONESHELL:

# Read VENV and requirements file
FILE ?= /path/to/file
VENV ?= VENV

# Create virtual env
$(VENV).installed: $(FILE)
	bash $(REPO_ROOT)/bin/install_venv.sh $(VENV) $(FILE)
	touch $(VENV).installed

venv: $(VENV).installed

clean:
	@echo "Cleaning up..."
	find $(REPO_ROOT) -regex '^.*\(__pycache__\|\.py[co]\)$\' -delete
	rm -rf .venv
