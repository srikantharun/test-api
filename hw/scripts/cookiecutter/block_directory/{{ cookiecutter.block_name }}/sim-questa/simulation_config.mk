# TODO: This was automatically generated, adaptions will need to be made
DFT = 0

# Configuration for the IP
IP_NAME            = {{ cookiecutter.block_name.lower() }}_p
TOP_LEVEL_MODULES  = {{ cookiecutter.block_name.lower() }}_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
