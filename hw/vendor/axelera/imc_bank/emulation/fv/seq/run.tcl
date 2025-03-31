
#Configure host file
set_grid_usage -file $::env(REPO_ROOT)/hw/scripts/fv/fpv/host.qsub -global

#-------------------------------------------------------
# Read configuraton file
#-------------------------------------------------------
source ../settings.tcl

# Enable FRV appmode
set_fml_appmode SEQ

# Set variables
set_fml_var fml_enable_prop_density_cov_map true
set_fml_var fml_reset_property_check true

# Define max mem and timeout
proc_set_mem_timeout

proc_set_abstraction

seq_config -map_uninit -map_x zero

# Including AIP
proc_enable_AIP

# Define Blackboxes
proc_set_design_blackboxes

# read design and testbench files
source rtl.analyze.tcl
source spec.analyze.tcl
#elaborate $design -cov line+cond+tgl -sva -vcs "-cm_tgl mda"
elaborate_seq -j 16 -spectop $design_spec -impltop $design_impl -cov line+cond+tgl

proc_mapping

# Defining clocks
proc_set_clks

# Defining resets
proc_set_rsts

# Disabing assertions and assumes in the rtl_file
fvdisable -usage {assert assume} { * }
fvenable -usage {assert assume} { *.*sva*.* *snps* _* }

sim_run -stable
sim_save_reset

# snip driver
proc_set_snip_drivers

check_fv -block

report_fv -verbose
report_fv -verbose > report_fv.log

save_session
