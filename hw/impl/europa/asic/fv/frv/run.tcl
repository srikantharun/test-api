
proc proc_formal_core {} {
  # Formal Core
  compute_formal_core -block
  report_formal_core -verbose
  compute_formal_core_coverage -par_task FRV -block
  save_formal_core_results -db_name FC.vdb
  #view_coverage -cov_input FC -mode FC -reload -elfiles { FPV_COV_FCORE_w_fcore.el }
}

#Configure host file
set_grid_usage -file $::env(REPO_ROOT)/hw/scripts/fv/fpv/host.qsub -global

#-------------------------------------------------------
# Read configuraton file
#-------------------------------------------------------
source ../settings.tcl

# Enable FRV appmode
set_fml_appmode FRV

# Define max mem and timeout
proc_set_mem_timeout

# Including AIP
proc_enable_AIP

# Define Blackboxes
proc_set_design_blackboxes

# read IP-XACT XML file and generate FRV checker file
frv_load -ipxact $ipxact -auto_load

# read design and testbench files
source rtl.analyze.tcl
#elaborate $design -cov line+cond+tgl -sva -vcs "-cm_tgl mda"
elaborate $design -cov line+cond+tgl -sva -vcs "-cm_tgl mda"

# Defining clocks
proc_set_clks

# Defining resets
proc_set_rsts

# Disabing assertions and assumes in the rtl_file
fvdisable -usage {assert assume} { * }
fvenable -usage {assert assume} { *.*sva*.* *snps*}

sim_run -stable
sim_save_reset

# snip driver
proc_set_snip_drivers

check_fv -block

report_fv -verbose
report_fv -verbose > report_fv.log

save_session
