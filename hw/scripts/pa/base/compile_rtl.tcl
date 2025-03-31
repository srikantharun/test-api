# RTL compile file.

# Define the logical and related physical libraries.
AddLibrary work WORK

if {$env(DFT) == 1} {
  set BENDER_MANI_LOC [list -d ${make_dir}/../rtl/dft]
} else {
  set BENDER_MANI_LOC [list -d ${make_dir}/../rtl]
}
set BENDER_ARGS [list -t asic -t sf5a -t rtl -t synthesis -t power_artist]

if {$env(DFT) == 1} {
  lappend BENDER_ARGS -t dft
}
lappend BENDER_ARGS -D SYNTHESIS

exec bender update {*}$BENDER_MANI_LOC
# set file_list [exec bender script flist-plus {*}$BENDER_MANI_LOC {*}$BENDER_ARGS]
set template hw/scripts/bender_templates/powerartist.tera
set file_list [exec bender script template --template $env(REPO_ROOT)/${template} {*}$BENDER_MANI_LOC {*}$BENDER_ARGS]
# Open the file for writing
set fh [open $WORK_DIR/rtl.tcl "w"]
# Write the content to the file and to stdout
puts $fh $file_list
close $fh

pa_set system_verilog true

source $WORK_DIR/rtl.tcl
