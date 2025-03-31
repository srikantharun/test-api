#!/bin/bash 

bender_dir=$1
shift 1

next=TITANIA

# Run bender to get all files
# for incdir remove, just put the directory in place
# And grep for TODO / FIXME recursively (so gets all incdir files)
# Remove EUROPA or whatever next chip is - this indicates that the TODO has been looked at and decided not to fix in current chip
# Remove anything in .c .h .py files - as SW and not in the chip DB
# Remove 3rd Party IP : _dw_ designware
bender -d $bender_dir script flist -t rtl -t dft $@  | sed -E 's~\+incdir\+~~'  | xargs grep -r  "waive" 


