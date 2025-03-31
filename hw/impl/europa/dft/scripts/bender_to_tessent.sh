#!/usr/bin/env bash

# Quick and dirty convertion script: bender filelist -> tessent dofile
# TODO: Replace this script by bender template

set -e
set -o pipefail

if [ "$#" -ne 2 ]; then
    echo 'Usage: <bender_flist_file_input> <tessent_dofile_output>'
    exit 1
fi

if [ ! -f $1 ]; then
    echo "File not found: $1"
    exit 2
fi

echo "$0 $1 $2"

outdir=$(dirname $2)
incdirs=$outdir/incdirs.do
vlog=$outdir/vlog.f
vhdl=$outdir/vhdl.f


mkdir -p $outdir

# Create incidrs.do
echo 'set_design_include_directories "' > $incdirs
for line in $(grep -sE '^\+incdir\+' $1); do
  echo $line >> $incdirs
done
sed -i -re 's/\+incdir\+/    /g' -e 's/$/ \\/g' $incdirs
echo '"' >> $incdirs

# Create vlog.do
grep -E '\.s?v$' $1 > $vlog

# Create vhdl.do
grep -E '\.vhdl?$' $1 > $vhdl || test $? = 1

# Filter files in vlog.do
if [ -f "removed_files.lst" ]; then
  grep -v ^# removed_files.lst | while IFS= read -r line
  do
    echo "Removing files matching: $line"
    sed -i "/${line}/s/^/# /" $vlog
  done
fi

# Create read_rtl.do
echo "dofile $incdirs" > $2
echo "read_verilog -format sv2009 -f $vlog" >> $2
echo "read_vhdl -f $vhdl" >> $2

