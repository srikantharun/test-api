#!/usr/bin/env bash

set -e
set -o pipefail

if [ "$#" -ne 3 ]; then
    echo "Usage: <source_tsdb> <release_dir> <Bender.yml>"
    exit 1
fi

if [ ! -d $1 ]; then
    echo "Directory not found: $1"
    exit 2
fi

# If DFT_HOME is not populated, create it and give write permissions
parent_dir=$(dirname $2)
if [ ! -d $parent_dir ]; then
    mkdir -p $parent_dir
    chmod -R 775 $parent_dir
fi

# If there is no directory for the current block, create it and give write permissions
if [ ! -d $2 ]; then
    mkdir -p $2
    chmod -R 775 $2
fi

echo "$0 $1 $2 $3"

timestamp=$(date +%Y%m%d%H%M)

srcdir=$1
outdir=$2
rtldir=$2/${timestamp}/rtl
tsdbdir=$2/${timestamp}/tsdb

mkdir -p $rtldir
mkdir -p $tsdbdir

blockname=$(basename $2)

modified_files_lst=$1/modified_files.lst
added_files_lst=$1/added_files.lst
library_files_lst=$1/library_files.lst

instruments_folders=$(find $srcdir/../../ -type d -name instruments)
for instruments in $instruments_folders
do
  find $instruments -type f -name "*.v" >> $added_files_lst
done

cat "$added_files_lst" "$modified_files_lst" | while IFS= read -r line
do
  cp -v $line $rtldir
done

mkdir -p ${rtldir}/include
# Find all INCLUDE folders from oldest to most recent
include_folders=$(find $srcdir/../../ -type d -name "INCLUDE" -exec ls -tdr {} +)
for include_folder in $include_folders
do
  # Copy includes, overwrite any older includes of the same name
  # If INCLUDE not empty, copy contents
  [ $(ls -1A $include_folder | wc -l) -ne 0 ] && cp -rvf $include_folder/* ${rtldir}/include
done
  
# Copy tessent tsdb directory
tsdbs=$(find $srcdir/../../ -maxdepth 3 -type d -name "tsdb_outdir")
for tsdb in $tsdbs
do
  bname=$(basename $(dirname $tsdb))
  mkdir -p $tsdbdir/$bname
  cp -rv $tsdb $tsdbdir/$bname
done


# Create Bender.yml
cat <<EOT > ${outdir}/${timestamp}/Bender.yml
package:
  name: dft_${blockname}
  description: "DFT RTL release for ${blockname}"
  authors:
    - "Tiago Campos <tiago.campos@axelera.ai>"

EOT

# Check if any package dependencies were found
#results=$(egrep ".*(_pkg|_subsys).*:.*" "$3")
#if [ ! -z "$results" ]; then
 #   echo "dependencies:" >> ${outdir}/${timestamp}/Bender.yml
  #  echo "$results"      >> ${outdir}/${timestamp}/Bender.yml
#fi

# Create Bender.yml
cat <<EOT >> ${outdir}/${timestamp}/Bender.yml

sources:
  - target: rtl
    defines:
      GLOBAL_MIN_HOLD_NS=0:
    include_dirs:
EOT

## Include the dirs from build_dependencies/incdirs.do
sed 's|    \(.*\) \\|      - \1|' $srcdir/../build_dependencies/incdirs.do >> ${outdir}/${timestamp}/Bender.yml
sed -i '/.*set_design_include_directories.*/d' ${outdir}/${timestamp}/Bender.yml
sed -i '$ d' ${outdir}/${timestamp}/Bender.yml
sed -i "s@${REPO_ROOT}@\$REPO_ROOT@g" ${outdir}/${timestamp}/Bender.yml

cat <<EOT >> ${outdir}/${timestamp}/Bender.yml
      - rtl/include
    files:
EOT

if [[ -f $library_files_lst ]]; then
    while IFS= read -r line; do
        if [ -n "$line" ]; then
            echo "      - ${line}" >> ${outdir}/${timestamp}/Bender.yml
        fi
    done < $library_files_lst
fi

for file in $(find $rtldir -type f)
do
    bname=$(basename "$file")
    echo "      - rtl/${bname}" >> ${outdir}/${timestamp}/Bender.yml
done

# Find most recent patterns directory
patterns_folders=$(find $srcdir/../../ -type d -name "*.patterns_signoff" -exec ls -td {} + | head -1)
cp -r ${patterns_folders} ${outdir}/${timestamp}/patterns

#I will move the subsystem insertion out of lpddr/pcie and this won't be required
if [[ "$blockname" == "lpddr" || "$blockname" == "pcie" ]] ; then
    echo "$blockname also taking memory_test/patterns"
    #also for this block get the memory_test patterns also.
    patterns_folders=$(find $srcdir/../../ -type d -name "*.patterns_signoff" -exec ls -td {} + | head -2 | tail -1 )
    cp  --verbose -r ${patterns_folders}/* ${outdir}/${timestamp}/patterns
    echo "cp  --verbose -r ${patterns_folders} ${outdir}/${timestamp}/patterns"
fi 

# Refresh Latest symbolic link
rm -rf ${outdir}/Latest
ln -s ${outdir}/${timestamp} ${outdir}/Latest
chmod 775 ${outdir}/Latest

# Remove write permissions from timestamped folder
chmod -R 755 ${outdir}/${timestamp}
