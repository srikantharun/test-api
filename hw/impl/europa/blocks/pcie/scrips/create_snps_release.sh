#!/usr/bin/env bash

version=DFT2_v0_2

# Make the release
# uncomment for local testing release_dir=${REPO_ROOT}/test_pcie_release
make -C ${REPO_ROOT} pd_release_flat REL_TYPE=block REL_BLOCK=pcie REL_DFT_ENABLE=true

# Look up the actual release dir
# uncomment for local testing release_dir=$(ls -d $release_dir/pcie/* | sort | tail -n 1  | awk '{print $NF}')
release_dir=$(ls -d /data/releases/europa/pcie/* | sort | tail -n 1  | awk '{print $NF}')
# Copy it as we will change it.
cp -r $release_dir ${release_dir}_snps
release_dir=${release_dir}_snps

chmod -R 755 $release_dir

# Move the rtl files into a src dir
mkdir $release_dir/src
mv $release_dir/*.sv $release_dir/src
mv $release_dir/*.v $release_dir/src
mv $release_dir/*.svh $release_dir/src

# Remove the FC compile read script from our release flow, paths won't work for snps
rm $release_dir/pcie_p.read_rtl*
rm $release_dir/release_manifest.md

# Add the DFT release to the release dir
cp -r ${DFT_HOME}/pcie/Latest/rtl/* $release_dir/src
mkdir $release_dir/scan_scripts
cp ${REPO_ROOT}/hw/impl/europa/blocks/pcie/fc/scripts/pcie_p.preserveDFT.tcl $release_dir/scan_scripts
cp ${REPO_ROOT}/hw/impl/europa/blocks/pcie/fc/scripts/pcie_p.insertDFT.tcl $release_dir/scan_scripts

mkdir $release_dir/dft_logs
cp ${REPO_ROOT}/hw/impl/europa/blocks/pcie/fc/logs/pcie_p.dft_drc_pre.rpt $release_dir/dft_logs
cp ${REPO_ROOT}/hw/impl/europa/blocks/pcie/fc/logs/pcie_p.dft_drc_post.rpt $release_dir/dft_logs

# Release info
# Manual modified and added lists from now, copied and adapted from DFT release
mkdir $release_dir/config
# Copy the manually maintained modified file list to the release location
cp ${REPO_ROOT}/hw/impl/europa/blocks/pcie/docs/release_info/$version/modified_files.lst $release_dir/config
# Use bender to make a list of all axelera files, including the modified ones
bender script flist-plus -d $REPO_ROOT/hw/impl/europa/blocks/pcie/rtl/dft -t asic -t rtl -t sf5a -t synthesis -t dft | grep -v /data/foundry | awk 'NF { if (system("[ -f " $0 " ]") == 0) { system("echo \\$PCIE_AXE_RTL_PATH/src/$(basename " $0 ")") } else { print $0 } }' > $release_dir/config/all_axe_files.lst

# We also need to list files in include directories, so go look for them and add them to the list
grep '^+incdir+' "$release_dir/config/all_axe_files.lst" | while read -r line; do
    dir=$(echo "$line" | cut -d'+' -f3)
    if [ -n "$(ls -A "$dir")" ]; then
        echo "Listing files in directory: $dir"
        for f in "$dir"/*; do
            echo "\$PCIE_AXE_RTL_PATH/src/$(basename "$f")"
        done > include_files.tmp
    fi
done
# Make a list of all the synthesis defines that should be used by snps
grep '^+define+' $release_dir/config/all_axe_files.lst > $release_dir/config/defines_synt.lst
# Remove the incdirs and defines from the bender output
grep -vE '^\+incdir\+|^\+define\+' $release_dir/config/all_axe_files.lst > all_axe_files.tmp
mv all_axe_files.tmp $release_dir/config/all_axe_files.lst
# Add the found include files to the top of the list
cat include_files.tmp $release_dir/config/all_axe_files.lst > all_axe_files.tmp
mv all_axe_files.tmp $release_dir/config/all_axe_files.lst
rm include_files.tmp

# Copy the readme
cp ${REPO_ROOT}/hw/impl/europa/blocks/pcie/docs/release_info/$version/release_readme.txt $release_dir/config

# Make it a tar file.
tar -czvf $release_dir/../$version.tar.gz $release_dir
# Move the tar inside the release dir.
mv $release_dir/../$version.tar.gz $release_dir

# Lock off the release dir

chmod -R 555 $release_dir




