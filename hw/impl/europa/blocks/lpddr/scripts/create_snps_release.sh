#!/usr/bin/env bash

version=DFT3_v3

# Make the release
# uncomment for local testing release_dir=${REPO_ROOT}/test_lpddr_release
make -C ${REPO_ROOT} pd_release_flat REL_TYPE=block REL_BLOCK=lpddr REL_DFT_ENABLE=true
#REL_DIR_FLAT=$release_dir

# Look up the actual release dir
# uncomment for local testing release_dir=$(ls -d $release_dir/lpddr/* | sort | tail -n 1  | awk '{print $NF}')
release_dir=$(ls -d /data/releases/europa/lpddr/* | sort | tail -n 1  | awk '{print $NF}')
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
rm $release_dir/lpddr_p.read_rtl.tcl

# Add the DFT release to the release dir
cp -r ${DFT_HOME}/lpddr/Latest/rtl/* $release_dir/src
mkdir $release_dir/scan_scripts
cp /data/europa/pd/lpddr_p/block_build/dev_dft/build/fc/compile/scripts/lpddr_p.preserveDFT.tcl $release_dir/scan_scripts
cp /data/europa/pd/lpddr_p/block_build/dev_dft/build/fc/compile/scripts/lpddr_p.insertDFT.tcl $release_dir/scan_scripts

# Release info
# Manual modified and added lists from now, copied and adapted from DFT release
mkdir $release_dir/config
# Copy the manually maintained modified file list to the release location
cp ${REPO_ROOT}/hw/impl/europa/blocks/lpddr/docs/release_info/$version/modified_files.lst $release_dir/config
# Use bender to make a list of all axelera files, including the modified ones
bender script flist-plus -d $REPO_ROOT/hw/impl/europa/blocks/lpddr/rtl/dft -t asic -t rtl -t sf5a -t dft | grep -v /data/foundry | awk 'NF { if (system("[ -f " $0 " ]") == 0) { system("echo \\$DDR_AXE_RTL_PATH/scr/$(basename " $0 ")") } else { print $0 } }' > $release_dir/config/all_axe_files.lst
# We also need to list files in include directories, so go look for them and add them to the list
grep '^+incdir+' "$release_dir/config/all_axe_files.lst" | while read -r line; do
    dir=$(echo "$line" | cut -d'+' -f3)
    if [ -n "$(ls -A "$dir")" ]; then
        echo "Listing files in directory: $dir"
        for f in "$dir"/*; do
            echo "\$DDR_AXE_RTL_PATH/src/$(basename "$f")"
        done > include_files.tmp
    fi
done
# Make a list of all the defines that should be used by snps
grep '^+define+' $release_dir/config/all_axe_files.lst > $release_dir/config/defines.lst
# Remove the incdirs and defines from the bender output
grep -vE '^\+incdir\+|^\+define\+' $release_dir/config/all_axe_files.lst > all_axe_files.tmp
mv all_axe_files.tmp $release_dir/config/all_axe_files.lst
# Add the found include files to the top of the list
cat include_files.tmp $release_dir/config/all_axe_files.lst > all_axe_files.tmp
mv all_axe_files.tmp $release_dir/config/all_axe_files.lst
rm include_files.tmp

# Extend the snps rtl sim list (but cut off their subsys reference) with the axe list to make a new complete sim list.
cat <(head -n -2 $DDR_SUBSYSTEM_RTL_PATH/customer_config/lpddr_ss_rtl_sim.lst) $release_dir/config/all_axe_files.lst > $release_dir/config/lpddr_axe_rtl_sim.lst

# Copy the readme
cp ${REPO_ROOT}/hw/impl/europa/blocks/lpddr/docs/release_info/$version/release_readme.txt $release_dir/config


# Simulation setup (experimental at this point)
mkdir $release_dir/sim
cp ${REPO_ROOT}/hw/impl/europa/blocks/lpddr/rtl/generated/lpddr_subsys_inv_wrapper.sv $release_dir/sim
cp ${REPO_ROOT}/hw/ip/tech_cell_library/default/rtl/simulation/axe_tcl_seq_metastability_model.sv $release_dir/sim
cp ${REPO_ROOT}/hw/impl/europa/blocks/lpddr/scripts/adapt_sim_setup.sh $release_dir/sim

# Make a .f file of extra compile sources. This is similar to the file list in the config, except for the include dirs, which are now modified to point to the axelera include sources instead of replaced by the verilog files in them.
bender script flist-plus -d $REPO_ROOT/hw/impl/europa/blocks/lpddr/rtl/dft -t asic -t rtl -t sf5a -t dft | grep -v /data/foundry | awk 'NF { if (system("[ -f " $0 " ]") == 0) { system("echo \\$DDR_AXE_RTL_PATH/scr/$(basename " $0 ")") } else { print $0 } }' > $release_dir/sim/extra_compile.f
echo "\$DDR_AXE_RTL_PATH/sim/axe_tcl_seq_metastability_model.sv" >> $release_dir/sim/extra_compile.f
echo "\$DDR_AXE_RTL_PATH/sim/lpddr_subsys_inv_wrapper.sv" >> $release_dir/sim/extra_compile.f
# Remove the bender indirs and replace by a fixed incdir for the release.
sed -i '/+incdir+/d' $release_dir/sim/extra_compile.f
sed -i '1i\
+incdir+$DDR_AXE_RTL_PATH/src/include\
+incdir+$DDR_AXE_RTL_PATH/src' $release_dir/sim/extra_compile.f

# Make it a tar file.
tar -czvf $release_dir/../$version.tar.gz $release_dir
# Move the tar inside the release dir.
mv $release_dir/../$version.tar.gz $release_dir

# Lock off the release dir

chmod -R 555 $release_dir




