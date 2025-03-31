#!/usr/bin/env bash


current_dir=$(pwd)

# Pick the customer_config stuff from SNPS and copy it to your local repo (otherwise you will get permission issues)
cp -r $PCIE_WORKSPACE/db/checksum_ss $REPO_ROOT/hw/vendor/synopsys/pcie_subsys/default

cd $REPO_ROOT/hw/vendor/synopsys/pcie_subsys/default/checksum_ss

./check_md5sum.pl | grep "ERROR\!"
grep_value=$?

cd $current_dir
rm -rf $REPO_ROOT/hw/vendor/synopsys/pcie_subsys/default/checksum_ss

if [ $grep_value -eq 0 ]; then
    echo "ERROR: CHECKSUM DID NOT MATCH!!!"
    exit 1
else
    echo "INFO: CHECKSUM PASSED"
    exit 0
fi
