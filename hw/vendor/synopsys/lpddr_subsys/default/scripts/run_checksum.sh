#!/usr/bin/env bash


current_dir=$(pwd)

# Pick the customer_config stuff from SNPS and copy it to your local repo (otherwise you will get permission issues)
cp -r $DDR_SUBSYSTEM_RTL_PATH/customer_config $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default

cd $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default/customer_config

./check_md5sum.pl | grep "ERROR\!"
grep_value=$?

cd $current_dir
rm -rf $REPO_ROOT/hw/vendor/synopsys/lpddr_subsys/default/customer_config

if [ $grep_value -eq 0 ]; then
    echo "ERROR: CHECKSUM DID NOT MATCH!!!"
    exit 1
else
    echo "INFO: CHECKSUM PASSED"
    exit 0
fi
