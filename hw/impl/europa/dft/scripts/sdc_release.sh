#!/usr/bin/env bash

set -e
set -o pipefail

if [ "$#" -ne 2 ]; then
    echo "Usage: <source_cns_dir> <release_cns_dir>"
    exit 1
fi

if [ ! -d $1 ]; then
    echo "Directory not found: $1"
    exit 2
fi

if [ ! -d $2 ]; then
    echo "Directory not found: $2"
    exit 3
fi

echo "$0 $1 $2"

sdcs=$(find $1 -type f -name *.sdc)
for sdc in $sdcs
do
    src_dname=$(dirname $sdc)
    src_bname=$(basename $sdc)

    dst_dname=$2
    dst_bname=$src_bname

    echo "$src_bname -> $dst_bname"

    if [ -f ${dst_dname}/${dst_bname} ]; then
        if [ -f ${dst_bname}/${dst_bname}.old ]; then
            echo "ERROR: Already exists and cannot append .old: ${dst_dname}/${dst_bname}"
            echo "To continue, delete ${dst_bname}/${dst_bname}.old"
            exit 4
        else
            mv ${dst_dname}/${dst_bname} ${dst_dname}/${dst_bname}.old
        fi
    fi

    cp -v ${src_dname}/${src_bname} ${dst_dname}/${dst_bname}
    chmod 775 ${dst_dname}/${dst_bname}
done
