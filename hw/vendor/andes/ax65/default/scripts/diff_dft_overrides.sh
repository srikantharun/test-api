#!/usr/bin/env bash
#
# Purposes:
# Diff the local overrides with the original files from Andes
# Should only show the diff surrounded between anchors:
# - //// AXELERA OVERRIDE START
# - //// AXELERA OVERRIDE END

if [[ -z "${REPO_ROOT}" ]]; then
  echo -e "\033[31;1mERROR\033[0;m: REPO_ROOT environment variable is not set, please source .env-default-modules"
  exit 1
fi
if [[ -z "${NDS_HOME}" ]]; then
  echo -e "\033[31;1mERROR\033[0;m: NDS_HOME environment variable is not set, please source .env-default-modules"
  exit 1
fi

for local_override in ${REPO_ROOT}/hw/vendor/andes/ax65/default/rtl/dft_override/*
do
  echo $local_override
  diff \
    $local_override \
    ${NDS_HOME}/andes_ip/mk_core/cluster/hdl/$(basename ${local_override})
done

