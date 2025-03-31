#!/usr/bin/env bash

set -e

banner() {{
cat << EOF

#--------------------------------------------------------------
# $@
#--------------------------------------------------------------
EOF
}}

output_dir={output_dir}
[ -d "${{output_dir}}.old" ] && rm -rf "${{output_dir}}.old"
[ -d $output_dir ] && mv $output_dir "${{output_dir}}.old"
mkdir -p $output_dir
cd $output_dir
mkdir -p input

banner "update UCDBs DUT's hierarchy to match each other"
{coverage_edit}
rm -f transcript

banner "merge UCDBs"
vcover merge -out merged.ucdb {ucdb_list} \
  -suppress vcover-6821 # Object type mismatch detected while merging

banner "Exclude signals"

vsim -c -do <(cat << EOF
coverage open merged.ucdb
{exclude_list}
coverage save merged.ucdb
exit
EOF
)

banner "print reports"
vcover report -html -annotate -details -showexcluded -output html merged.ucdb
vcover report -output report.txt -instance=/*. -detail -showexcluded -all -code t merged.ucdb
vcover testnames merged.ucdb > testnames.txt

banner "generate CSV"
(
echo "scope,toggle_coverage"
paste -d ","  - - < <(grep "Instance:\|Toggles" report.txt | awk '{{print $NF}}' | sed -e 's#/top/##' -e 's/%//')
echo "total,$(grep 'Total Coverage By Instance' report.txt | awk '{{print $NF}}' | sed 's/%//')"
) > coverage.csv
