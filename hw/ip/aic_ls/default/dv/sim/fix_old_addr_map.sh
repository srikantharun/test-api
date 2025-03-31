#!/bin/bash

# this script is used when we need to replace some values inside the stimuli file. it's not in use right now, but left in case we need big replacemenets in the future
# Check if exactly one argument is provided
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <output_folder>"
  exit 1
fi

output_folder="$1"

# Declare associative arrays for old and new address maps
declare -A old_address_map_csr
old_address_map_csr=(
  ["m_ifd0"]="\(^[01] \)10010\([0-9][0-9][0-9] \)"
  ["m_ifd1"]="\(^[01] \)10020\([0-9][0-9][0-9] \)"
  ["m_ifdw"]="\(^[01] \)10030\([0-9][0-9][0-9] \)"
  ["m_odr"]="\(^[01] \)10040\([0-9][0-9][0-9] \)"
  ["d_ifd0"]="\(^[01] \)10050\([0-9][0-9][0-9] \)"
  ["d_ifd1"]="\(^[01] \)10060\([0-9][0-9][0-9] \)"
  ["d_odr"]="\(^[01] \)10070\([0-9][0-9][0-9] \)"
)

declare -A new_address_map_csr
new_address_map_csr=(
  ["m_ifd0"]="\102000\2"
  ["m_ifd1"]="\102010\2"
  ["m_ifdw"]="\102030\2"
  ["m_odr"]="\102040\2"
  ["d_ifd0"]="\102050\2"
  ["d_ifd1"]="\102060\2"
  ["d_odr"]="\102070\2"
)


declare -A old_address_map_cmdb
old_address_map_cmdb=(
  ["m_ifd0"]="\(^[01] \)10011\([0-9][0-9][0-9] \)"
  ["m_ifd1"]="\(^[01] \)10021\([0-9][0-9][0-9] \)"
  ["m_ifdw"]="\(^[01] \)10031\([0-9][0-9][0-9] \)"
  ["m_odr"]="\(^[01] \)10041\([0-9][0-9][0-9] \)"
  ["d_ifd0"]="\(^[01] \)10051\([0-9][0-9][0-9] \)"
  ["d_ifd1"]="\(^[01] \)10061\([0-9][0-9][0-9] \)"
  ["d_odr"]="\(^[01] \)10071\([0-9][0-9][0-9] \)"
)

declare -A new_address_map_cmdb
new_address_map_cmdb=(
  ["m_ifd0"]="\102800\2"
  ["m_ifd1"]="\102810\2"
  ["m_ifdw"]="\102830\2"
  ["m_odr"]="\102840\2"
  ["d_ifd0"]="\102850\2"
  ["d_ifd1"]="\102860\2"
  ["d_odr"]="\102870\2"
)


declare -A old_address_map_mem
old_address_map_mem=(
  ["m_ifd0"]="\(^[01] \)10018\([0-9][0-9][0-9] \)"
  ["m_ifd1"]="\(^[01] \)10028\([0-9][0-9][0-9] \)"
  ["m_ifdw"]="\(^[01] \)10038\([0-9][0-9][0-9] \)"
  ["m_odr"]="\(^[01] \)10048\([0-9][0-9][0-9] \)"
  ["d_ifd0"]="\(^[01] \)10058\([0-9][0-9][0-9] \)"
  ["d_ifd1"]="\(^[01] \)10068\([0-9][0-9][0-9] \)"
  ["d_odr"]="\(^[01] \)10078\([0-9][0-9][0-9] \)"
)

declare -A new_address_map_mem
new_address_map_mem=(
  ["m_ifd0"]="\103000\2"
  ["m_ifd1"]="\103010\2"
  ["m_ifdw"]="\103030\2"
  ["m_odr"]="\103040\2"
  ["d_ifd0"]="\103050\2"
  ["d_ifd1"]="\103060\2"
  ["d_odr"]="\103070\2"
)

# Function to replace old addresses with new addresses
replace_address() {
  local file="$1"
  local old_pattern="$2"
  local new_value="$3"

  if [ -f "$file" ]; then
    # Using sed to replace the value inside the group with the new value
    sed -i "s/${old_pattern}/${new_value}/g" "$file"
  fi
}

# Iterate over the associative arrays and process the files
for key in "${!old_address_map_csr[@]}"; do
  old_pattern="${old_address_map_csr[$key]}"
  new_value="${new_address_map_csr[$key]}"
  output_file="$output_folder/ls_cmd.txt"

  replace_address "$output_file" "$old_pattern" "$new_value"
done

for key in "${!old_address_map_cmdb[@]}"; do
  old_pattern="${old_address_map_cmdb[$key]}"
  new_value="${new_address_map_cmdb[$key]}"
  output_file="$output_folder/ls_cmd.txt"

  replace_address "$output_file" "$old_pattern" "$new_value"
done

for key in "${!old_address_map_mem[@]}"; do
  old_pattern="${old_address_map_mem[$key]}"
  new_value="${new_address_map_mem[$key]}"
  output_file="$output_folder/ls_cmd.txt"

  replace_address "$output_file" "$old_pattern" "$new_value"
done

echo "Fixed old addresses."
