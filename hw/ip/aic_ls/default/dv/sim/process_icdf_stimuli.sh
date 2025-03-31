#! /bin/bash

# This script will copy the data from dv/icdf/stimuli to local folder, for convenience. it allows data manipulation if neccessary

# Parameters
input_folder="$1"
output_folder="$2"
OLD_ADDR_MAP=0

# Check if exactly two arguments are provided
if [ "$#" -ne 2 ]; then
  echo "Usage: $0 <input_folder> <output_folder>"
  exit 1
fi

# Check if input_folder exists
if [ ! -d "$input_folder" ]; then
  echo "Error: Input folder $input_folder does not exist."
  exit 1
fi

# Check if output_folder exists
if [ -d "$output_folder" ]; then
  # Force delete the output_folder
  rm -rf "$output_folder"
  echo "Deleted old $output_folder ."
fi

# Create the output_folder
mkdir "$output_folder"

echo "Created new $output_folder."

# Check if input_folder/cmd.txt exists
input_file="$input_folder/ls_cmd.txt"
if [ ! -f "$input_file" ]; then
  echo "Error: $input_file does not exist."
  exit 1
fi

output_file="$output_folder/ls_cmd.txt"
cp "$input_file" "$output_file"

# # Declare an associative array for text parameters
# declare -A text_patterns
# text_patterns=(
#   ["m_ifd0"]="^\d 1001\d\d\d\d "
#   ["m_ifd1"]="^\d 1002\d\d\d\d "
#   ["m_ifd2"]="^\d 1202\d\d\d\d "
#   ["m_ifdw"]="^\d 1003\d\d\d\d "
#   ["m_odr"]="^\d 1004\d\d\d\d "
#   ["d_ifd0"]="^\d 1005\d\d\d\d "
#   ["d_ifd1"]="^\d 1006\d\d\d\d "
#   ["d_odr"]="^\d 1004\d\d\d\d "
#   # Add more patterns here as needed
# )

# # Process the input file for each pattern
# for key in "${!text_patterns[@]}"; do
#   pattern="${text_patterns[$key]}"
#   output_file="$output_folder/${key}_cmd.txt"
  
#   # Execute grep and conditionally create the output file
#   grep -P "$pattern" "$input_file" > "$output_file"
# done

echo "Processed $input_file/ls_cmd.txt."

# Check if OLD_ADDR_MAP is set to 1, and run fix_old_addr_map script if it is
if [ $OLD_ADDR_MAP -eq 1 ]; then
  if [ -x "$REPO_ROOT/hw/ip/aic_ls/default/dv/sim/fix_old_addr_map.sh" ]; then
    $REPO_ROOT/hw/ip/aic_ls/default/dv/sim/fix_old_addr_map.sh $output_folder
  else
    echo "Error: fix_old_addr_map script not found or not executable."
    exit 1
  fi
fi

# Function to replace old IDLE register with STATE. remove when not needed
file="$output_folder/ls_cmd.txt"
old_pattern="\(^0 12[0-9]\{6\} [0-9]\{8\} [0-9]\{63\}\)1"
new_value="\10"

if [ -f "$file" ]; then
  # Using sed to replace the value inside the group with the new value
  sed -i "s/${old_pattern}/${new_value}/g" "$file"
fi


# Declare an associative array for text parameters
declare -A additional_files
additional_files=(
  ["ls_stream_m_dpu_to_m_odr"]="m_odr_in"
  ["ls_stream_d_dpu_to_d_odr"]="d_odr_in"
  ["ls_stream_m_ifd_w_to_m_mvmprg"]="m_ifdw_out"
  ["ls_stream_m_ifd_0_to_m_mvmexe"]="m_ifd0_out"
  ["ls_stream_m_ifd_1_to_m_dpu"]="m_ifd1_out"
  ["ls_stream_d_ifd_0_to_d_dwpu"]="d_ifd0_out"
  ["ls_stream_d_ifd_1_to_d_dpu"]="d_ifd1_out"
  ["ls_mem_pre"]="l1_mem_in"
  ["ls_mem_post"]="l1_mem_out"
  # Add more patterns here as needed
)

# Check if input_folder/file.txt exists and copy it to output_folder if it does
for key in "${!additional_files[@]}"; do
  input_file="$input_folder/${key}.txt"
  output_file="$output_folder/${additional_files[$key]}.txt"
  
  if [ -f "$input_file" ]; then
    cp "$input_file" "$output_file"
  fi
done

echo "Copied over and renamed the rest of the files."

# Delete empty files in the output folder
find "$output_folder" -type f -empty -delete

echo "Processing complete."
