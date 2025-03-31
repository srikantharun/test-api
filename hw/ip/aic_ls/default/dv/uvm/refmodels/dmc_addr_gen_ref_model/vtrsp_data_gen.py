#!/usr/bin/env python3
# This script has the reference for VTRSP functionality it recieves the ODR stream file, and the recipe, to output transposed data

import collections
import json
import sys

import numpy as np

pword_len = 64

# main function, does the transpose.
def execute_vtrsp(
  input_stream,  # list[list[int]]
  vtrsp_mode
):  # list[list[int]]
  if vtrsp_mode == "OFF":
      return input_stream

  in_stream_copy = collections.deque(input_stream.copy())
  output_stream = []

  if vtrsp_mode == "INT8":
    byte_count=1
  elif vtrsp_mode == "FP16":
    byte_count=2
  elif vtrsp_mode == "FP32":
    byte_count=4
  else:
    msg = f"unsupported VTRSP mode '{vtrsp_mode}"
    raise ValueError(msg)
  word_len = pword_len // byte_count

  # Process input stream in VTRSP unit until depleted
  transpose_buffer = []
  while True:
      # Pop stream elements into transpose buffer
      transpose_buffer.append(in_stream_copy.popleft())

      # Transpose buffer content when full
      if len(transpose_buffer) == word_len:
          transpose_buffer = np.array(transpose_buffer)
          transpose_buffer = (
              transpose_buffer.reshape((word_len, word_len, byte_count))
              .transpose((1, 0, 2))
              .reshape((word_len, pword_len))
          )
          transpose_buffer = transpose_buffer.tolist()
          output_stream.extend(transpose_buffer)
          transpose_buffer = []

      if len(in_stream_copy) == 0:
          break

  # Check VTRSP execution
  if len(transpose_buffer) != 0:
      msg = f"transpose buffer still contains {len(transpose_buffer)} PWORDs after input stream depletion"
      raise ValueError(msg)
  if len(output_stream) != len(input_stream):
      msg = f"output stream does not match input stream length: {len(output_stream)} != {len(input_stream)}"
      raise ValueError(msg)

  return output_stream

def convert_vtrsp_list_to_hex(vtrsp_list):
    # converts the int8 list into a list of hexadecimal values, so it's simpler for the tb to read and process
    hex_list = []

    for sublist in vtrsp_list:
        # Ensure each sublist has exactly 64 int8 numbers
        if len(sublist) != 64:
            raise ValueError("Each sublist must contain exactly 64 elements.")
        sublist_reversed = sublist[::-1]
        # Convert each int8 number to a 2-digit hexadecimal string
        hex_str = ''.join(f'{(num & 0xFF):02x}' for num in sublist_reversed)

        # Append the 512-bit hexadecimal string to the result list
        hex_list.append(hex_str)

    return hex_list

def hex_to_int8_list(hex_list):
    # converts the hexadecimal list into a list of int8 values, so the tb doesn't have to do that in funny ways
    int8_lists = []

    for hex_value in hex_list:
        # Convert the hexadecimal string to a binary string (without the "0x" prefix)
        binary_value = bin(int(hex_value, 16))[2:].zfill(512)  # Ensure 512 bits

        # Split the binary string into chunks of 8 bits
        int8_chunks = [binary_value[i:i+8] for i in range(0, 512, 8)]
        int8_chunks.reverse()
        # Convert each 8-bit chunk to an int8 value
        int8_list = []
        for chunk in int8_chunks:
            # Convert from binary to integer, treating the value as signed
            num = int(chunk, 2)
            if num >= 128:  # Handle two's complement for negative values
                num -= 256
            int8_list.append(num)

        # Append the list of int8 values to the final result
        int8_lists.append(int8_list)

    return int8_lists

def read_json_config(vtrsp_data_path, vtrsp_cmd_path):
  # Open and read the JSON file
  with open(vtrsp_data_path, 'r') as file:
    # Load the JSON content
    vtrsp_input_hex_list = json.load(file)

  # Extract values if they exist
  vtrsp_input_list = hex_to_int8_list(vtrsp_input_hex_list)

  with open(vtrsp_cmd_path, 'r') as file:
    command_json = json.load(file)
    vtrsp_mode = command_json["vtrsp_mode"]
    vtrsp_addresses_list = command_json["vtrsp_addresses"]
    vtrsp_mask_list = command_json["vtrsp_masks"]
    vtrsp_intra_pad_list = command_json["vtrsp_padding"]

  return vtrsp_input_list, vtrsp_mode, vtrsp_addresses_list, vtrsp_mask_list, vtrsp_intra_pad_list

if __name__ == "__main__":
  # Check if exactly two arguments are provided
  if len(sys.argv) not in (4,5):
    print("Usage: python script_name.py <input json file> <output_file>")
    sys.exit(1)  # Exit the script with an error code
  vtrsp_data_file_path = sys.argv[1]
  vtrsp_recipe_file_path = sys.argv[2]
  vtrsp_output_file_path = sys.argv[3]
  if len(sys.argv) == 5:
    int16_to_int8_conversion = True
  else:
    int16_to_int8_conversion = False

  vtrsp_input_data, vtrsp_mode, vtrsp_addresses_list, vtrsp_mask_list, vtrsp_intra_pad_list = read_json_config(vtrsp_data_file_path, vtrsp_recipe_file_path)
  vtrsp_result = execute_vtrsp(vtrsp_input_data, vtrsp_mode)
  vtrsp_to_hex_list = convert_vtrsp_list_to_hex(vtrsp_result)
  if (not int16_to_int8_conversion and len(vtrsp_to_hex_list) != len(vtrsp_addresses_list)):  # checks that lengths fit
    msg = f"output stream does not match addresses length: {len(vtrsp_to_hex_list)} != {len(vtrsp_addresses_list)}"
    raise ValueError(msg)
  if (int16_to_int8_conversion and len(vtrsp_to_hex_list) != 2*len(vtrsp_addresses_list)):
    msg = f"output stream does not match addresses length: {len(vtrsp_to_hex_list)} != {len(vtrsp_addresses_list)}"
    raise ValueError(msg)
  with open(vtrsp_output_file_path, 'w') as output_file:  # checks that lengths fit
    for i in range(len(vtrsp_to_hex_list)):
      if int16_to_int8_conversion:
        g = i//2
        output_file.write(f"addr: {vtrsp_addresses_list[g]} mask: {vtrsp_mask_list[g]} intra_pad_value: {vtrsp_intra_pad_list[g]} data: {vtrsp_to_hex_list[i]}\n")
      else:
        output_file.write(f"addr: {vtrsp_addresses_list[i]} mask: {vtrsp_mask_list[i]} intra_pad_value: {vtrsp_intra_pad_list[i]} data: {vtrsp_to_hex_list[i]}\n")
  print(f"REFERENCE MODEL: VTRSP done with final legnth {len(vtrsp_result)}")

