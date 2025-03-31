#!/usr/bin/env python3
import argparse

def hex_to_bin_file(hex_file, bin_file, word_size=16):
    with open(hex_file, 'r') as infile, open(bin_file, 'w') as outfile:
        for line in infile:
            # Remove leading/trailing whitespace and ignore lines that are comments or blank
            line = line.strip()
            if not line or line.startswith("//"):  # Skip blank lines or comment lines
                continue

            # Split the line into individual hex values, ignoring any non-hex characters
            hex_values = line.split()
            for hex_value in hex_values:
                try:
                    # Convert hex to binary, padding to the word size
                    bin_value = format(int(hex_value, 16), f'0{word_size}b')
                    # Write the binary value to the output file
                    outfile.write(bin_value + '\n')
                except ValueError:
                    print(f"Skipping invalid hex value: {hex_value}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert hex file to binary file for SystemVerilog's readmemb")
    
    # Positional arguments
    parser.add_argument("hex_file", help="Input hex file to be converted")
    parser.add_argument("bin_file", help="Output binary file to be written")
    
    # Optional arguments
    parser.add_argument("--word_size", type=int, default=16, 
                        help="Word size in bits (default: 16)")

    # Parse the command-line arguments
    args = parser.parse_args()
    
    # Call the conversion function with the provided arguments
    hex_to_bin_file(args.hex_file, args.bin_file, args.word_size)
