import re
import os
import argparse
import sys

def strings_match_except_numbers(str1, str2):
    """
    Check if two strings match except for numbers in the same positions.
    Returns: (bool, list of positions) where numbers differ
    """
    if len(str1) != len(str2):
        return False, []
        
    diff_positions = []
    
    for i in range(len(str1)):
        if str1[i] != str2[i]:
            # If both characters are digits, record the position
            if str1[i].isdigit() and str2[i].isdigit():
                diff_positions.append(i)
            # If one is digit and other isn't, or both are non-digits
            else:
                return False, []
                
    return len(diff_positions) > 0, diff_positions

def process_line(line):
    line = line.replace(' {', ' { ').replace('}]', ' }]')
    strings = line.strip().split()
    result = strings.copy()
    number_positions = {}  # Dictionary to store positions for each string index
    
    # Compare each string with others in the same line
    for i in range(len(strings)):
        if result[i] is None:  # Skip if already processed
            continue
            
        base_string = strings[i]
        
        for j in range(i + 1, len(strings)):
            if result[j] is None:  # Skip if already processed
                continue
                
            compare_string = strings[j]
            
            # Check if strings match except for numbers
            matches, diff_positions = strings_match_except_numbers(base_string, compare_string)
            
            if matches:
                # Store positions for the base string if not already stored
                if i not in number_positions:
                    number_positions[i] = diff_positions
                else:
                    # Update with any new positions
                    number_positions[i] = list(set(number_positions[i] + diff_positions))
                    
                result[j] = None  # Mark the matching string for deletion
    
    # Replace numbers with * in the first string of each group
    for idx, positions in number_positions.items():
        if result[idx] is not None:
            string_chars = list(result[idx])
            for pos in positions:
                string_chars[pos] = '*'
            result[idx] = ''.join(string_chars)
    
    # Filter out None values and join with spaces
    return ' '.join(s for s in result if s is not None)

def post_process_line(line):
    strings = line.strip().split()
    # Filter out strings containing **
    filtered_strings = [s for s in strings if '**' not in s]
    # Filter out strings containing 1*, 2*, etc
    filtered_strings2 = [s for s in filtered_strings if not any(c.isdigit() and s[i+1] == '*' for i, c in enumerate(s[:-1]))]
    # Join the remaining strings back into a line
    return ' '.join(filtered_strings2)

def process_strings(filename):
    result_lines = []
    
    with open(filename, 'r') as file:
        for line in file:
            if "get_pins" in line:  # Only process lines containing "get_pins"
                processed_line = process_line(line)
                post_processed_line = post_process_line(processed_line)
                post_processed_line = post_processed_line.replace(' { ', ' {').replace(' }]', '}]')
                result_lines.append(post_processed_line)
            else:
                result_lines.append(line.rstrip('\n'))  # Keep original line if no "get_pins"
    
    # Add final newline to preserve EOF
    return '\n'.join(result_lines) + '\n'



def main() -> None:
    parser = argparse.ArgumentParser(
        description="Process an sdc file"
    )
    parser.add_argument(
        'input_file', 
        help='Path to the input file to process')
    args = parser.parse_args()

    compressed_line = process_strings(args.input_file)
    try:
        with open(args.input_file, 'w') as f_out:
            f_out.write(compressed_line)
    except FileNotFoundError:
        print(f"Error: File '{args.input_file}' not found")


if __name__ == "__main__":
    main()
