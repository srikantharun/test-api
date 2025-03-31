#!/usr/bin/env python

import re
import sys

def align_tcl_comments(lines):
    """
    Align TCL comments (;#) across multiple lines and handle indentation.
    Returns aligned lines.
    """
    max_code_length = 0
    code_lengths = []
    
    for line in lines:
        parts = re.split(r'(?<![\\"]);#', line.rstrip())
        if len(parts) > 1:
            code_length = len(parts[0].rstrip())
            max_code_length = max(max_code_length, code_length)
            code_lengths.append(code_length)
        else:
            code_lengths.append(None)
    
    aligned_lines = []
    for i in range(len(lines)):
        if code_lengths[i] is not None:
            parts = re.split(r'(?<![\\"]);#', lines[i].rstrip(), maxsplit=1)
            code_part = parts[0].rstrip()
            comment_part = parts[1] if len(parts) > 1 else ""
            padding = " " * (max_code_length - len(code_part) + 2)
            aligned_lines.append("%s%s;# %s\n" % (code_part, padding, comment_part.lstrip()))
        else:
            aligned_lines.append(lines[i])
    
    return aligned_lines

def get_indent_level(line):
    """
    Determine the proper indent level based on TCL syntax.
    """
    stripped_line = line.strip()
    if stripped_line.startswith('}'):
        return -1
    elif stripped_line.endswith('{'):
        return 1
    return 0

def indent_tcl(lines, base_indent=4):
    """
    Apply proper TCL indentation to the lines.
    """
    current_indent = 0
    indented_lines = []
    
    for line in lines:
        stripped = line.strip()
        if stripped:
            indent_change = get_indent_level(line)
            if indent_change < 0:
                current_indent = max(0, current_indent - 1)
            
            indented_line = ' ' * (current_indent * base_indent) + line.lstrip()
            indented_lines.append(indented_line)
            
            if indent_change > 0:
                current_indent += 1
        else:
            indented_lines.append(line)
            
    return indented_lines

def align_command_arguments(line):
    """
    Align arguments in crsel_read_masked commands.
    """
    if 'crsel_read_masked' in line:
        parts = re.split(r'(?<![\\"]);#', line.rstrip(), maxsplit=1)
        command_part = parts[0]
        comment_part = parts[1] if len(parts) > 1 else ""
        
        components = command_part.split()
        if len(components) >= 4:
            aligned_command = components[0].ljust(20)
            for arg in components[1:4]:
                aligned_command += arg.ljust(8)
            
            if comment_part:
                return "%s ;# %s\n" % (aligned_command.rstrip(), comment_part.lstrip())
            return aligned_command + "\n"
    
    return line

def process_file(input_file, output_file):
    """
    Process the input file to merge pairs of crsel_read_masked lines and format TCL code.
    """
    try:
        f = open(input_file, 'r')
        lines = f.readlines()
        f.close()
    except:
        sys.stderr.write("Error reading input file\n")
        sys.exit(1)

    # Dictionary to store address values from the first type of line
    addr_values = {}
    # List to store indices of lines to be removed
    lines_to_remove = set()

    # First pass: find crsel_read_masked lines that are immediately followed by ADDR_MOD
    i = 0
    while i < len(lines) - 1:  # Stop one line before the end
        line = lines[i].strip()
        next_line = lines[i + 1].strip() 
        
        # Check if current line matches first pattern and next line has ADDR_MOD
        match = re.match(r'crsel_read_masked\s+(0x[0-9A-Fa-f]+)\s+0x[0-9A-Fa-f]+\s+0x[0-9A-Fa-f]+\s*$', line)
        if match and 'ADDR_MOD' in next_line and 'crsel_read_masked' in next_line:
            addr = match.group(1)
            addr_values[i] = addr
            lines_to_remove.add(i)
        i += 1

    # Second pass: process ADDR_MOD lines and perform replacements
    modified_lines = []
    i = 0
    while i < len(lines):
        if i in lines_to_remove:
            i += 1
            continue
            
        current_line = lines[i]
        if 'ADDR_MOD' in current_line and 'crsel_read_masked' in current_line:
            # Get the address from the line immediately above
            prev_index = i - 1
            if prev_index in addr_values:
                modified_line = current_line.replace('ADDR_MOD', addr_values[prev_index])
                modified_lines.append(modified_line)
            else:
                modified_lines.append(current_line)
        else:
            modified_lines.append(current_line)
        i += 1


    #third pass
     
    # Track if we're inside the INTTASK block
    inside_task = False
    task_start_pattern = re.compile(r'BEGIN_INTTASK\s*<check_rx_lbert@X>')
    task_end_pattern = re.compile(r'END_INTTASK\s*<check_rx_lbert@X>')
    pause_pattern = re.compile(r'\s+Insert the vector pause of interest for normal FW in ate.vec at line number.*')
    
    second_modified_lines = []
    i = 0
    while i < len(modified_lines):
        current_line = modified_lines[i]
        # Track task boundaries
        if task_start_pattern.search(current_line):
            inside_task = True
        elif task_end_pattern.search(current_line):
            inside_task = False
         
        # Convert read_capture to read_nodata if inside task block
        if inside_task and 'crsel_read_capture' in current_line:
            current_line = current_line.replace('crsel_read_capture', 'crsel_read_nodata')

        second_modified_lines.append(current_line)

        if pause_pattern.search(current_lines):
            second_modified_lines.append("    if {$manuf} {")
            second_modified_lines.append("      iNote \"	 Waiting for 8 miliseconds for expected events to take place\""
            second_modified_lines.append("      iRunLoop 800000 -tck")
            second_modified_lines.append("    }")
               
        
        i += 1


    # Apply TCL formatting
    indented_lines = indent_tcl(second_modified_lines)
    
    aligned_commands = []
    for line in indented_lines:
        aligned_commands.append(align_command_arguments(line))
    
    final_lines = align_tcl_comments(aligned_commands)

    try:
        f = open(output_file, 'w')
        f.writelines(final_lines)
        f.close()
    except:
        sys.stderr.write("Error writing output file\n")
        sys.exit(1)

def main():
    if len(sys.argv) != 3:
        sys.stderr.write("Usage: python script.py input_file output_file\n")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2]
    
    try:
        process_file(input_file, output_file)
        sys.stdout.write("Processing complete. Output written to %s\n" % output_file)
    except Exception as e:
        import traceback
        sys.stderr.write(f"Traceback: {''.join(traceback.format_tb(e.__traceback__))}")
        sys.stderr.write("Error processing file\n")
        sys.exit(1)

if __name__ == "__main__":
    main()
