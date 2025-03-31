#!/usr/bin/env python

import re
import sys


# Custom function to process the match
def calculate_replacement(match):
    number = int(match.group(1))  # Extract the number
    clock  = str(match.group(2))  # Extract the clock

    # Perform your calculation, to convert from the testbench clock ticks to TCK ticks
    if 'dficlk' in clock:
        calculated_number = number / 16
    elif 'apbclk' in clock:
        calculated_number = number / 2
    else:
        calculated_number = number * 1

    
    return str(int(calculated_number))  # Return the calculated value as a string



def process_file(input_file, output_file, backdoor):
    """
    Process the input file to merge pairs of csr_rd_masked lines and format TCL code.
    """
    try:
        f = open(input_file, 'r')
        lines = f.readlines()
        f.close()
    except:
        sys.stderr.write("Error reading input file\n")
        sys.exit(1)

    clk_mod_pattern = r"CLK_MOD_\s*(\d+)_(\w+)"
    modified_lines = []
    i = 0
    while i < len(lines):
        current_line = lines[i]
        i += 1
        if 'CLK_MOD' in current_line:
            current_line = re.sub(clk_mod_pattern, calculate_replacement, current_line)  
                    
        modified_lines.append(current_line)
        


    inside_task = False
    task_start_pattern = re.compile(r'.*?INFO: polling DWC_DDRPHYA_APBONLY0_UctShadowRegs.*')
    task_end_pattern = re.compile(r'.*?INFO: End polling DWC_DDRPHYA_APBONLY0_UctShadowRegs.*')
    second_modified_lines = []
    i = 0
    while i < len(modified_lines):
        current_line = modified_lines[i]
        i += 1
        # Track task boundaries
        if task_start_pattern.search(current_line):
            inside_task = True
        elif task_end_pattern.search(current_line):
            inside_task = False
           
        if inside_task and 'csr_rd' in current_line :
            continue
        else:
            second_modified_lines.append(current_line)
       

    if backdoor:
        mem_start_pattern = re.compile(r'.*?Start\s+.mem\s+load.*')
        mem_end_pattern   = re.compile(r'.*?End\s+.mem\s+load.*')
        third_modified_lines = []
        i = 0
        first=True
        while i < len(second_modified_lines):
            current_line = second_modified_lines[i]
            i += 1
            # Track task boundaries
            if mem_start_pattern.search(current_line):
                inside_task = True
                if first:
                    third_modified_lines.append("    iCall simulation_only_backdoor_load_mem\n")
                    first=False
            elif mem_end_pattern.search(current_line):
                inside_task = False

            if inside_task :
                continue
            else:
                third_modified_lines.append(current_line)
    else:
       third_modified_lines = second_modified_lines     

            

    try:
        f = open(output_file, 'w')
        f.writelines(third_modified_lines)
        f.close()
    except:
        sys.stderr.write("Error writing output file\n")
        sys.exit(1)

def main():
    if len(sys.argv) < 3 or len(sys.argv) > 4:
        sys.stderr.write("Usage: python script.py input_file output_file [backdoor]\n")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2]

    #will be doing backdoor loading of memory
    if len(sys.argv) == 4 and sys.argv[3].lower() == "backdoor":
        backdoor=True
    else:
        backdoor=False
    
    try:
        process_file(input_file, output_file,backdoor)
        sys.stdout.write("Processing complete. Output written to %s\n" % output_file)
    except Exception as e:
        import traceback
        sys.stderr.write(f"Traceback: {''.join(traceback.format_tb(e.__traceback__))}")
        sys.stderr.write("Error processing file\n")
        sys.exit(1)

if __name__ == "__main__":
    main()
