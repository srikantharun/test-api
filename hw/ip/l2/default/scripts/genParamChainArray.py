import re
from collections import defaultdict

def generate_chain_order_param_array(input_file, output_file, param_name, num_banks, num_rams, num_sram):
    # Convert dimension parameters to string if they are numbers
    if isinstance(num_banks, int):
        num_banks = str(num_banks)
    if isinstance(num_rams, int):
        num_rams = str(num_rams)
    if isinstance(num_sram, int):
        num_sram = str(num_sram)

    # Read lines from the specified input file
    with open(input_file, "r") as file:
        lines = file.readlines()

    # Regular expression pattern to extract the required information
    pattern = r"bank_(\d+)__u_l2_bank/g_ram_(\d+)__u_l2_ram_g_sram_(\d+)"

    # Extract tuples and store in a nested dictionary by bank, ram, sram indices
    array_data = defaultdict(lambda: defaultdict(lambda: defaultdict(lambda: 0)))

    for index, line in enumerate(lines):
        match = re.search(pattern, line)
        if match:
            bank, ram, sram = map(int, match.groups())
            array_data[bank][ram][sram] = index  # Assign the index as the value

    # Prepare SystemVerilog parameter array initialization in the requested format
    output = f"parameter int unsigned {param_name} [{num_banks}][{num_rams}][{num_sram}] = '{{\n"

    bank_keys = sorted(array_data.keys())
    for bank_index, bank in enumerate(bank_keys):
        output += f"    // Bank {bank}\n    '{{\n"  # Opening brace with single quote for SystemVerilog syntax
        ram_keys = sorted(array_data[bank].keys())
        for ram_index, ram in enumerate(ram_keys):
            output += f"        // RAM {ram}\n        {{\n"  # Opening brace without single quote

            # Write each sram value on a new line with '32'd' and its index as a comment
            max_sram_index = max(array_data[bank][ram].keys())
            for sram in range(max_sram_index + 1):
                value = array_data[bank][ram].get(sram, 0)

                # Add '32'd' prefix and a comma if it's not the last sram element
                if sram == max_sram_index:
                    output += f"          32'd{value}    // ({bank},{ram},{sram})\n"
                else:
                    output += f"          32'd{value},   // ({bank},{ram},{sram})\n"

            # Close the current RAM block, with a conditional comma
            if ram_index == len(ram_keys) - 1:
                output += "        }\n"  # No comma for the last ram in the bank
            else:
                output += "        },\n"  # Comma for all other rams

        # Close the current Bank block, with a conditional comma
        if bank_index == len(bank_keys) - 1:
            output += "    }\n"  # No comma for the last bank in the array
        else:
            output += "    },\n"  # Comma for all other banks

    output += "};\n"  # Close the full array without single quote

    # Write the generated SystemVerilog code to the specified output file
    with open(output_file, "w") as file:
        file.write(output)

    print(f"Conversion complete. SystemVerilog chain order parameter array initialized in '{output_file}'.")

# Define input and output file paths, parameter name, and array dimensions
input_file = "/data/europa/pd/l2_p/block_build/dev/doc/repair_chains.txt"  # Replace this with the actual input file path
output_file = "l2_chain_order_parameter.sv"  # Replace this with the desired output file path

param_name = "L2_ARB_CHAIN_ORDER"  # Parameter name
num_banks = "L2_NUM_BANKS"  # Use a string (can be another parameter)
num_rams = "L2_NUM_RAMS"    # Use an integer (direct size)
num_sram = "L2_NUM_SRAMS"   # Use a string (can be another parameter)

# Call the function with the defined variables
generate_chain_order_param_array(input_file, output_file, param_name, num_banks, num_rams, num_sram)
