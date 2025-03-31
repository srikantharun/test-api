import csv
import argparse
import re

# List of CSR instructions to check (add more if needed)
csr_list = ['minstret', 'mcycle', 'instret', 'cycle',
    'mhpmcounter3', 'mhpmcounter4', 'mhpmcounter5', 'mhpmcounter6', 'mhpmcounter7', 'mhpmcounter8', 'mhpmcounter9', 'mhpmcounter10', 'mhpmcounter11',
    'mhpmcounter12', 'mhpmcounter13', 'mhpmcounter14', 'mhpmcounter15', 'mhpmcounter16', 'mhpmcounter17', 'mhpmcounter18', 'mhpmcounter19', 'mhpmcounter20' 'mhpmcounter21',
    'mhpmcounter22', 'mhpmcounter23', 'mhpmcounter24', 'mhpmcounter25', 'mhpmcounter26', 'mhpmcounter27', 'mhpmcounter28', 'mhpmcounter29', 'mhpmcounter30' 'mhpmcounter31',
    'hpmcounter3', 'hpmcounter4', 'hpmcounter5', 'hpmcounter6', 'hpmcounter7', 'hpmcounter8', 'hpmcounter9', 'hpmcounter10', 'hpmcounter11',
    'hpmcounter12', 'hpmcounter13', 'hpmcounter14', 'hpmcounter15', 'hpmcounter16', 'hpmcounter17', 'hpmcounter18', 'hpmcounter19', 'hpmcounter20' 'hpmcounter21',
    'hpmcounter22', 'hpmcounter23', 'hpmcounter24', 'hpmcounter25', 'hpmcounter26', 'hpmcounter27', 'hpmcounter28', 'hpmcounter29', 'hpmcounter30' 'hpmcounter31',
    'stval' # TODO: spike bug on ecall
]  # Add other CSRs as needed

def process_csv(input_file, output_file, csr_list):
    with open(input_file, mode='r') as infile, open(output_file, mode='w', newline='') as outfile:
        reader = csv.DictReader(infile)
        fieldnames = reader.fieldnames

        # Open the CSV writer
        writer = csv.DictWriter(outfile, fieldnames=fieldnames)
        writer.writeheader()
        previous_line = None

        # Process each row
        for row in reader:

            # Get the CSR instruction from the "instr_str" column
            instr_str = row['instr_str']

            # Check if any CSR from the list appears in the instruction
            if any(csr in instr_str for csr in csr_list):
                # Set GPR to 0 if it exists
                if 'gpr' in row and row['gpr']:
                    reg_name, _ = row['gpr'].split(':')
                    row['gpr'] = f"{reg_name}:0000000000000000"

            writer.writerow(row)

def main():
    # Set up argument parser with default values
    parser = argparse.ArgumentParser(description='Process a CSV file and zero out GPR for specific CSRs.')
    parser.add_argument('--input', type=str, default='sim_rvvi_raw.csv', help='Input CSV file (default: sim_rvvi_raw.csv)')
    parser.add_argument('--output', type=str, default='sim_rvvi.csv', help='Output CSV file (default: sim_rvvi.csv)')

    # Parse the arguments
    args = parser.parse_args()

    # Process the CSV file
    process_csv(args.input, args.output, csr_list)

if __name__ == '__main__':
    main()
