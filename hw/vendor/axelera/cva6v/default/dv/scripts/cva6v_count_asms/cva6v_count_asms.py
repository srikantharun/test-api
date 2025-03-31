import os
from collections import defaultdict

# Function to count assembly files per test
def count_asm_tests(directory):
    asm_files = defaultdict(int)

    # Iterate over files in the directory
    for filename in os.listdir(directory):
        # Check if file ends with .S
        if filename.endswith(".S"):
            # Extract the base name (ignoring the index and extension)
            base_name = filename.rsplit('_', 1)[0]
            asm_files[base_name] += 1

    # Number the tests and print the count
    for index, (test, count) in enumerate(asm_files.items(), start=1):
        print(f"Test {index}: {test} - {count}")

# Take directory input from the user or default to current directory
directory = input("Enter directory path (leave blank for current directory): ").strip()

# If no directory is provided, use the current folder
if not directory:
    directory = os.getcwd()

# Call the function
count_asm_tests(directory)
