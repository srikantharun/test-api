# Example usage:
#cva6v_gen_imperas_testlist /home/projects_2/workspace/pwiecha/europa/hw/vendor/axelera/cva6v/default/dv/deps/tests/imperas-riscv-tests/riscv-test-suite/rv64i_m/F/src
# --reqid CVA6V_FEAT_1 CVA6V_FEAT_2 CVA6V_FEAT_3 --vsdk --name cva6v_imperas_F_rv64i
# --extlabel F --extpath F --arch 64
#
# cva6v_gen_imperas_testlist ../deps/tests/imperas-riscv-tests/riscv-test-suite/rv64i_m/Vf/src/ --vsdk  --name cva6v_imperas_Vf_rv64i --reqid CVA6V_FEAT_11 CVA6V_FEAT_12 CVA6V_FEAT_13 CVA6V_FEAT_14 --extlabel VF --extpath Vf

import argparse
import os
import subprocess

# Define the output file path

# Configuration for the common parameters
iterations = 1
path_var = "TESTS_PATH"
gcc_opts = "-DVLEN=4096 -D rvtest_mtrap_routine -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -I<path_var>/../../asm/env"
description = "TODO"
platforms = "[cva6v.*]"
owner = "Raymond Garcia"
exclude_tests = ["SEW64", "EI64", "RE64"] # tests with 64-bit standard element widths will not compile in zve32f

# Set up argument parsing for the --vsdk flag and directory argument
parser = argparse.ArgumentParser(description="Generate output in either default or vsdk format based on .S files in a directory.")
parser.add_argument("directory", help="Path to the directory containing .S files")
parser.add_argument("--vsdk", action="store_true", help="Generate output in vsdk format")
parser.add_argument("--extlabel", type=str, default="V", help="Generates verifsdk label")
parser.add_argument("--extpath", type=str, default="Vi", help="Path to the ASM subfolder in the imperas structure")
parser.add_argument("--reqid", type=str, default="", nargs="+", help="Requirement IDs to generate")
parser.add_argument("--arch", type=int, default=64, help="32 vs 64")
parser.add_argument("--name", type=str, default="cva6v_imperas_vector_rv64i", help="Name prefix")
args = parser.parse_args()

labels = f"[CVA6V_DV_TESTS, CVA6V_DV_IMPERAS_TESTS, CVA6V_DV_IMPERAS_{args.extlabel}_TESTS]"
flags = f"[RUN_SCRIPT_ONLY, ELF=$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/deps/tests/build/imperas-riscv-tests/riscv-test-suite/rv{args.arch}i_m/{args.extpath}/src/"
if not args.reqid:
    requirement_ids = "[]"
else:
    requirement_ids = "["
    for id in args.reqid:
        requirement_ids += id
        requirement_ids += ", "
    requirement_ids = requirement_ids[:-2]+"]" # drop last ", "
if args.vsdk:
    output_file_path = f"tests_fw_cva6v_imperas_fillhere_rv{args.arch}i_{args.extpath}.yaml"
else:
    output_file_path = f"testlist_imperas_riscv-tests-cv64a6_fillhere_rv{args.arch}i_{args.extpath}.yaml"

# Get list of all .S files in the specified directory
try:
    test_names = [f for f in os.listdir(args.directory) if f.endswith(".S")]
except FileNotFoundError:
    print(f"Directory '{args.directory}' not found.")
    sys.exit(1)

# check for tests that use 64-bit load and stores and exclude them! They won't compile with zve32f!
# command = f"grep -rl vle64 {args.directory}/*.S"
command = f"grep -rl -e 'vle64' -e 'fmv.d' -e 'fmv.x.d' {args.directory}/*.S"
result = subprocess.run(command, shell=True, capture_output=True, text=True)

# Check if the command was successful
if result.returncode == 0:
    # Get the output file paths
    file_paths = result.stdout.strip().split("\n")

    # Extract only the filenames without paths or extensions
    filenames_without_extension = [os.path.basename(file).rsplit(".S", 1)[0] for file in file_paths if file]

    # Print the resulting array
    exclude_tests.extend(filenames_without_extension)
    print(exclude_tests)
else:
    print(f"Command failed with error: {result.stderr}")

# Open the output file to write the results
with open(output_file_path, 'w') as output_file:
    if args.vsdk:
        # Generate the YAML-style output
        output_file.write("tests:\n")
        for test_name in test_names:
            test_base = test_name.replace(".S", "")  # Remove .S extension for the name and flags
            output_entry = (
                f"  - name: {args.name}_{test_base}\n"
                f"    description: \"{description}\"\n"
                f"    labels: {labels}\n"
                f"    requirement_ids: {requirement_ids}\n"
                f"    platforms: {platforms}\n"
                f"    owner: {owner}\n"
                f"    flags: {flags}{test_base}]\n\n"
            )
            if not any(substring in test_base for substring in exclude_tests):
                output_file.write(output_entry)
    else:
        # Generate the first format with "<path_var>" exactly as written in asm_tests
        for test_name in test_names:
            test = test_name.replace(".S", "")
            output_entry = (
                f"- test: {test}\n"
                f"  iterations: {iterations}\n"
                f"  path_var: {path_var}\n"
                f"  gcc_opts: \"{gcc_opts}\"\n"
                f"  asm_tests: <path_var>/imperas-riscv-tests/riscv-test-suite/rv{args.arch}i_m/{args.extpath}/src/{test_name}\n\n"
            )
            if not any(substring in test_name for substring in exclude_tests):
                output_file.write(output_entry)

print(f"Output successfully written to {output_file_path}")
