import argparse
import os
import yaml

def load_yaml(filename):
    with open(filename, 'r') as file:
        try:
            data = yaml.safe_load(file)
            return data
        except yaml.YAMLError as e:
            print(f"Error reading YAML file: {e}")
            return None


def save_to_file(test_list: list[str], output_file: str, header: list[str]):
    with open(output_file, 'w') as f:
        for header_line in header:
            f.write(header_line + '\n')
        for test in test_list:
            f.write(test + '\n')


def parse_asm_test_path(
    asm_test_path: list[str],
    allowed_sets: list[str],
    allowed_extensions: list[str],
    target: str,
) -> tuple[bool, str, str, str]:
    """
        Returns True if one of allowed_set and allowed_extension in the path
        Returns matched allowed_set, allowed_extension and asm testname w/o .S and _ as separator
        False + empty strings otherwise
    """
    if target == "arch":
        for allowed_set in allowed_sets:
            if allowed_set in asm_test_path:
                for allowed_extenstion in allowed_extensions:
                    if allowed_extenstion in asm_test_path:
                        asm_test_name = asm_test_path[-1][:-2] # get test name, drop .S
                        asm_test_name = asm_test_name.replace("-", "_").replace(".", "_")
                        return True, allowed_set+"_"+allowed_extenstion, asm_test_name
    else:
        asm_test_name = asm_test_path[-1][:-2] # get test name, drop .S
        asm_test_name = asm_test_name.replace("-", "_").replace(".", "_")
        return True, asm_test_path[-3], asm_test_name
    return False, "", ""


def generate_testlist_from_parsed_yaml(
    parsed_yaml: list[dict[str]],
    allowed_sets: list[str],
    allowed_extensions: list[str],
    testname_prefix: str,
    testname_suffix:str,
    target: str,
) -> list[str]:
    """
        Parses yaml for tests containing allowed extension and set in their path.
        Modifies testname by adding prefix, suffix and replaces (-, .) with _.
        Returns a list of testnames.
    """
    sep = "_"
    tests = []
    nonzero_iterations_yaml = (entry for entry in parsed_yaml if entry["iterations"])
    for entry in nonzero_iterations_yaml:
        test_path_decomposed=entry["asm_tests"].split("/")
        test_valid, set_and_ext, test_name = parse_asm_test_path(
            asm_test_path=test_path_decomposed,
            allowed_sets=allowed_sets,
            allowed_extensions=allowed_extensions,
            target=target,
        )
        if test_valid:
            full_test_name = sep.join([testname_prefix, set_and_ext, test_name, testname_suffix])
            tests.append(full_test_name)
    return tests


def generate_testlist(target: str):
    """
        Creates arch testlist by processing all tests from the riscv-arch-test folder.
        Filters out .asm files based on allowed_sets and allowed_extensions.
        Saves testlist to the riscv_arch_tests.list in the sim-mini-soc folder.
    """
    allowed_sets=["rv64i_m"]
    allowed_extensions=["A", "C", "F", "I", "M", "privlege", "Zifencei"]
    env_folder_path_var = "CVA6_VERIF_HOME"
    env_out_file_path_var = "REPO_ROOT"
    header = []
    if not os.getenv(env_folder_path_var) or not os.getenv(env_out_file_path_var):
        print(f"{env_folder_path_var} or {env_out_file_path_var} environment variable is not set.")
        return

    if target == "arch":
        tests_file = os.getenv(env_folder_path_var) + "/tests/testlist_riscv-arch-test-cv64a6_imafdc_sv39.yaml"
        header = [
            "# PW: 71 less tests compared to older list",
            "# 9 fmv which are for D ext (double precision, not supported)",
            "# 18 fcvt (see above)",
            "# 43 B-extension tests (not supported)",
            "# 1 with iterations: 0",
        ]
    else:
        tests_file = os.getenv(env_folder_path_var) + "/tests/testlist_riscv-compliance-cv64a6_imafdc_sv39.yaml"

    out_file = os.getenv(env_out_file_path_var) + f"/hw/vendor/axelera/cva6v/default/dv/sim-mini-soc/riscv_{target}.list"
    testname_prefix = f"cva6v_riscv_{target}"

    test_data = load_yaml(tests_file)
    test_list = generate_testlist_from_parsed_yaml(
        parsed_yaml=test_data,
        allowed_sets=allowed_sets,
        allowed_extensions=allowed_extensions,
        testname_prefix=testname_prefix,
        testname_suffix="test",
        target=target,
    )
    save_to_file(
        test_list=test_list,
        output_file=out_file,
        header=header,
    )
    print(f"{os.path.basename(__file__)} generated {len(test_list)} tests to\n{out_file}")


def parse_arguments():
    parser = argparse.ArgumentParser(
        description=(
            "Script to create riscv tests list from predefined YAML"
        )
    )
    allowed_targets = ("arch", "compliance", "all")
    parser.add_argument(
        "-t",
        "--target",
        dest="target",
        type=str,
        default="arch",
        help=f"Defines what testlist to generate: {allowed_targets}",
    )

    parsed_args = parser.parse_args()
    if parsed_args.target not in allowed_targets:
        parser.error(f"Unrecognized target {parsed_args.target}")
    return parsed_args


def main():
    parsed_args = parse_arguments()
    generate_testlist(
        target=parsed_args.target,
    )


if __name__ == "__main__":
    main()
