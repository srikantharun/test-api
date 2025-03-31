import os
import argparse

def get_first_diff(diff_file, max_lines=1000):
    """Read the first block of diffs, supporting multiple consecutive < and > lines, up to a maximum of max_lines."""
    first_diff_block = []
    capturing_diff = False
    starting_string = ""
    ending_string = ""

    try:
        with open(diff_file, 'r') as file:
            for line in file:
                # Stop capturing once we reach the maximum number of lines
                if len(first_diff_block) >= max_lines:
                    break

                # Start capturing if we see < or > lines
                if line.startswith('< ') or line.startswith('> '):
                    if starting_string == "":
                        first_diff_block.append(line.strip())
                        starting_string = "<" if line.startswith('< ') else ">"
                    elif ending_string == "":
                        if line.startswith('< ') and starting_string == "<":
                            first_diff_block.append(line.strip())
                        elif line.startswith('< ') and starting_string == ">":
                            first_diff_block.append(line.strip())
                            ending_string = ">"
                        elif line.startswith('> ') and starting_string == ">":
                            first_diff_block.append(line.strip())
                        else:
                            first_diff_block.append(line.strip())
                            ending_string = ">"
                elif capturing_diff:
                    break
                else:
                    if starting_string and not line.startswith('---'):
                        capturing_diff = True

    except Exception as e:
        print(f"Error reading file {diff_file}: {e}")

    if first_diff_block:
        return "\n".join(first_diff_block)
    return None

def collect_first_diffs(regression_folder, max_lines=1000):
    """Collect the first diff block from each sim_rvvi.diff in the run directories."""
    diffs = {}

    for root, dirs, files in os.walk(regression_folder):
        for file_name in files:
            if file_name == 'sim_rvvi.diff':
                diff_file_path = os.path.join(root, file_name)
                first_diff = get_first_diff(diff_file_path, max_lines)
                if first_diff:
                    dir_name = os.path.basename(root)
                    diffs[dir_name] = first_diff

    return diffs

def save_diffs_to_file(diffs, output_file):
    """Save the collected diffs to an output file."""
    with open(output_file, 'w') as out_file:
        for run_dir, diff in diffs.items():
            out_file.write(f"Run Directory: {run_dir}\n{diff}\n\n")

if __name__ == "__main__":
    # Use argparse to get the regression folder as a command-line argument
    parser = argparse.ArgumentParser(description="Collect first diffs from sim_rvvi.diff files")
    parser.add_argument('regression_folder', help="Path to the regression folder containing run directories")
    parser.add_argument('--output', default="first_diffs.txt", help="Output file to save the diffs (default: first_diffs.txt)")
    parser.add_argument('--max_lines', type=int, default=1000, help="Maximum number of lines to parse in each diff file (default: 100)")

    args = parser.parse_args()

    # Collect diffs
    diffs = collect_first_diffs(args.regression_folder, args.max_lines)

    # Save diffs to file
    save_diffs_to_file(diffs, args.output)

    print(f"Collected diffs have been saved to {args.output}")
