import os
import re
import argparse

def grep_files(base_dir, pattern="Vector count", verbose=False):
    """Finds .S files containing the given pattern and extracts all percentage values."""
    results = {}
    for file in os.listdir(base_dir):
        if file.endswith(".S"):
            filepath = os.path.join(base_dir, file)
            with open(filepath, "r", encoding="utf-8") as f:
                content = f.read()
                if pattern in content:
                    matches = re.findall(r"Vector count:\s*\d+\s*\(\s*(\d+\.\d{2})%\s*\)", content)
                    if matches:
                        percentages = [float(match) for match in matches]
                        if all(p == 0.00 for p in percentages):  # Delete only if ALL are 0.00%
                            results[file] = 0.00
                        else:
                            results[file] = max(percentages)  # Store max percentage for debugging

    if verbose:
        print(f"Step 1: Found {len(results)} .S files with percentage values.")

    return results

def delete_unwanted_files(base_dir, file_percentages, verbose=False):
    """Deletes only the .S files and their corresponding binaries if all percentages are 0.00%."""
    build_dir = os.path.join(base_dir, "build")
    to_delete = [file for file, percent in file_percentages.items() if percent == 0.00]

    for file in to_delete:
        asm_path = os.path.join(base_dir, file)
        bin_path = os.path.join(build_dir, file.replace(".S", ""))  # Binary without .S
        if os.path.exists(asm_path):
            os.remove(asm_path)
        if os.path.exists(bin_path):
            os.remove(bin_path)

    if verbose:
        print(f"Step 2: Deleted {len(to_delete)} files with 0.00%.")

def rename_files(base_dir, verbose=False):
    """Renames remaining files in numerical order while keeping test groups separate."""
    build_dir = os.path.join(base_dir, "build")
    files = [f for f in os.listdir(base_dir) if f.endswith(".S")]
    groups = {}

    for file in files:
        match = re.match(r"(.*_)(\d+)\.S", file)  # Extract base name and number
        if match:
            prefix, num = match.groups()
            num = int(num)  # Convert to int
            if prefix not in groups:
                groups[prefix] = []
            groups[prefix].append((num, file))

    rename_count = 0
    for prefix, file_list in groups.items():
        file_list.sort()  # Sort numerically
        available_numbers = iter(range(len(file_list)))  # Sequential numbers

        for _, old_name in file_list:
            new_num = next(available_numbers)  # Assign new sequential number
            new_name = f"{prefix}{new_num}.S"
            old_path = os.path.join(base_dir, old_name)
            new_path = os.path.join(base_dir, new_name)
            os.rename(old_path, new_path)
            rename_count += 1

            # Rename binary in build folder
            old_bin = os.path.join(build_dir, old_name.replace(".S", ""))
            new_bin = os.path.join(build_dir, new_name.replace(".S", ""))
            if os.path.exists(old_bin):
                os.rename(old_bin, new_bin)

    if verbose:
        print(f"Step 3: Renamed {rename_count} files sequentially.")

def main():
    parser = argparse.ArgumentParser(description="Clean and rename assembly test files.")
    parser.add_argument("base_dir", type=str, help="Base directory containing the .S files and build folder.")
    parser.add_argument("--pattern", type=str, default="Vector count", help="Pattern to search in .S files.")
    parser.add_argument("--verbose", action="store_true", help="Enable verbose output.")
    args = parser.parse_args()

    # Step 1: Find .S files with their percentage values
    file_percentages = grep_files(args.base_dir, args.pattern, args.verbose)

    # Step 2: Delete only files with exactly 0.00%
    delete_unwanted_files(args.base_dir, file_percentages, args.verbose)

    # Step 3: Rename remaining files sequentially
    rename_files(args.base_dir, args.verbose)

if __name__ == "__main__":
    main()
