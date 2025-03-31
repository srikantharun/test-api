import os
import sys
import re

def increment_filenames(directory, increment):
    pattern = re.compile(r"^(.*_)(\d+)(\.[^.]*)$")  # Match the last numeric part before extension

    for filename in os.listdir(directory):
        match = pattern.match(filename)
        if match:
            base, num, ext = match.groups()
            new_num = str(int(num) + increment)  # Increment the last number
            new_filename = f"{base}{new_num}{ext}"
            old_path = os.path.join(directory, filename)
            new_path = os.path.join(directory, new_filename)

            if os.path.exists(new_path):
                print(f"Skipping {filename}, {new_filename} already exists.")
                continue

            os.rename(old_path, new_path)
            #print(f"Renamed: {filename} -> {new_filename}")

            # Rename corresponding ELF file in build/ folder
            build_dir = os.path.join(directory, "build")
            elf_old = os.path.join(build_dir, filename.replace(".S", ""))
            elf_new = os.path.join(build_dir, new_filename.replace(".S", ""))

            if os.path.exists(elf_old):
                if os.path.exists(elf_new):
                    print(f"Skipping ELF rename for {elf_old}, {elf_new} already exists.")
                else:
                    os.rename(elf_old, elf_new)
                    #print(f"Renamed ELF: {elf_old} -> {elf_new}")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python cva6v_reindex_asms.py <directory> <increment>")
        sys.exit(1)

    input_directory = sys.argv[1]
    try:
        increment_value = int(sys.argv[2])
    except ValueError:
        print("Error: Increment value must be an integer.")
        sys.exit(1)

    if not os.path.isdir(input_directory):
        print(f"Error: '{input_directory}' is not a valid directory.")
        sys.exit(1)

    increment_filenames(input_directory, increment_value)
