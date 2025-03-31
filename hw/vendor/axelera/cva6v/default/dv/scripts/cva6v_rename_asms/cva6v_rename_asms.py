import os
import sys

def rename_files_in_directory(directory, remove_text, replacement_text):
    try:
        # Check if the provided path is a valid directory
        if not os.path.isdir(directory):
            print(f"Error: '{directory}' is not a valid directory.")
            return

        # Iterate over the files in the directory
        for filename in os.listdir(directory):
            # Check if the filename contains the remove_text
            if remove_text in filename:
                # Construct the new filename
                new_filename = filename.replace(remove_text, replacement_text)

                # Build full paths for renaming
                old_file_path = os.path.join(directory, filename)
                new_file_path = os.path.join(directory, new_filename)

                # Rename the file
                os.rename(old_file_path, new_file_path)
                print(f"Renamed: '{filename}' -> '{new_filename}'")

        print("Renaming process completed.")
    except Exception as e:
        print(f"Error: {e}")

# Main entry point
if __name__ == "__main__":
    # Check if correct number of arguments are provided
    if len(sys.argv) != 4:
        print("Usage: python script.py <directory_path> <text_to_remove> <replacement_text>")
        sys.exit(1)

    # Get inputs from arguments
    directory_path = sys.argv[1]
    text_to_remove = sys.argv[2]
    replacement_text = sys.argv[3]

    # Process the directory
    rename_files_in_directory(directory_path, text_to_remove, replacement_text)
