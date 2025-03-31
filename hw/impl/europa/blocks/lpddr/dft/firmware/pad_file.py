import argparse
import random

def generate_random_binary_line(length=20):
    """Generate a random binary string of a specified length."""
    return ''.join(random.choice('0123456789abcdef') for _ in range(length)) + '\n'

def pad_file_with_data(file_path: str, total_lines: int = 6144, line_length: int = 20):
    try:
        # Read the file
        with open(file_path, 'r') as file:
            lines = file.readlines()

        # Calculate how many zeros to add
        current_line_count = len(lines)
        if current_line_count < total_lines:
            lines_to_add = total_lines - current_line_count
            lines.extend([generate_random_binary_line(line_length) for _ in range(lines_to_add)])
            print(f"File '{file_path}' padded to {total_lines} lines.")

        # Write back to the file
        with open(file_path, 'w') as file:
            file.writelines(lines)

    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

def main():
    parser = argparse.ArgumentParser(description="Pad a file with random data to ensure it has 6144 lines.")
    parser.add_argument("filename", help="The path to the file to be padded.")
    args = parser.parse_args()

    pad_file_with_data(args.filename)

if __name__ == "__main__":
    main()
