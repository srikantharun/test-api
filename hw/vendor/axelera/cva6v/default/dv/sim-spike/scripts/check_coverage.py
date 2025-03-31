import argparse
import re
import pandas as pd

# Define all requirements based on previous analysis
instructions = [
    'ADD', 'SUB', 'MUL', 'DIV', 'REM',
    'ADDW', 'SUBW', 'MULW', 'DIVW', 'REMW'
]

# Register mapping from ABI names to numeric names
register_map = {
    'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4,
    't0': 5, 't1': 6, 't2': 7, 's0': 8, 'fp': 8, 's1': 9,
    'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17,
    's2': 18, 's3': 19, 's4': 20, 's5': 21, 's6': 22, 's7': 23, 's8': 24, 's9': 25, 's10': 26, 's11': 27,
    't3': 28, 't4': 29, 't5': 30, 't6': 31
}

# Updated regex pattern to match the log format
pattern = re.compile(r"core\s+\d+:\s+0x[0-9a-f]+\s+\(0x[0-9a-f]+\)\s+(add|sub|mul|div|rem|addw|subw|mulw|divw|remw)\s+x(\d+),\s*x(\d+),\s*x(\d+)\s+\(0x[0-9a-f]+\s*\)")

def parse_log(log_path):
    matches = []

    with open(log_path, 'r') as file:
        for line in file:
            match = pattern.match(line)
            if match:
                instruction = match.group(1).upper()
                rd = int(match.group(2))
                rs1 = int(match.group(3))
                rs2 = int(match.group(4))
                matches.append((instruction, rd, rs1, rs2))

    return matches

def analyze_coverage(log_data):
    df = pd.DataFrame(log_data, columns=['instruction', 'rd', 'rs1', 'rs2'])
    coverage = df.groupby('instruction').apply(lambda x: x[['rd', 'rs1', 'rs2']].drop_duplicates().shape[0])

    return coverage

def main(log_path):
    log_data = parse_log(log_path)
    coverage = analyze_coverage(log_data)

    print("Coverage Analysis:")
    for instruction, count in coverage.items():
        print(f"{instruction}: {count}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Analyze instruction coverage.')
    parser.add_argument('log', type=str, help='Path to the log file to analyze.')
    args = parser.parse_args()

    main(args.log)
