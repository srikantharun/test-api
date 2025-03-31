import pandas as pd
import matplotlib.pyplot as plt
from collections import defaultdict
import numpy as np
import argparse
import sys

# Function to safely convert TIME to float
def safe_float_convert(x):
    try:
        return float(x)
    except ValueError:
        print(f"Warning: Could not convert '{x}' to float")
        return np.nan

# Argument parser to take file inputs
parser = argparse.ArgumentParser(description='Process read and write transaction files.')
parser.add_argument('file1', type=str, help='Path to the first transaction file (either read or write).')
parser.add_argument('file2', type=str, help='Path to the second transaction file (either read or write).')
args = parser.parse_args()

# Check the filenames to identify which is the write and which is the read file
wr_file = None
rd_file = None

if args.file1.endswith('_wr_txns.txt'):
    wr_file = args.file1
elif args.file1.endswith('_rd_txns.txt'):
    rd_file = args.file1
else:
    print(f"Error: The first file '{args.file1}' must end with '_wr_txns.txt' or '_rd_txns.txt'")
    sys.exit(1)

if args.file2.endswith('_wr_txns.txt'):
    wr_file = args.file2
elif args.file2.endswith('_rd_txns.txt'):
    rd_file = args.file2
else:
    print(f"Error: The second file '{args.file2}' must end with '_wr_txns.txt' or '_rd_txns.txt'")
    sys.exit(1)

# Ensure both the read and write files are identified
if not wr_file or not rd_file:
    print("Error: Both a write transaction file and a read transaction file must be provided.")
    sys.exit(1)

# Read the data from the text files
wr_data = pd.read_csv(wr_file, delimiter=',', comment='-', usecols=['TIME', 'TXN_ID', 'THROUGHPUT'], skipinitialspace=True)
rd_data = pd.read_csv(rd_file, delimiter=',', comment='-', usecols=['TIME', 'TXN_ID', 'THROUGHPUT'], skipinitialspace=True)

# Convert THROUGHPUT to numeric
wr_data['THROUGHPUT'] = pd.to_numeric(wr_data['THROUGHPUT'].str.rstrip('%'), errors='coerce')
rd_data['THROUGHPUT'] = pd.to_numeric(rd_data['THROUGHPUT'].str.rstrip('%'), errors='coerce')

# Convert TIME to numeric
wr_data['TIME'] = wr_data['TIME'].apply(safe_float_convert)
rd_data['TIME'] = rd_data['TIME'].apply(safe_float_convert)

# Fill NaN values
wr_data = wr_data.ffill().bfill()
rd_data = rd_data.ffill().bfill()

# Function to add suffix to identical points
def add_suffix(data):
    point_count = defaultdict(int)
    suffixed_txn_ids = []

    for i, row in data.iterrows():
        point_count[row['TXN_ID']] += 1
        suffixed_txn_id = f"{row['TXN_ID']}_{point_count[row['TXN_ID']]}"
        suffixed_txn_ids.append(suffixed_txn_id)

    data['SUFFIXED_TXN_ID'] = suffixed_txn_ids
    return data

# Add suffix to identical points
wr_data = add_suffix(wr_data)
rd_data = add_suffix(rd_data)

# Function to calculate moving average
def moving_average(data, window_size):
    return data.rolling(window=window_size, center=True).mean()

# Calculate moving average for throughput
window_size = 3
wr_data['SMOOTHED_THROUGHPUT'] = moving_average(wr_data['THROUGHPUT'], window_size)
rd_data['SMOOTHED_THROUGHPUT'] = moving_average(rd_data['THROUGHPUT'], window_size)

# Plot settings
fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(20, 12))

# Plot write data
write_line, = ax1.plot(wr_data['TIME'], wr_data['THROUGHPUT'], marker='o', linestyle='-', color='blue', label='Write Throughput')
ax1.plot(wr_data['TIME'], wr_data['SMOOTHED_THROUGHPUT'], linestyle='-', color='green', label='Moving Average')
ax1.set_title('Write Performance')
ax1.set_xlabel('TIME (ns)')
ax1.set_ylabel('Throughput (%)')
ax1.legend()
ax1.grid(True)

# Plot read data
read_line, = ax2.plot(rd_data['TIME'], rd_data['THROUGHPUT'], marker='o', linestyle='-', color='red', label='Read Throughput')
ax2.plot(rd_data['TIME'], rd_data['SMOOTHED_THROUGHPUT'], linestyle='-', color='green', label='Moving Average')
ax2.set_title('Read Performance')
ax2.set_xlabel('TIME (ns)')
ax2.set_ylabel('Throughput (%)')
ax2.legend()
ax2.grid(True)

# Enable interactive mode
plt.ion()

# Create annotations for both graphs
annot1 = ax1.annotate("", xy=(0,0), xytext=(20,20),
                    textcoords="offset points",
                    bbox=dict(boxstyle="round", fc="w"),
                    arrowprops=dict(arrowstyle="->"))
annot1.set_visible(False)

annot2 = ax2.annotate("", xy=(0,0), xytext=(20,20),
                    textcoords="offset points",
                    bbox=dict(boxstyle="round", fc="w"),
                    arrowprops=dict(arrowstyle="->"))
annot2.set_visible(False)

# Function to update annotation
def update_annot(annot, ind, line, data):
    x, y = line.get_data()
    idx = ind["ind"][0]
    annot.xy = (x[idx], y[idx])
    text = (f"TIME: {data['TIME'].iloc[idx]}\n"
            f"TXN_ID: {data['SUFFIXED_TXN_ID'].iloc[idx]}\n"
            f"Throughput: {data['THROUGHPUT'].iloc[idx]:.2f}%")
    annot.set_text(text)
    annot.get_bbox_patch().set_facecolor('yellow')
    annot.get_bbox_patch().set_alpha(0.6)
    annot.set_visible(True)
    fig.canvas.draw_idle()

# Function to handle hover event
def hover(event):
    vis1 = annot1.get_visible()
    vis2 = annot2.get_visible()
    if event.inaxes == ax1:
        cont, ind = write_line.contains(event)
        if cont:
            update_annot(annot1, ind, write_line, wr_data)
        else:
            if vis1:
                annot1.set_visible(False)
                fig.canvas.draw_idle()
    elif event.inaxes == ax2:
        cont, ind = read_line.contains(event)
        if cont:
            update_annot(annot2, ind, read_line, rd_data)
        else:
            if vis2:
                annot2.set_visible(False)
                fig.canvas.draw_idle()

# Connect the hover event
fig.canvas.mpl_connect("motion_notify_event", hover)

# Show plot
plt.tight_layout()
plt.show()

# Keep the plot open in interactive mode
plt.ioff()
plt.show()

