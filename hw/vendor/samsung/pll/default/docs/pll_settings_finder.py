import pandas as pd
import numpy as np
import argparse

# Define the variables
p_values = np.arange(1, 64)
m_values = np.arange(64, 1024)
s_values = np.arange(0, 7)
# Create an argument parser
parser = argparse.ArgumentParser()

# Add arguments for Fin, specific_Fout, and margin
parser.add_argument("-Fin", type=float, default=20e6, required=True, help="The value of Fin reference frequency for the PLL")
parser.add_argument("-Ftarget", type=float, default=800e6, required=True, help="The specific value of the output frequency you are looking up the settings for.")
parser.add_argument("-margin", type=float, default=0, required=False, help="The margin our the output frequency you are also interested in. Default is 0.")

# Parse the command line arguments
args = parser.parse_args()

# Assign the parsed values to variables
Fin = args.Fin
specific_Fout = args.Ftarget
margin = args.margin

# Create an empty DataFrame
df = pd.DataFrame(columns=["p", "m", "s", "Fout"])

# Iterate over all combinations of p, m, and s
# Create an empty list to store the data
data = []
# Iterate over all combinations of p, m, and s
for p in p_values:
    for m in m_values:
        for s in s_values:
            # Calculate Fout
            Fout = (m * Fin) / (p * 2**s)
            # Append the result to the list
            data.append({"p": p, "m": m, "s": s, "Fout": Fout})
# Create a DataFrame from the list of data
df = pd.DataFrame(data)

# Filter the DataFrame to only include rows where Fout is within the specified margin of the specific Fout value
if margin == 0:
    closest_Fout = df.loc[df['Fout'].sub(specific_Fout).abs().idxmin(), 'Fout']
    df_filtered = df[df['Fout'] == closest_Fout]
else:
    # Filter the DataFrame to only include rows where Fout is within the specified margin of the specific Fout value
    if margin == 0:
        closest_Fout = df.loc[df['Fout'].sub(specific_Fout).abs().idxmin(), 'Fout']
        df_filtered = df[df['Fout'] == closest_Fout]
    else:
        df_filtered = df[
            (df["Fout"] >= specific_Fout * (1 - margin))
            & (df["Fout"] <= specific_Fout * (1 + margin))
        ]
        # If no Fout is found in the range, select the closest match Fout value
        if df_filtered.empty:
            closest_Fout = df.loc[df['Fout'].sub(specific_Fout).abs().idxmin(), 'Fout']
            df_filtered = df[df['Fout'] == closest_Fout]

# Remove duplicate Fout values from the filtered DataFrame
df_filtered = df_filtered.drop_duplicates(subset=["Fout"])


# Sort the filtered DataFrame by Fout
df_filtered = df_filtered.sort_values("Fout")

# Compute the average step size from one Fout value to the next
step_sizes = df_filtered["Fout"].diff().mean()

# Print the average step size
print(f"Average step size: {step_sizes}")

# Print the filtered DataFrame with an incrementing index
print(df_filtered.reset_index(drop=True).to_string(index=True))
