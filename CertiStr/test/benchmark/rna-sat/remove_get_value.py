import os
import glob

for file in glob.glob("*.smt2"):
    with open(file, 'r') as f:
        lines = f.readlines()
    
    filtered_lines = [line for line in lines if 'get-value' not in line]
    
    with open(file, 'w') as f:
        f.writelines(filtered_lines)
    
    print(f"Processed: {file}")

print("Done!")