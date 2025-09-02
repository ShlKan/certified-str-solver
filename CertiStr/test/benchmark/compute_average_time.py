#!/usr/bin/env python3
import re
import os

def parse_time_to_seconds(time_str):
    """Convert time format like '0m11.227s' to seconds"""
    match = re.match(r'(\d+)m([\d.]+)s', time_str)
    if match:
        minutes = int(match.group(1))
        seconds = float(match.group(2))
        return minutes * 60 + seconds
    return 0

def extract_real_times(file_path):
    """Extract all 'real' times from a result file"""
    times = []
    try:
        with open(file_path, 'r') as f:
            for line in f:
                if line.startswith('real'):
                    time_part = line.strip().split('\t')[1]  # Split by tab and get time part
                    seconds = parse_time_to_seconds(time_part)
                    times.append(seconds)
    except FileNotFoundError:
        print(f"File not found: {file_path}")
        return []
    return times

def compute_average_time(directory_name, file_path):
    """Compute and display average execution time for a directory"""
    times = extract_real_times(file_path)
    
    if not times:
        print(f"No timing data found in {directory_name}")
        return
    
    average_time = sum(times) / len(times)
    
    print(f"\n{directory_name}:")
    print(f"  Total entries: {len(times)}")
    print(f"  Average execution time: {average_time:.3f} seconds")
    print(f"  Min time: {min(times):.3f} seconds")
    print(f"  Max time: {max(times):.3f} seconds")

def main():
    base_path = "/Users/shuanglong.kan/MyProjects/certified-str-solver/CertiStr/test/benchmark"
    
    file_paths = [
        os.path.join(base_path, "pcp-3-3-random", "test1.result"),
        os.path.join(base_path, "pcp-3-4-hard", "test1.result")
    ]
    
    print("Computing combined average execution time from 'real' time entries:")
    print("=" * 60)
    
    all_times = []
    for file_path in file_paths:
        times = extract_real_times(file_path)
        all_times.extend(times)
    
    if not all_times:
        print("No timing data found")
        return
    
    average_time = sum(all_times) / len(all_times)
    
    print(f"\nCombined results:")
    print(f"  Total entries: {len(all_times)}")
    print(f"  Average execution time: {average_time:.3f} seconds")
    print(f"  Min time: {min(all_times):.3f} seconds")
    print(f"  Max time: {max(all_times):.3f} seconds")

if __name__ == "__main__":
    main()