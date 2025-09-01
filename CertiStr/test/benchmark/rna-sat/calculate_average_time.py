#!/usr/bin/env python3
import re

def parse_time(time_str):
    """Parse time string like '0m14.643s' to seconds"""
    match = re.match(r'(\d+)m([\d.]+)s', time_str)
    if match:
        minutes = int(match.group(1))
        seconds = float(match.group(2))
        return minutes * 60 + seconds
    return 0

def calculate_average_real_time(filename):
    """Calculate average real execution time from test result file"""
    real_times = []
    
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('real'):
                # Extract time part after 'real\t'
                time_part = line.split('\t')[1]
                seconds = parse_time(time_part)
                if seconds > 0:
                    real_times.append(seconds)
    
    if not real_times:
        print("No real time entries found")
        return
    
    average_time = sum(real_times) / len(real_times)
    
    print(f"Total test cases: {len(real_times)}")
    print(f"Average real time: {average_time:.3f} seconds")
    print(f"Average real time: {int(average_time // 60)}m{average_time % 60:.3f}s")
    print(f"Min time: {min(real_times):.3f}s")
    print(f"Max time: {max(real_times):.3f}s")

if __name__ == "__main__":
    calculate_average_real_time("test1.result")