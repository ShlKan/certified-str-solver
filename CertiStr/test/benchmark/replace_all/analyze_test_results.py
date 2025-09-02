#!/usr/bin/env python3
"""
Analyze test result files to count timeouts and compute average execution time.
This script processes test result files and extracts:
1. Number of TIMEOUT tests
2. Average execution time of non-timeout tests
"""

import re
import sys
from typing import List, Tuple

def analyze_test_file(filename: str) -> Tuple[int, float, int]:
    """
    Analyze a test result file.
    
    Args:
        filename: Path to the test result file
        
    Returns:
        Tuple of (timeout_count, average_time_ms, total_non_timeout_tests)
    """
    timeout_count = 0
    execution_times = []
    
    try:
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            
        # Find all TIMEOUT occurrences
        timeout_matches = re.findall(r'TIMEOUT.*?limit exceeded', content, re.IGNORECASE)
        timeout_count = len(timeout_matches)
        
        # Find all execution times (lines ending with "ms")
        time_matches = re.findall(r'(\d+)ms$', content, re.MULTILINE)
        execution_times = [int(time) for time in time_matches]
        
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return 0, 0.0, 0
    except Exception as e:
        print(f"Error reading file '{filename}': {e}")
        return 0, 0.0, 0
    
    # Calculate average execution time
    if execution_times:
        average_time = sum(execution_times) / len(execution_times)
    else:
        average_time = 0.0
    
    return timeout_count, average_time, len(execution_times)

def main():
    """Main function to analyze test result files."""
    files_to_analyze = ['test2.result', 'test3.result']
    
    total_timeouts = 0
    all_execution_times = []
    
    print("Test Result Analysis")
    print("=" * 50)
    
    for filename in files_to_analyze:
        print(f"\nAnalyzing {filename}...")
        timeout_count, avg_time, test_count = analyze_test_file(filename)
        
        print(f"  TIMEOUT tests: {timeout_count}")
        print(f"  Non-timeout tests: {test_count}")
        if test_count > 0:
            print(f"  Average execution time: {avg_time:.2f} ms")
        else:
            print(f"  Average execution time: N/A (no valid tests)")
        
        total_timeouts += timeout_count
        
        # Re-read file to get individual execution times for overall average
        try:
            with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            time_matches = re.findall(r'(\d+)ms$', content, re.MULTILINE)
            all_execution_times.extend([int(time) for time in time_matches])
        except:
            pass
    
    print(f"\n" + "=" * 50)
    print("OVERALL SUMMARY:")
    print(f"Total TIMEOUT tests: {total_timeouts}")
    print(f"Total non-timeout tests: {len(all_execution_times)}")
    
    if all_execution_times:
        overall_avg = sum(all_execution_times) / len(all_execution_times)
        print(f"Overall average execution time: {overall_avg:.2f} ms")
        print(f"Overall average execution time: {overall_avg/1000:.3f} seconds")
        
        # Additional statistics
        min_time = min(all_execution_times)
        max_time = max(all_execution_times)
        print(f"Minimum execution time: {min_time} ms")
        print(f"Maximum execution time: {max_time} ms")
    else:
        print("Overall average execution time: N/A (no valid tests)")

if __name__ == "__main__":
    main()