#!/usr/bin/env python3
"""
Analyze test results from test2.result file.
Count timeouts and calculate average execution time for non-timeout tests.
"""

import re
import sys
import subprocess

def parse_test_results(file_path):
    """
    Parse test results file and extract timing information.
    Handles binary files by using strings command first.
    
    Returns:
        tuple: (timeout_count, non_timeout_times, total_tests)
    """
    timeout_count = 0
    non_timeout_times = []
    total_tests = 0
    
    # Use strings command to extract readable text from potentially binary file
    try:
        result = subprocess.run(['strings', file_path], capture_output=True, text=True)
        if result.returncode != 0:
            # Fall back to regular file reading
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
        else:
            content = result.stdout
    except:
        # Final fallback to regular file reading
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    
    # Split by test cases - look for "Test (" pattern
    test_blocks = re.split(r'Test \([^)]+\):', content)[1:]  # Skip first empty element
    
    for block in test_blocks:
        total_tests += 1
        
        # Check if this test timed out
        if 'TIMEOUT' in block:
            timeout_count += 1
        else:
            # Extract real time - look for "real\t<time>" pattern
            time_match = re.search(r'real\s+(\d+)m([\d.]+)s', block)
            if time_match:
                minutes = int(time_match.group(1))
                seconds = float(time_match.group(2))
                total_seconds = minutes * 60 + seconds
                non_timeout_times.append(total_seconds)
    
    return timeout_count, non_timeout_times, total_tests

def main():
    file_path = 'test2.result'
    
    try:
        timeout_count, non_timeout_times, total_tests = parse_test_results(file_path)
        
        print("=== Test Results Analysis ===")
        print(f"Total tests: {total_tests}")
        print(f"Timeout tests: {timeout_count}")
        print(f"Non-timeout tests: {len(non_timeout_times)}")
        
        if non_timeout_times:
            avg_time = sum(non_timeout_times) / len(non_timeout_times)
            min_time = min(non_timeout_times)
            max_time = max(non_timeout_times)
            
            print(f"\n=== Execution Time Statistics (Non-timeout tests) ===")
            print(f"Average execution time: {avg_time:.3f} seconds")
            print(f"Minimum execution time: {min_time:.3f} seconds")
            print(f"Maximum execution time: {max_time:.3f} seconds")
            
            # Additional statistics
            non_timeout_times.sort()
            median_time = non_timeout_times[len(non_timeout_times) // 2]
            print(f"Median execution time: {median_time:.3f} seconds")
            
            # Show timeout percentage
            timeout_percentage = (timeout_count / total_tests) * 100
            print(f"\n=== Summary ===")
            print(f"Timeout rate: {timeout_percentage:.1f}%")
            
        else:
            print("No non-timeout tests found!")
            
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found!")
        sys.exit(1)
    except Exception as e:
        print(f"Error analyzing file: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()