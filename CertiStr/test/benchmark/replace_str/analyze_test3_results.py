#!/usr/bin/env python3
"""
Analyze test3.result to count timeouts and compute average execution time.

This script:
1. Counts the number of timeout tests
2. Excludes timeout tests and computes average execution time for the rest
"""

import re
import sys

def analyze_test_results(filename):
    """
    Analyze test results from the given file.
    
    Returns:
        tuple: (timeout_count, average_time, total_tests, valid_tests)
    """
    timeout_count = 0
    execution_times = []
    total_tests = 0
    
    try:
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return None, None, None, None
    except Exception as e:
        print(f"Error reading file: {e}")
        return None, None, None, None
    
    # Split content into test blocks
    # Each test starts with "Test (./filename.smt2):"
    test_blocks = re.split(r'Test \([^)]+\.smt2\):', content)[1:]  # Skip first empty element
    
    total_tests = len(test_blocks)
    
    for block in test_blocks:
        # Check if this test timed out
        if 'TIMEOUT' in block:
            timeout_count += 1
        else:
            # Look for execution time at the end of the block
            # The pattern seems to be a standalone number followed by "ms" at the end
            lines = block.strip().split('\n')
            for line in reversed(lines):
                line = line.strip()
                # Look for standalone time in milliseconds
                time_match = re.match(r'^(\d+)ms$', line)
                if time_match:
                    execution_time = int(time_match.group(1))
                    execution_times.append(execution_time)
                    break
    
    valid_tests = len(execution_times)
    
    if execution_times:
        average_time = sum(execution_times) / len(execution_times)
    else:
        average_time = 0
    
    return timeout_count, average_time, total_tests, valid_tests

def main():
    filename = 'test3.result'
    
    print("Analyzing test3.result...")
    print("=" * 50)
    
    timeout_count, average_time, total_tests, valid_tests = analyze_test_results(filename)
    
    if timeout_count is None:
        sys.exit(1)
    
    print(f"Total tests found: {total_tests}")
    print(f"Timeout tests: {timeout_count}")
    print(f"Valid tests (with execution time): {valid_tests}")
    print(f"Tests excluded from average: {total_tests - valid_tests}")
    print()
    
    if valid_tests > 0:
        print(f"Average execution time (excluding timeouts): {average_time:.2f} ms")
        print(f"Average execution time (excluding timeouts): {average_time/1000:.3f} seconds")
    else:
        print("No valid execution times found.")
    
    print()
    print("Summary:")
    print(f"- Timeout rate: {(timeout_count/total_tests)*100:.1f}% ({timeout_count}/{total_tests})")
    if valid_tests > 0:
        print(f"- Average time for successful tests: {average_time:.2f} ms")

if __name__ == "__main__":
    main()