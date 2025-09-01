#!/usr/bin/env python3

import re
import sys

def parse_time(time_str):
    """Parse time string like '0m0.008s' or '1m22.497s' to seconds"""
    match = re.match(r'(\d+)m(\d+\.\d+)s', time_str)
    if match:
        minutes = int(match.group(1))
        seconds = float(match.group(2))
        return minutes * 60 + seconds
    return None

def analyze_results(filename):
    """Analyze test results from the given file"""
    timeout_count = 0
    total_tests = 0
    execution_times = []
    timeouts = []
    
    with open(filename, 'r') as f:
        content = f.read()
    
    # Split by test entries
    test_blocks = re.split(r'Test \([^)]+\):', content)[1:]  # Skip first empty split
    
    for block in test_blocks:
        total_tests += 1
        lines = block.strip().split('\n')
        
        # Check for timeout
        timeout_found = False
        real_time = None
        
        for line in lines:
            if 'TIMEOUT' in line:
                timeout_found = True
                timeouts.append(line.strip())
                break
            elif line.startswith('real'):
                # Extract time from real time line
                time_match = re.search(r'real\s+(.+)', line)
                if time_match:
                    time_str = time_match.group(1)
                    real_time = parse_time(time_str)
        
        if timeout_found:
            timeout_count += 1
        elif real_time is not None:
            execution_times.append(real_time)
    
    # Calculate statistics
    if execution_times:
        avg_time = sum(execution_times) / len(execution_times)
        min_time = min(execution_times)
        max_time = max(execution_times)
        median_time = sorted(execution_times)[len(execution_times) // 2]
    else:
        avg_time = min_time = max_time = median_time = 0
    
    # Print results
    print("=" * 50)
    print("EXPERIMENTAL RESULTS ANALYSIS")
    print("=" * 50)
    print(f"Total tests: {total_tests}")
    print(f"Timeouts: {timeout_count}")
    print(f"Successful tests: {len(execution_times)}")
    print()
    
    if timeouts:
        print("Timeout details:")
        for i, timeout in enumerate(timeouts, 1):
            print(f"  {i}. {timeout}")
        print()
    
    if execution_times:
        print("Execution time statistics (excluding timeouts):")
        print(f"  Average execution time: {avg_time:.6f} seconds")
        print(f"  Minimum execution time: {min_time:.6f} seconds") 
        print(f"  Maximum execution time: {max_time:.6f} seconds")
        print(f"  Median execution time: {median_time:.6f} seconds")
        print(f"  Total execution time: {sum(execution_times):.6f} seconds")
        print()
        
        # Show distribution
        print("Time distribution:")
        ranges = [(0, 0.1), (0.1, 1), (1, 10), (10, 60), (60, float('inf'))]
        for min_t, max_t in ranges:
            count = len([t for t in execution_times if min_t <= t < max_t])
            if max_t == float('inf'):
                print(f"  >= {min_t}s: {count} tests")
            else:
                print(f"  {min_t}-{max_t}s: {count} tests")
    
    return {
        'total_tests': total_tests,
        'timeout_count': timeout_count,
        'successful_tests': len(execution_times),
        'avg_time': avg_time if execution_times else 0,
        'execution_times': execution_times
    }

if __name__ == "__main__":
    filename = "test1.result"
    if len(sys.argv) > 1:
        filename = sys.argv[1]
    
    try:
        results = analyze_results(filename)
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error analyzing results: {e}")
        sys.exit(1)