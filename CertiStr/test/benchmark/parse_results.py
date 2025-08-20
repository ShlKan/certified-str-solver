#!/usr/bin/env python3
"""
Script to parse test.result files and generate statistics for benchmark categories.
"""

import os
import re
import statistics
from collections import defaultdict

def parse_test_result_file(filepath):
    """Parse a test.result file and extract test data."""
    tests = []
    current_test = {}
    
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        
        # Look for test start pattern
        if line.startswith('Test (') and line.endswith('):'):
            # Extract test filename
            test_match = re.search(r'Test \((.+)\):', line)
            if test_match:
                if current_test:  # Save previous test if exists
                    tests.append(current_test)
                current_test = {'filename': test_match.group(1)}
        
        # Look for timing information
        elif line.startswith('real'):
            time_match = re.search(r'real\s+(\d+)m([\d.]+)s', line)
            if time_match:
                minutes = int(time_match.group(1))
                seconds = float(time_match.group(2))
                total_seconds = minutes * 60 + seconds
                current_test['time'] = total_seconds
        
        # Look for result status
        elif line in ['SAT', 'UNSAT', 'inconclusive']:
            current_test['result'] = line
            
        i += 1
    
    # Don't forget the last test
    if current_test:
        tests.append(current_test)
    
    return tests

def calculate_folder_stats(folder_path):
    """Calculate statistics for a benchmark folder."""
    result_file = os.path.join(folder_path, 'test.result')
    
    if not os.path.exists(result_file):
        print(f"Warning: {result_file} does not exist")
        return None
    
    tests = parse_test_result_file(result_file)
    
    if not tests:
        print(f"Warning: No tests found in {result_file}")
        return None
    
    # Calculate statistics
    times = [test.get('time', 0) for test in tests if 'time' in test]
    results = [test.get('result', 'Unknown') for test in tests if 'result' in test]
    
    stats = {
        'num_tests': len(tests),
        'avg_time': statistics.mean(times) if times else 0,
        'sat_count': results.count('SAT'),
        'unsat_count': results.count('UNSAT'),
        'inconclusive_count': results.count('inconclusive'),
        'unknown_count': results.count('Unknown')
    }
    
    return stats

def main():
    """Main function to process all benchmark folders."""
    benchmark_dir = '/Users/shuanglong.kan/MyProjects/certified-str-solver/CertiStr/test/benchmark'
    
    folders = [
        'pcp-3-3-random',
        'pcp-3-4-hard', 
        'replace_all',
        'replace_re',
        'replace_str',
        'rna-sat',
        'rna-unsat'
    ]
    
    all_stats = {}
    
    # Process individual folders
    for folder in folders:
        folder_path = os.path.join(benchmark_dir, folder)
        stats = calculate_folder_stats(folder_path)
        if stats:
            all_stats[folder] = stats
            print(f"{folder}: {stats}")
    
    # Combine PCP folders
    if 'pcp-3-3-random' in all_stats and 'pcp-3-4-hard' in all_stats:
        pcp_random = all_stats['pcp-3-3-random']
        pcp_hard = all_stats['pcp-3-4-hard']
        
        pcp_combined = {
            'num_tests': pcp_random['num_tests'] + pcp_hard['num_tests'],
            'sat_count': pcp_random['sat_count'] + pcp_hard['sat_count'],
            'unsat_count': pcp_random['unsat_count'] + pcp_hard['unsat_count'],
            'inconclusive_count': pcp_random['inconclusive_count'] + pcp_hard['inconclusive_count'],
            'unknown_count': pcp_random['unknown_count'] + pcp_hard['unknown_count']
        }
        
        # Calculate combined average time (weighted by number of tests)
        total_time_random = pcp_random['avg_time'] * pcp_random['num_tests']
        total_time_hard = pcp_hard['avg_time'] * pcp_hard['num_tests']
        pcp_combined['avg_time'] = (total_time_random + total_time_hard) / pcp_combined['num_tests']
        
        all_stats['pcp-combined'] = pcp_combined
        print(f"pcp-combined: {pcp_combined}")
    
    # Generate LaTeX table
    generate_latex_table(all_stats)

def generate_latex_table(stats_dict):
    """Generate LaTeX table from statistics."""
    latex_content = """\\begin{table}[h]
\\centering
\\caption{Benchmark Test Results Statistics}
\\begin{tabular}{|l|c|c|c|c|c|}
\\hline
\\textbf{Category} & \\textbf{\\# Tests} & \\textbf{Avg Time (s)} & \\textbf{SAT} & \\textbf{UNSAT} & \\textbf{Inconclusive} \\\\
\\hline
"""
    
    # Define the order and display names for categories
    category_order = [
        ('pcp-combined', 'PCP'),
        ('replace_all', 'Replace All'),
        ('replace_re', 'Replace RE'),
        ('replace_str', 'Replace Str'),
        ('rna-sat', 'RNA SAT'),
        ('rna-unsat', 'RNA UNSAT')
    ]
    
    for key, display_name in category_order:
        if key in stats_dict:
            stats = stats_dict[key]
            latex_content += f"{display_name} & {stats['num_tests']} & {stats['avg_time']:.3f} & {stats['sat_count']} & {stats['unsat_count']} & {stats['inconclusive_count']} \\\\\n"
            latex_content += "\\hline\n"
    
    latex_content += """\\end{tabular}
\\label{tab:benchmark_stats}
\\end{table}
"""
    
    print("\n" + "="*50)
    print("LATEX TABLE:")
    print("="*50)
    print(latex_content)
    
    # Also save to file
    with open('/Users/shuanglong.kan/MyProjects/certified-str-solver/CertiStr/test/benchmark/benchmark_stats.tex', 'w') as f:
        f.write(latex_content)
    
    print("LaTeX table saved to: benchmark_stats.tex")

if __name__ == '__main__':
    main()