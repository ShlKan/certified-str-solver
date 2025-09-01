#!/bin/bash

# Script to run ostrich on all .smt2 files and collect timing data
# Usage: ./run_ostrich_benchmark.sh

echo "Running ostrich benchmark on all .smt2 files..."
echo "File,Time(seconds),Result" > ostrich_results.csv

total_time=0
count=0
successful_runs=0

for file in unsolved_pcp_instance_*.smt2; do
    if [ -f "$file" ]; then
        echo "Processing: $file"
        
        # Measure execution time using time command
        start_time=$(date +%s.%N)
        
        # Run ostrich and capture both stdout and return code
        if timeout 60 ostrich "$file" > /dev/null 2>&1; then
            end_time=$(date +%s.%N)
            execution_time=$(echo "$end_time - $start_time" | bc)
            result="completed"
            total_time=$(echo "$total_time + $execution_time" | bc)
            successful_runs=$((successful_runs + 1))
        else
            end_time=$(date +%s.%N)
            execution_time=$(echo "$end_time - $start_time" | bc)
            result="timeout/error"
        fi
        
        # Log to CSV
        echo "$file,$execution_time,$result" >> ostrich_results.csv
        
        count=$((count + 1))
        
        # Progress indicator
        if [ $((count % 50)) -eq 0 ]; then
            echo "Processed $count files..."
        fi
    fi
done

# Calculate and display results
if [ $successful_runs -gt 0 ]; then
    average_time=$(echo "scale=6; $total_time / $successful_runs" | bc)
else
    average_time=0
fi

echo ""
echo "=== Benchmark Results ==="
echo "Total files processed: $count"
echo "Successful runs: $successful_runs"
echo "Failed/timeout runs: $((count - successful_runs))"
echo "Total execution time (successful): ${total_time}s"
echo "Average execution time: ${average_time}s"
echo ""
echo "Detailed results saved to: ostrich_results.csv"