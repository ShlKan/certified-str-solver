#!/bin/bash

# Corrected script to run ostrich on all .smt2 files and collect timing data
# Usage: ./run_ostrich_corrected.sh

echo "Running ostrich benchmark on all .smt2 files..."
echo "File,Time(seconds),Result,Output" > ostrich_corrected_results.csv

total_time=0
count=0
successful_runs=0

for file in unsolved_pcp_instance_*.smt2; do
    if [ -f "$file" ]; then
        echo "Processing: $file"
        
        # Measure execution time using time command
        start_time=$(date +%s.%N)
        
        # Run ostrich and capture both stdout and return code
        output=$(timeout 120 ostrich "$file" 2>&1)
        exit_code=$?
        
        end_time=$(date +%s.%N)
        execution_time=$(echo "$end_time - $start_time" | bc)
        
        if [ $exit_code -eq 0 ]; then
            result="completed"
            # Extract result from output (sat/unsat/unknown)
            solver_result=$(echo "$output" | head -1)
            total_time=$(echo "$total_time + $execution_time" | bc)
            successful_runs=$((successful_runs + 1))
        elif [ $exit_code -eq 124 ]; then
            result="timeout"
            solver_result="timeout"
        else
            result="error"
            solver_result="error"
        fi
        
        # Log to CSV (escape commas in output)
        clean_output=$(echo "$solver_result" | tr ',' ';')
        echo "$file,$execution_time,$result,$clean_output" >> ostrich_corrected_results.csv
        
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
echo "=== Corrected Benchmark Results ==="
echo "Total files processed: $count"
echo "Successful runs: $successful_runs"
echo "Failed/timeout runs: $((count - successful_runs))"
echo "Total execution time (successful): ${total_time}s"
echo "Average execution time: ${average_time}s"
echo ""
echo "Detailed results saved to: ostrich_corrected_results.csv"