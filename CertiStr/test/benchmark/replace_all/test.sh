#!/bin/bash

for test in ./*.smt2; do
    echo "Test ($test):"
    { time result=$(timeout 3600 ostrich -portfolio=strings $test); } 2>&1 #dune exec CertiStr -- --left-most
    if [ $? -eq 124 ]; then
        echo "TIMEOUT (1 hour limit exceeded)"
    else
        echo "$result"
    fi
done
