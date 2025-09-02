#!/bin/bash

for test in ./*.smt2; do
    echo "Test ($test):"
    { time result=$(ostrich -portfolio=strings $test); } 2>&1 #dune exec CertiStr -- 
    echo "$result"
done
