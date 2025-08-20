#!/bin/bash

for test in ./*.smt2; do
    echo "Test ($test):"
    { time result=$(dune exec CertiStr -- $test); } 2>&1
    echo "$result"
done
