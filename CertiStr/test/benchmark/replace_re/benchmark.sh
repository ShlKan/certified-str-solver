#!/bin/bash

for test in ./*.smt2; do
    echo "Test ($test):"
    result=$(dune exec CertiStr -- $test);
    echo "$result"
done
