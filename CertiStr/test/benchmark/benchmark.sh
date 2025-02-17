#!/bin/bash

for test in ./*.smt2; do
    echo "Test ($test):"
    result=$(CertiStr $test)
    echo "$result"
done