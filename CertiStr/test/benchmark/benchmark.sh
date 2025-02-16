#!/bin/bash

for test in ./*.smt2; do
    result=$(CertiStr $test)
    echo "Test ($test): $result"
done