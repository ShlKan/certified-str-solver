#!/bin/bash

for test in ./*.smt2; do
    result=$(CertiStr $test)
    if ( [ $result != 'UNSAT' ])
    then
        echo "Test ($test) Fail:"
        echo $result
        exit
    fi
done

echo 'Success'