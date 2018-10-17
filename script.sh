#!/bin/bash
test=$1
ocamlc -I hw -I test hw/hw1.mli hw/hw1_reduction.mli hw/hw2_unify.mli test/test.mli
if [[ "$test" -eq "1" ]]
then
    ocamlc -I hw -I test unix.cma hw/hw1.ml test/test.ml test/test_hw1.ml -o t ; ./t
else 
    if [[ "$test" -eq "2" ]]
    then
        ocamlc -I hw -I test unix.cma hw/hw1.ml hw/hw1_reduction.ml test/test.ml test/test_hw1_reduction.ml -o t ; ./t
    else
        ocamlc -I hw -I test  unix.cma test/test.ml hw/hw2_unify.ml test/test_hw2_unify.ml -o t ; ./t
    fi
fi