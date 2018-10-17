#!/bin/bash
test=$1
ocamlc -I hw -I test hw/hw1.mli hw/hw1_reduction.mli hw/hw2_unify.mli hw/hw2_inference.mli test/test.mli
case "$test" in
"1")
    ocamlc -I hw -I test unix.cma hw/hw1.ml test/test.ml test/test_hw1.ml -o t ; ./t;;
"2")
    ocamlc -I hw -I test unix.cma hw/hw1.ml hw/hw1_reduction.ml test/test.ml test/test_hw1_reduction.ml -o t ; ./t;;
"3")
    ocamlc -I hw -I test unix.cma test/test.ml hw/hw2_unify.ml test/test_hw2_unify.ml -o t ; ./t;;
"4")
    ocamlc -I hw -I test unix.cma test/test.ml hw/hw1_reduction.ml hw/hw2_unify.ml hw/hw2_inference.ml test/test_hw2_inference.ml -o t ; ./t;;
esac