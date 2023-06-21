#!/bin/bash

tests=(
"tests.llvm.fma_dsl"
"tests.llvm.ite1"
"tests.llvm.ite3"
"tests.llvm.set1"
"tests.llvm.tuples1"
"tests.llvm.tuples2"
"tests.llvm.tuples3"
"tests.llvm.while3"
"tests.llvm.while4"
"tests.llvm.no_loop_matmul"
"tests.python.fma1-driver"
"tests.python.fma2-driver"
"tests.python.ite1-driver"
"tests.python.ite2-driver"
"tests.python.ite3-driver"
"tests.python.while1-driver"
)

for test in ${tests[*]}; do
  printf "\n\nrunning %s\n" "$test"
  python -m $test
done

