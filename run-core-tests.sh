#!/bin/bash

tests=(
"tests.llvm.fma1_driver"
"tests.llvm.ite1_driver"
"tests.llvm.ite3_driver"
"tests.llvm.set1_driver"
"tests.llvm.tuples1_driver"
"tests.llvm.tuples2_driver"
"tests.llvm.tuples3_driver"
"tests.llvm.while3_driver"
"tests.llvm.while4_driver"
"tests.llvm.no_loop_matmul_driver"
"tests.python.fma1_driver"
"tests.python.fma2_driver"
"tests.python.ite1_driver"
"tests.python.ite2_driver"
"tests.python.ite3_driver"
"tests.python.set1_driver"
"tests.python.while1_driver"
"tests.python.while3_driver"
"tests.python.while4_driver"
"tests.python.tuples1_driver"
"tests.python.tuples2_driver"
"tests.python.tuples3_driver"
"tests.python.no_loop_matmul_driver"
)

for test in ${tests[*]}; do
  printf "\n\nrunning %s\n" "$test"
  python -m $test
done
