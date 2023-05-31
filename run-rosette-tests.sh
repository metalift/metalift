#!/bin/bash

tests=(
"tests.llvm.count"
"tests.llvm.list1"
"tests.llvm.list1_fns"
"tests.llvm.uninterp"
"tests.llvm.struct1"
)

for test in ${tests[*]}; do
  printf "\n\nrunning %s\n" "$test"
  python -m $test
done

