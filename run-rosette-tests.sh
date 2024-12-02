#!/bin/bash

# TODO: add these back to tests after adding support for them
# "tests.llvm.list1"
# "tests.llvm.list1_fns"
# "tests.llvm.struct1"

tests=(
# "tests.python.list1_driver"
# "tests.python.list1_fns_driver"
# "tests.python.list_abs_sum_driver"
  "tests.llvm.vector1_driver"
  "tests.llvm.count_driver"
  "tests.llvm.uninterp_driver"
  "tests.python.count_driver"
  "tests.python.uninterp_driver"
)

for test in ${tests[*]}; do
  printf "\n\nrunning %s\n" "$test"
  python -m $test
done
