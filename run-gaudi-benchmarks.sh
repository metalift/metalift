#!/bin/bash

tests=(
"tests.llvm.gaudi.darken_blend_8_driver"
"tests.llvm.gaudi.multiply_blend_8_driver"
"tests.llvm.gaudi.linear_burn_8_driver"
"tests.llvm.gaudi.color_burn_8_driver"
"tests.llvm.gaudi.lighten_blend_8_driver"
"tests.llvm.gaudi.screen_blend_8_driver"
"tests.llvm.gaudi.linear_dodge_8_driver"
"tests.llvm.gaudi.color_dodge_8_driver"
"tests.llvm.gaudi.overlay_blend_8_driver"
)

for test in ${tests[*]}; do
  printf "\n\nrunning %s\n" "$test"
  python -m $test
done

