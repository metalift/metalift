#!/bin/bash

# Array of benchmarks
benchmarks=(
  "dissolve_blend_8"
  "darken_blend_8"
  "multiply_blend_8"
  "linear_burn_8"
  "color_burn_8"
  "lighten_blend_8"
  "screen_blend_8"
  "linear_dodge_8"
  "color_dodge_8"
  "overlay_blend_8"
  "matmul"
  "transformer_part1"
  "transformer_part2"
)

# Iterate over each benchmark and run the command
for benchmark in "${benchmarks[@]}"; do
  python3 -u tenspiler/llm/scripts/run_with_parser_and_fuzzer_feedback.py --benchmark "$benchmark"
done
