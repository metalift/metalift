#!/bin/bash

# Define an array of benchmarks
benchmarks=(
    "normal_blend_f"
    "normal_blend_8"
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
)

# Loop through each benchmark
for benchmark in "${benchmarks[@]}"; do
    echo "Running benchmark: $benchmark"
    python3 scripts/gemini_benchmarks.py --filename "$benchmark" --source-code "benchmarks/dexter/source/${benchmark}.cc" --dsl-code python_dsl.py
    # --n-choices 1
    echo "Benchmark $benchmark complete."
    echo
done

echo "All benchmarks completed."
