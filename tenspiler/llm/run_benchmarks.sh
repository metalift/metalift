#!/bin/bash

# Parse additional command-line options
while [[ $# -gt 0 ]]; do
    case "$1" in
        --benchmark-suite)
            shift
            benchmark_suite=$1
            ;;
        --n-choices)
            shift
            n_choices=$1
            ;;
        --backend)
            shift
            backend=$1
            ;;
        --inv-ps)
            shift
            inv_ps=$1
            ;;
        *)
            echo "Invalid option: $1"
            exit 1
            ;;
    esac
    shift
done


if [ "$benchmark_suite" == "dexter" ]; then
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
elif [ "$benchmark_suite" == "llama" ]; then
    benchmarks=(
        "softmax_part1"
        "softmax_part2"
        "softmax_part3"
        "softmax_part4"
        "rmsnorm_part1"
        "rmsnorm_part2"
        "matmul"
        "transformer_part1"
        "transformer_part2"
        "transformer_part3"
        "transformer_part4"
    )
else
    echo "Invalid benchmark suite specified. Please choose 'dexter' or 'llama'."
    exit 1
fi

# Loop through each benchmark
for benchmark in "${benchmarks[@]}"; do
    echo "Running benchmark: $benchmark"

    source_file=$(find "benchmarks/${benchmark_suite}/source" -type f -name "${benchmark}.cc" -print -quit)

    if [ "$backend" == "gemini" ]; then
        python3 scripts/gemini_ps.py \
            --filename "$benchmark" \
            --source-code "${source_file}" \
            --dsl-code python_dsl.py
    elif [ "$backend" == "openai" ]; then
        if [ "$inv_ps" == "inv" ]; then
            script_to_run="openai_inv.py"
        else
            script_to_run="openai_ps.py"
        fi
        python3 scripts/$script_to_run \
            --filename "$benchmark" \
            --source-code "${source_file}" \
            --dsl-code python_dsl.py \
            --n-choices=${n_choices}
    else
        echo "Invalid backend specified. Please choose 'gemini' or 'openai'."
        exit 1
    fi
    echo "Benchmark $benchmark complete."
    echo
done

echo "All benchmarks completed."
