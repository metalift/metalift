#!/bin/bash

# Check if the folder path is provided as an argument
if [ $# -eq 0 ]; then
    echo "Usage: $0 <folder_path>"
    exit 1
fi

# Get the folder path from the command line argument
folder_path="$1"

# Ensure the folder exists
if [ ! -d "$folder_path" ]; then
    echo "Error: The specified folder does not exist."
    exit 1
fi

# Loop through each .rkt file in the folder
for file in "$folder_path"/*.rkt; do
    # Exclude utils.rkt and bounded.rkt
    if [ "$(basename "$file")" != "utils.rkt" ] && [ "$(basename "$file")" != "bounded.rkt" ]; then
        echo "Running $file..."

        # Measure the time taken to execute the racket file
        start_time=$(date +%s)
        timeout 1h racket "$file"
        exit_status=$?
        end_time=$(date +%s)

        if [ $exit_status -eq 124 ]; then
            echo "Timeout reached for $file."
        else
            elapsed_time=$((end_time - start_time))
            echo "Time taken: ${elapsed_time} seconds for $file."
        fi

        echo
    fi
done
