#!/bin/bash

# Directory where racket files are located
base_dir="tenspiler/c2taco/holing/racket/"

# Directory to log timings
log_dir="timings/"

# Directory to copy racket files before running
copy_dir="./synthesisLogs/"

# Create log directory if it doesn't exist
mkdir -p "$log_dir"

# Create copy directory if it doesn't exist
mkdir -p "$copy_dir"

# Find all directories under base_dir
directories=$(find "$base_dir" -type d)

# Iterate over each directory
for dir in $directories; do
    # Find all racket files in the current directory
    racket_files=$(find "$dir" -maxdepth 1 -type f -name "*.rkt")

    # Iterate over each racket file
    for file in $racket_files; do
        # Get filename without directory path
        filename=$(basename "$file")

        # Copy the racket file to copy_dir
        cp "$file" "$copy_dir"

        # Run time command on racket file and log timing
        echo "Running time on $filename in directory $dir..."
        # cd "$copy_dir" || exit 1
        { time racket "./synthesisLogs/$filename"; } 2>&1 | grep real | awk '{print $2}' >> "${log_dir}/${filename}_timing.log"
        # cd - || exit 1
    done
done
