#!/bin/bash

# Function to count lines ignoring comments
count_lines() {
    local file="$1"
    local lines=0

    # Check if file exists
    if [ -f "$file" ]; then
        # Loop through each line in the file
        while IFS= read -r line; do
            # Remove leading and trailing whitespace
            line=$(echo "$line" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
            # Ignore empty lines and single-line comments
            if [[ ! "$line" =~ ^\s*$ && ! "$line" =~ ^// ]]; then
                # Remove inline comments and count non-empty lines
                line=$(echo "$line" | sed 's/\/\/.*//')
                if [ -n "$line" ]; then
                    ((lines++))
                fi
            fi
        done < "$file"
    else
        echo "File not found: $file"
    fi

    echo "$lines"
}

# Directory containing C++ files
directory=$1

# Sum of lines excluding comments
total_lines=0

total_files=0

# Find all C++ files recursively in the directory
cpp_files=$(find "$directory" -type f \( -name "*.cc" -o -name "*.h" \))

# Iterate over each C++ file found
for file in $cpp_files; do
    lines=$(count_lines "$file")
    total_lines=$((total_lines + lines))
    total_files=$((total_files + 1))
done

echo "Total lines of code excluding comments: $total_lines"
echo "Total number of files: $total_files"
