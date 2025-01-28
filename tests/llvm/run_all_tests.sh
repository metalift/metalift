#!/bin/bash

SEARCH_DIR="tests/llvm"

find "$SEARCH_DIR" -type f -name "*_driver.py" | while read file; do
    echo "Executing $file..."
    python "$file"
    if [ $? -eq 0 ]; then
        echo "$file execution completed successfully."
    else
        echo "Execution of $file failed with status $?."
        exit 1
    fi
done
