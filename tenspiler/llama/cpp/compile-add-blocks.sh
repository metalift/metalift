#!/usr/bin/env bash

# Compiles benchmark and runs switch converter and instruction namer on it

include_path="/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/include"

process_file() {
    file="$1"
    ext="${file##*.}"
    dir=$(dirname "$file")
    filename=$(basename "$file")
    base="${filename%.*}"
    clang_out="$dir/$base.ll"

    echo "output to:" $clang_out

    if [[ $file == *.c ]]
    then
      clang -O0 -I "$include_path" -I../../headers -c -emit-llvm -fno-discard-value-names -S "$file" -o "$clang_out"
    else
      clang++ -stdlib=libc++ -O0 -I "$include_path" -I../../headers -c -emit-llvm -fno-discard-value-names -S "$file" -o "$clang_out"
    fi

    opt -load ../../../llvm-pass/build/addEmptyBlocks/libAddEmptyBlocksPass.so -addEmptyBlock -lowerinvoke --unreachableblockelim -instnamer -S "$clang_out" > "$dir/tmp.ll"

    mv "$dir/tmp.ll" "$clang_out"

    loops_out="$dir/$base.loops"
    echo "output loops info to:" $loops_out
    opt -analyze -loops "$clang_out" > "$loops_out"
}

if [ "$1" == "ALL" ]; then
    # Find both .c and .cc files
    files=$(find . -type f \( -name '*.cc' -o -name '*.c' \))
    for file in $files; do
        process_file "$file"
    done
else
    process_file "$1"
fi
