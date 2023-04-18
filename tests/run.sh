#!/usr/bin/env bash

file="$1"
ext="${file##*.}"
clang_out=${file/.$ext/.exe}

include_path="/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/include"

clang++ -std=c++17 -O0 -I $include_path -I../headers $file -o $clang_out
