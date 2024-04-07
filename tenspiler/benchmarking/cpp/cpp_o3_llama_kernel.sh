#!/bin/bash
cd benchmarks

FLAG="-O3 -fopenmp -mavx512f"
INCLUDE="-I/usr/include/opencv"
LINK="-lopencv_highgui -lopencv_core -lopencv_imgproc -lhdf5_cpp -lhdf5 "

h5c++ $FLAG $INCLUDE  utils.cc matmul_kernel.cc $LINK -o matmul_kernel_O3
printf "%-50s\n" "matmul_kernel_O3"
./matmul_kernel_O3
rm matmul_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc transformer_part1_kernel.cc $LINK -o transformer_part1_kernel_O3
printf "%-50s\n" "transformer_part1_kernel_O3"
./transformer_part1_kernel_O3
rm transformer_part1_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc transformer_part2_kernel.cc $LINK -o transformer_part2_kernel_O3
printf "%-50s\n" "transformer_part2_kernel_O3"
./transformer_part2_kernel_O3
rm transformer_part2_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc transformer_part3_kernel.cc $LINK -o transformer_part3_kernel_O3
printf "%-50s\n" "transformer_part3_kernel_O3"
./transformer_part3_kernel_O3
rm transformer_part3_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc transformer_part4_kernel.cc $LINK -o transformer_part4_kernel_O3
printf "%-50s\n" "transformer_part4_kernel_O3"
./transformer_part4_kernel_O3
rm transformer_part4_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc rmsnorm_part1_kernel.cc $LINK -o rmsnorm_part1_kernel_O3
printf "%-50s\n" "rmsnorm_part1_kernel_O3"
./rmsnorm_part1_kernel_O3
rm rmsnorm_part1_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc rmsnorm_part2_kernel.cc $LINK -o rmsnorm_part2_kernel_O3
printf "%-50s\n" "rmsnorm_part2_kernel_O3"
./rmsnorm_part2_kernel_O3
rm rmsnorm_part2_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc softmax_part1_kernel.cc $LINK -o softmax_part1_kernel_O3
printf "%-50s\n" "softmax_part1_kernel_O3"
./softmax_part1_kernel_O3
rm softmax_part1_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc softmax_part2_kernel.cc $LINK -o softmax_part2_kernel_O3
printf "%-50s\n" "softmax_part2_kernel_O3"
./softmax_part2_kernel_O3
rm softmax_part2_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc softmax_part3_kernel.cc $LINK -o softmax_part3_kernel_O3
printf "%-50s\n" "softmax_part3_kernel_O3"
./softmax_part3_kernel_O3
rm softmax_part3_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc softmax_part4_kernel.cc $LINK -o softmax_part4_kernel_O3
printf "%-50s\n" "softmax_part4_kernel_O3"
./softmax_part4_kernel_O3
rm softmax_part4_kernel_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"
