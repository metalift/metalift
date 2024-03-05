#!/bin/bash

cd benchmarks

FLAG="-O3 -fopenmp -mavx512f"
INCLUDE="-I/usr/include/opencv"
LINK="-lopencv_highgui -lopencv_core -lopencv_imgproc -lhdf5_cpp -lhdf5 "

h5c++ $FLAG $INCLUDE  utils.cc dissolve_blend_8.cc $LINK -o dissolve_blend_8_O3
printf "%-50s\n" "dissolve_blend_8_O3"
./dissolve_blend_8_O3
rm dissolve_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc darken_blend_8.cc $LINK -o darken_blend_8_O3
printf "%-50s\n" "darken_blend_8_O3"
./darken_blend_8_O3
rm darken_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc multiply_blend_8.cc $LINK -o multiply_blend_8_O3
printf "%-50s\n" "multiply_blend_8_O3"
./multiply_blend_8_O3
rm multiply_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc linear_burn_8.cc $LINK -o linear_burn_8_O3
printf "%-50s\n" "linear_burn_8_O3"
./linear_burn_8_O3
rm linear_burn_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc color_burn_8.cc $LINK -o color_burn_8_O3
printf "%-50s\n" "color_burn_8_O3"
./color_burn_8_O3
rm color_burn_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc lighten_blend_8.cc $LINK -o lighten_blend_8_O3
printf "%-50s\n" "lighten_blend_8_O3"
./lighten_blend_8_O3
rm lighten_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc screen_blend_8.cc $LINK -o screen_blend_8_O3
printf "%-50s\n" "screen_blend_8_O3"
./screen_blend_8_O3
rm screen_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc linear_dodge_8.cc $LINK -o linear_dodge_8_O3
printf "%-50s\n" "linear_dodge_8_O3"
./linear_dodge_8_O3
rm linear_dodge_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc color_dodge_8.cc $LINK -o color_dodge_8_O3
printf "%-50s\n" "color_dodge_8_O3"
./color_dodge_8_O3
rm color_dodge_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE  utils.cc overlay_blend_8.cc $LINK -o overlay_blend_8_O3
printf "%-50s\n" "overlay_blend_8_O3"
./overlay_blend_8_O3
rm overlay_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE utils.cc normal_blend_8.cc $LINK -o normal_blend_8_O3
printf "%-50s\n" "normal_blend_8_O3"
./normal_blend_8_O3
rm normal_blend_8_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"

h5c++ $FLAG $INCLUDE utils.cc normal_blend_f.cc $LINK -o normal_blend_f_O3
printf "%-50s\n" "normal_blend_f_O3"
./normal_blend_f_O3
rm normal_blend_f_O3
printf "=%.0s"  $(seq 1 63)
printf "\n"
