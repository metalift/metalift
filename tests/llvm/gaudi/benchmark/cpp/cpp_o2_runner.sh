#!/bin/bash
FLAG="-O2 -fopenmp -mavx512f"
INCLUDE="-I/usr/local/include/opencv4"
LINK="-lstdc++ -lm -lopencv_core  -lopencv_imgcodecs"

g++ $FLAG $INCLUDE  utils.cc darken_blend_8.cc $LINK -o darken_blend_8_O2
./darken_blend_8_O2

g++ $FLAG $INCLUDE  utils.cc multiply_blend_8.cc $LINK -o multiply_blend_8_O2
./multiply_blend_8_O2

g++ $FLAG $INCLUDE  utils.cc linear_burn_8.cc $LINK -o linear_burn_8_O2
./linear_burn_8_O2

g++ $FLAG $INCLUDE  utils.cc color_burn_8.cc $LINK -o color_burn_8_O2
./color_burn_8_O2

g++ $FLAG $INCLUDE  utils.cc lighten_blend_8.cc $LINK -o lighten_blend_8_O2
./lighten_blend_8_O2

g++ $FLAG $INCLUDE  utils.cc screen_blend_8.cc $LINK -o screen_blend_8_O2
./screen_blend_8_O2

g++ $FLAG $INCLUDE  utils.cc linear_dodge_8.cc $LINK -o linear_dodge_8_O2
./linear_dodge_8_O2

g++ $FLAG $INCLUDE  utils.cc color_dodge_8.cc $LINK -o color_dodge_8_O2
./color_dodge_8_O2

g++ $FLAG $INCLUDE  utils.cc overlay_blend_8.cc $LINK -o overlay_blend_8_02
./overlay_blend_8_O2

g++ $FLAG utils.cc normal_blend_8.cc -o normal_blend_8_O2
./normal_blend_8_O2

g++ $FLAG utils.cc normal_blend_f.cc -o normal_blend_f_O2
./normal_blend_f_O2