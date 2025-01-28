
// setup code
#include <stdint.h>
#include <stddef.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#ifndef BAREMETAL
#include <sys/mman.h>
#endif
#include "include/gemmini_testutils.h"

# define LEN 488

unsigned long long start = 0;
unsigned long long end = 0;

float random_float() {
    return (float)(rand()) / (float)(RAND_MAX);
}

uint8_t random_uint8() {
    return (uint8_t)(rand() % 256 - 128);
}

int32_t random_int() {
    return rand();
}


// include statements
#include "include/gemmini_params.h"
#include "include/gemmini.h"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t

void normal_blend_8_gemmini(elem_t base[LEN][LEN], elem_t active[LEN][LEN], elem_t opacity, elem_t out[LEN][LEN]){
    tiled_resadd_auto(LEN, LEN, opacity, (255) - (opacity), 1, active[0], base[0], out[0], false, WS);

}

uint8_t* normal_blend_8_gemmini_glued (uint8_t base[LEN], uint8_t active[LEN], uint8_t opacity){
    static elem_t glued_42[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_42[i][0] = base[i];
    }

    static elem_t glued_43[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_43[i][0] = active[i];
    }

    static uint8_t out [LEN][LEN];
    normal_blend_8_gemmini(glued_42, glued_43, opacity, out);
    static uint8_t out_postprocess [LEN];


    for (int i = 0; i < LEN; i++) {
        out_postprocess[i] = out[i][0];
    }

    return out_postprocess;
}


int main() {
#ifndef BAREMETAL
    if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {
      perror("mlockall failed");
      exit(1);
    }
#endif

    gemmini_flush(0);
    unsigned long long totalTime = 0;

    static uint8_t input[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        input[i] = random_uint8();
    }

    static uint8_t input2[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        input2[i] = random_uint8();
    }
    uint8_t opacity = random_uint8();
    static uint8_t out [LEN][LEN];
    start = read_cycles();
    normal_blend_8_gemmini(input, input2, opacity, out);
    end = read_cycles();
    totalTime += end - start;

    printf("normal_blend_8_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
