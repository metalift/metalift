
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

# define LEN 676

uint64_t start = 0;
uint64_t end = 0;

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

void rmsnorm_part1_gemmini(elem_t input[LEN][LEN], elem_t weight[LEN][LEN], elem_t* out){
    static elem_t temp0[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
     	 temp0[i][0] = input[i][0] * input[i][0];
     }
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1);
    *out = *out * LEN * LEN;

}

float rmsnorm_part1_gemmini_glued (float input[LEN], float weight[LEN]){
    static elem_t glued_47[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_47[i][0] = input[i];
    }

    static elem_t glued_48[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_48[i][0] = weight[i];
    }

    elem_t out;
    rmsnorm_part1_gemmini(glued_47, glued_48, &out);

    return out;
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

    static float w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w[i][0] = random_float();
    }
    static float input[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        input[i][0] = random_float();
    }
    elem_t out;
    start = read_cycles();
    rmsnorm_part1_gemmini(input, w, &out);
    end = read_cycles();

    totalTime += end - start;

    printf("rmsnorm_part1_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
