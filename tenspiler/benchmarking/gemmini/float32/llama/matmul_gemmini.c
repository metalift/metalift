
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

# define LEN 832

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

void matmul_gemmini(elem_t weight[LEN][LEN], elem_t input[LEN][LEN], elem_t out[LEN][LEN]){
    tiled_matmul_auto(LEN, LEN, 1, (elem_t*) weight, (elem_t*) input, NULL, out, 1, LEN, LEN, LEN, 1, 1, 1, 0, 1, 0, false, false, false, false, 0, 0, WS);

}

float* matmul_gemmini_glued (float weight[LEN][LEN], float input[LEN]){
    static elem_t glued_49[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_49[i][0] = input[i];
    }

    static float out [LEN][LEN];
    matmul_gemmini(weight, glued_49, out);
    static float out_postprocess [LEN];


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

    static float w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        for (int j = 0; j < LEN; j++) {
            w[i][j] = random_float();
        }
    }
    static float input[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        input[i][0] = random_float();
    }

    static float out [LEN][LEN];
    start = read_cycles();
    matmul_gemmini(w, input, out);
    end = read_cycles();

    totalTime += end - start;

    printf("matmul_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
