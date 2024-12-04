
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

# define LEN 338

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

void softmax_part3_gemmini(elem_t output[LEN][LEN], elem_t max_pos, elem_t* out){
    static elem_t temp0[LEN][LEN];
    for (int i = 0; i < max_pos; i++) {
     	 temp0[i][0] = output[i][0];
     }
    tiled_global_average(temp0[0], (elem_t*) out, 1, 1, 1, 1);
    *out = *out * LEN * LEN;

}

float softmax_part3_gemmini_glued (float output[LEN], float max_pos){
    static elem_t glued_46[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_46[i][0] = output[i];
    }

    elem_t out;
    softmax_part3_gemmini(glued_46, max_pos, &out);

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
    static float input[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        input[i][0] = random_float();
    }

    elem_t out;
    start = read_cycles();
    softmax_part3_gemmini(input, LEN, &out);
    end = read_cycles();

    totalTime += end - start;
    printf("softmax_part3_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
