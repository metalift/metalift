
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

# define LEN 500

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

void scale_matrix_gemmini(elem_t m[LEN][LEN], elem_t scale, elem_t out[LEN][LEN]){
    GEMMINI_ACC_SCALE(m, scale);
    memcpy(m, out, sizeof(elem_t) * LEN * LEN);

}

int32_t* scale_matrix_gemmini_glued (int32_t m[LEN][LEN], int32_t scale){
    static int32_t out [LEN][LEN];
    scale_matrix_gemmini(m, scale, out);

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

    static int32_t w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        for (int j = 0; j < LEN; j++) {
            w[i][j] = random_int();
        }
    }
    int32_t scale = random_int();
    static int32_t out [LEN][LEN];
    start = read_cycles();
    scale_matrix_gemmini(w, scale, out);
    end = read_cycles();
    totalTime += end - start;



    printf("scale_matrix_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
