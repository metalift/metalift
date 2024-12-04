
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

void scale_array_gemmini(elem_t a[LEN][LEN], elem_t n, elem_t s, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN];
    for (int i = 0; i < n; i++) {
     	 temp0[i][0] = a[i][0];
     }
    GEMMINI_ACC_SCALE(temp0, s);
    memcpy(temp0, out, sizeof(elem_t) * LEN * LEN);

}

int32_t* scale_array_gemmini_glued (int32_t a[LEN], int32_t n, int32_t s){
    static elem_t glued_35[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_35[i][0] = a[i];
    }

    static int32_t out [LEN][LEN];
    scale_array_gemmini(glued_35, n, s, out);
    static int32_t out_postprocess [LEN];


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

    static int32_t w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w[i][0] = random_int();
    }



    int32_t n = LEN;
    int32_t s = random_int();
    static int32_t out [LEN][LEN];
    start = read_cycles();
    scale_array_gemmini(w, n, s, out);
    end = read_cycles();

    totalTime += end - start;

    printf("scale_array_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
