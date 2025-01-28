
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

void lmsfir2_gemmini(elem_t NTAPS, elem_t input[LEN][LEN], elem_t coefficient[LEN][LEN], elem_t error, elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN];
    for (int i = 0; i < (NTAPS) - (1); i++) {
     	 temp0[i][0] = coefficient[i][0];
     }
    static elem_t temp1[LEN][LEN];
    static elem_t temp2[LEN][LEN];
    for (int i = 0; i < (NTAPS) - (1); i++) {
     	 temp2[i][0] = input[i][0];
     }
    GEMMINI_ACC_SCALE(temp2, error);
    memcpy(temp2, temp1, sizeof(elem_t) * LEN * LEN);
    tiled_resadd_auto((NTAPS) - (1), (NTAPS) - (1), 1, 1, 1, temp0[0], temp1[0], out[0], false, WS);

}

int32_t* lmsfir2_gemmini_glued (int32_t NTAPS, int32_t input[LEN], int32_t coefficient[LEN], int32_t error){
    static elem_t glued_40[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_40[i][0] = input[i];
    }

    static elem_t glued_41[LEN][LEN];

    for (int i = 0; i < LEN; i++) {
        glued_41[i][0] = coefficient[i];
    }

    static int32_t out [LEN][LEN];
    lmsfir2_gemmini(NTAPS, glued_40, glued_41, error, out);
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

    int32_t n = LEN;
    int32_t e = random_int();
    static int32_t w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w[i][0] = random_int();
    }
    static int32_t w2[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        w2[i][0] = random_int();
    }
    static int32_t out [LEN][LEN];
    start = read_cycles();
    lmsfir2_gemmini(n, w, w2, e, out);
    end = read_cycles();

    totalTime += end - start;



    printf("lmsfir2_gemmini_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
