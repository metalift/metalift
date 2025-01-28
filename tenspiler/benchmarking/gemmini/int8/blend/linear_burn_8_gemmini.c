
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

void linear_burn_8_gemmini(elem_t base[LEN][LEN], elem_t active[LEN][LEN], elem_t out[LEN][LEN]){
    static elem_t temp0[LEN][LEN];
    tiled_resadd_auto(LEN, LEN, 1, 1, 1, base[0], active[0], temp0[0], false, WS);
    for (int i = 0; i < LEN; i++) {
     	 for (int j = 0; j < LEN; j++) {
     	 	 out[i][j] = temp0[i][j] - 255;
     	 }
     }

}

uint8_t* linear_burn_8_gemmini_glued (uint8_t base[LEN][LEN], uint8_t active[LEN][LEN]){
    static uint8_t out [LEN][LEN];
    linear_burn_8_gemmini(base, active, out);

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

    static uint8_t w[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        for (int j = 0; j < LEN; j++) {
            w[i][j] = random_uint8();
        }
    }

    static uint8_t w2[LEN][LEN];
    for (int i = 0; i < LEN; i++) {
        for (int j = 0; j < LEN; j++) {
            w2[i][j] = random_uint8();
        }
    }
    static uint8_t out [LEN][LEN];
    start = read_cycles();
    linear_burn_8_gemmini(w, w2, out);
    end = read_cycles();
    totalTime += end - start;



    printf("linear_burn_8_gemmini");
    printf("%llu\n", totalTime);
    printf("%llu\n", totalTime);
    exit(0);
}
